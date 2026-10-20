"""G1 and G2 checks with prover-supplied slopes, and constant tables selected by bits of a word.

Points are affine.  Every doubling or addition takes its slope lambda from the witness, and the program
checks the defining equation instead of inverting:

    doubling:  lambda 2y = 3x^2                 (y is never 0: neither curve has a point of order 2)
    addition:  lambda (xQ - xT) = yQ - yT,  and xQ != xT

With xQ != xT the equation has one solution, so a slope that passes is the true slope and the step is
the group law.  The prover has no freedom.  Values are kept below about 1.3 p by normalising slopes and
step outputs, so that every accumulator stays within the CRT bound.

`chain` sequences such steps: each step computes some values and binds them in a fresh, minimal
environment.

Tables: `select_const` picks the entry of a constant table by a digit of a word (a few of its bits) with
a case tree on the bits.  When the program is pruned for a spend, only the selected entry and the
commitments of the branches not taken remain.
"""
from . import bn254
from .dsl import ensure
from .fp import Val, P, P_SECP, mult_of_p_at_least
from .sym import E, is_sym


def chain(fp, ctx, steps, final):
    """Run `steps` on a context, a dict of Vals (or tuples and lists of them) and constants.  Each `let`
    re-packs the live values into a fresh environment (fp.scope), so reads stay shallow and dead values
    are not copied along.  Steps:

        ('let', names, fn)     bind fn(ctx) under names
        ('let', names, fn, gone) the same, forgetting the values `gone` (read by fn) in the new environment
        ('push', names, fn)    bind fn(ctx) under names in front of the environment (fp.let): the live
                               values stay where they are, one level deeper, instead of being copied
        ('check', fn)          fn(ctx) -> a unit-typed Val or a list of them, collected
        ('drop', names)        forget values

    final(ctx, checks) -> E, with the collected checks."""
    def is_val(v):
        return isinstance(v, (Val, list, tuple))

    def strip(v):
        """Remove the None leaves, remembering where they were, so the structure can be packed."""
        if isinstance(v, Val):
            return v, None
        if v is None:
            return None, 'none'
        items, infos = [], []
        for x in v:
            sx, ix = strip(x)
            infos.append(ix)
            if sx is not None:
                items.append(sx)
        return items, (type(v), infos)

    def restore(v, info):
        if info is None:
            return v
        if info == 'none':
            return None
        typ, infos = info
        it = iter(v)
        out = [None if ix == 'none' else restore(next(it), ix) for ix in infos]
        return typ(out) if typ is tuple else out

    def repack(ctx, extra, body):
        """Scope over the Vals of ctx plus `extra`; body(ctx2)."""
        merged = {k: v for k, v in ctx.items() if is_val(v)}
        merged.update(extra)
        names = list(merged)
        stripped = [strip(merged[k]) for k in names]
        vals = [sv for sv, info in stripped]
        consts = {k: v for k, v in ctx.items() if not is_val(v)}

        def inner(new):
            ctx2 = dict(consts)
            ctx2.update({k: restore(nv, info) for k, nv, (sv, info) in zip(names, new, stripped)})
            return body(ctx2)
        return fp.scope(vals, inner)

    def go(ctx, steps):
        if not steps:
            checks = [v for k, v in ctx.items() if k.startswith('_chk')]
            return final({k: v for k, v in ctx.items() if not k.startswith('_chk')}, checks)
        step, rest = steps[0], steps[1:]
        kind = step[0]
        if kind == 'let':
            _, names, fn, *gone = step
            vals = fn(ctx)
            kept = {k: v for k, v in ctx.items() if k not in (gone[0] if gone else ())}
            return repack(kept, dict(zip(names, vals)), lambda ctx2: go(ctx2, rest))
        if kind == 'push':
            _, names, fn = step
            stripped = [strip(v) for v in fn(ctx)]

            def lifted(v, lift):
                if isinstance(v, Val):
                    return lift(v)
                if v is None or not is_val(v):
                    return v
                return type(v)(lifted(x, lift) for x in v) if isinstance(v, tuple) else [lifted(x, lift) for x in v]

            def body(new, lift):
                ctx2 = {k: lifted(v, lift) for k, v in ctx.items()}
                ctx2.update({k: restore(nv, info) for k, nv, (sv, info) in zip(names, new, stripped)})
                return go(ctx2, rest)
            return fp.let([sv for sv, info in stripped], body)
        if kind == 'check':
            _, fn = step
            res = fn(ctx)
            res = res if isinstance(res, list) else [res]
            ctx2 = dict(ctx)
            for v in res:
                ctx2[f'_chk{len([k for k in ctx2 if k.startswith("_chk")])}'] = v
            return go(ctx2, rest)
        if kind == 'drop':
            _, names = step
            return go({k: v for k, v in ctx.items() if k not in names}, rest)
        raise ValueError(kind)
    return go(ctx, steps)


class Curve:
    def __init__(self, fp):
        self.fp = fp
        self.be = fp.be

    # F_p2 helpers on (x, y) tuples of Vals.  The sign variants a product needs (-b1, 2 a0) are used once,
    # so they stay inline; each operand component appears in two terms, which is fine for projections.
    def add2(self, a, b):
        return (self.fp.add(a[0], b[0]), self.fp.add(a[1], b[1]))

    def sub2(self, a, b):
        return (self.fp.sub(a[0], b[0]), self.fp.sub(a[1], b[1]))

    def neg2(self, a):
        return (self.fp.neg(a[0]), self.fp.neg(a[1]))

    def norm2(self, a):
        return (self.fp.normalize(a[0]), self.fp.normalize(a[1]))

    def mul2(self, a, b):
        """(a0 + a1 u)(b0 + b1 u) = (a0 b0 - a1 b1) + (a0 b1 + a1 b0) u"""
        fp = self.fp
        return (fp.reduce_dot([(a[0], b[0]), (a[1], fp.neg(b[1]))]),
                fp.reduce_dot([(a[0], b[1]), (a[1], b[0])]))

    def sqr2(self, a):
        """(a0 + a1 u)^2 = (a0^2 - a1^2) + 2 a0 a1 u"""
        fp = self.fp
        return (fp.reduce_dot([(a[0], a[0]), (a[1], fp.neg(a[1]))]),
                fp.reduce_dot([(fp.double(a[0]), a[1])]))

    def mul2_const(self, a, k):
        """(a0, a1) times the F_p constant k"""
        return (self.fp.mul_const(a[0], k), self.fp.mul_const(a[1], k))

    # Equality of non-canonical words: a - b, computed as a + (kp - b), must be a multiple of p below its
    # bound.  Operands are normalised first when that sum would not fit below p_s.
    def is_zero_flag(self, d, verified=False):
        """d = 0 (mod p): d is compared with every multiple of p up to its bound.  A 1-bit flag, or with
        `verified` the unit-typed check."""
        be = self.be

        def body(v):
            cands = [be.eq256(v[0].e, be.word(i * P)) for i in range(d.hi // P + 1)]
            acc = cands[0]
            for c in cands[1:]:
                acc = be.or1(acc, c)
            return be.verify(acc) if verified else acc
        return self.fp.scope([d], body)

    def zero_check(self, d):
        return Val(self.is_zero_flag(d, verified=True), 0)

    def is_eq_flag(self, a, b):
        fp = self.fp
        if a.hi + mult_of_p_at_least(b.hi) >= P_SECP:
            a = fp.normalize(a)
        if a.hi + mult_of_p_at_least(b.hi) >= P_SECP:
            b = fp.normalize(b)
        return self.is_zero_flag(fp.sub(a, b))

    def eq_check(self, a, b):
        return Val(self.be.verify(self.is_eq_flag(a, b)), 0)

    def neq_check(self, a, b):
        return Val(self.be.verify(self.be.not1(self.is_eq_flag(a, b))), 0)

    def eq2_check(self, a, b):
        return [self.eq_check(a[0], b[0]), self.eq_check(a[1], b[1])]

    def neq2_check(self, a, b):
        """a != b in F_p2: at least one coordinate differs."""
        be = self.be
        return Val(be.verify(be.not1(be.and1(self.is_eq_flag(a[0], b[0]), self.is_eq_flag(a[1], b[1])))), 0)

    # on-curve checks
    def g1_on_curve_check(self, x, y):
        """y^2 = x^3 + 3 for normalised x, y."""
        fp = self.fp
        return chain(fp, {'x': x, 'y': y}, [
            ('let', ['xx'], lambda c: [fp.normalize(fp.reduce_dot([(c['x'], c['x'])]))]),
            ('check', lambda c: self.eq_check(fp.reduce_dot([(c['y'], c['y'])]), fp.add(fp.reduce_dot([(c['xx'], c['x'])]), fp.const(3)))),
        ], lambda c, checks: self.be.checks([ch.e for ch in checks]))

    def g2_on_curve_check(self, x, y):
        """y^2 = x^3 + b', b' = 3 / (9 + u), for normalised x, y in F_p2."""
        fp = self.fp
        return chain(fp, {'x': x, 'y': y}, [
            ('let', ['xx'], lambda c: [self.norm2(self.sqr2(c['x']))]),
            ('check', lambda c: self.eq2_check(self.sqr2(c['y']), self.add2(self.mul2(c['xx'], c['x']),
                                                                               (fp.const(bn254.TWIST_B.c0), fp.const(bn254.TWIST_B.c1))))),
        ], lambda c, checks: self.be.checks([ch.e for ch in checks]))

    def lt_const_check(self, word, bound):
        """Verify word < bound (a constant) limb by limb, from the most significant 64 bits.  Reading the
        whole word also consumes witness bits that nothing else reads."""
        be = self.be
        if not is_sym(be):
            ensure(word.e < bound, 'range check')
            return Val(0, 0)
        limbs = [be.sub(word.e, pth, 64) for pth in ('OO', 'OI', 'IO', 'II')] # most significant first
        consts = [(bound >> (64 * (3 - i))) & 0xFFFFFFFFFFFFFFFF for i in range(4)]
        # lt = l0 < c0 or (l0 == c0 and (l1 < c1 or (l1 == c1 and ...)))
        flag = be.lt64(limbs[3], be.const(64, consts[3]))
        for i in (2, 1, 0):
            flag = be.or1(be.lt64(limbs[i], be.const(64, consts[i])), be.and1(be.eq64(limbs[i], be.const(64, consts[i])), flag))
        return Val(be.verify(flag), 0)

    # constant tables, selected by bits of a word
    def select_const(self, word, lo, w, leaves):
        """leaves[d] for the digit d in bits lo .. lo+w-1 of the projected word `word` (a Val): each leaf a
        list of groups of constant words.  A case tree on the bits, most significant first, with the leaves
        as wide constants.  Sym: an E of the leaf's words; Num: leaves[d]."""
        be = self.be
        if not is_sym(be):
            return leaves[(word.e >> lo) & ((1 << w) - 1)]
        aligned = w & (w - 1) == 0 and lo % w == 0 and 256 % w == 0
        if aligned:
            # the w bits are one aligned chunk of the word: project it once, and turn it into the digit as a
            # nested sum with a shared function, so that a window adds few nodes of its own
            path = ''.join('O' if (255 - lo) >> (7 - k) & 1 == 0 else 'I' for k in range(8))[:8 - (w.bit_length() - 1)]
            env = be.call(self.digit_fn(w), [be.sub(word.e, path, w)])
        else:
            bits = [be.bit(word.e, lo + i) for i in range(w - 1, -1, -1)]
            env = be.unit()
            for b in reversed(bits):
                env = be.pair(b, env)

        # case s t : (A + B) x C -> D.  On the digit as a nested sum, (T_w, 1) with T_k = T_(k-1) + T_(k-1),
        # each branch sees (T_(k-1), 1), the next level's input.  On bits, (b, rest) with b = 1 + 1, each
        # branch sees (1, rest) and the next level reads rest with `drop`.
        def tree(depth, prefix):
            if depth == w:
                return be.consts(256, leaves[prefix])
            l, r = tree(depth + 1, prefix << 1), tree(depth + 1, (prefix << 1) | 1)
            if depth + 1 < w and not aligned:
                l, r = be.drop(l), be.drop(r)
            # named every few levels, so that no line of the program text is long (the parser is slow on those)
            return be.share(be.case(l, r)) if (w - depth) % 4 == 0 else be.case(l, r)
        return be.comp(env, tree(0, 0))

    def digit_fn(self, w):
        """DIGIT<w>: a w-bit word -> (T_w, 1), its value as a nested sum, T_0 = 1 and T_k = T_(k-1) + T_(k-1)
        with the most significant bit outermost: a case tree on it needs no `drop`.  BITS<w>, then one case
        per bit.  Defined once per program."""
        be = self.be
        fns = be.__dict__.setdefault('_digit_fns', {})
        if w not in fns:
            f = be.unit() # T_0 from the 1 that ends the bits
            for k in range(1, w + 1): # (b, rest) -> T_k: the bit picks the side, the rest gives T_(k-1)
                f = be.case(be.injl(be.drop(f), k), be.injr(be.drop(f), k))
            bits = self.bits_fn(w)
            fns[w] = be.function(f'DIGIT{w}', [E('', w, 0)], lambda acc: be.pair(be.comp(be.call(bits, [acc[0] if isinstance(acc, list) else acc]), f), be.unit()))
        return fns[w]

    def bits_fn(self, w):
        """BITS<w>: a w-bit word -> its bits, most significant first, as (b, (b, ... (b, 1))), the input of a
        case tree.  Defined once per program."""
        be = self.be
        fns = be.__dict__.setdefault('_bits_fns', {})
        if w not in fns:
            n = w.bit_length() - 1

            def body(acc):
                acc = acc[0] if isinstance(acc, list) else acc
                env = be.unit()
                for i in range(w): # least significant first, so that the most significant ends up outside
                    pos = w - 1 - i
                    env = be.pair(be.sub(acc, ''.join('I' if pos >> (n - 1 - k) & 1 else 'O' for k in range(n)), 1), env)
                return env
            fns[w] = be.function(f'BITS{w}', [E('', w, 0)], body)
        return fns[w]
