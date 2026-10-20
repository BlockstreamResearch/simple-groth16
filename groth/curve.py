"""G1 and G2 arithmetic with prover-supplied slopes, and the fixed-base MSM of the public inputs.

Points are affine.  Every doubling or addition takes its slope lambda from the witness, and the program
checks the defining equation instead of inverting:

    doubling:  lambda 2y = 3x^2                 (y is never 0: neither curve has a point of order 2)
    addition:  lambda (xQ - xT) = yQ - yT,  and xQ != xT

With xQ != xT the equation has one solution, so a slope that passes is the true slope and the step is
the group law.  The prover has no freedom.  Values are kept below about 1.3 p by normalising slopes and
step outputs, so that every accumulator stays within the CRT bound.

`chain` sequences such steps: each step computes some values and binds them in a fresh, minimal
environment.

MSM: L = IC_0 + sum a_i IC_i with fixed bases.  For each w-bit digit d of a scalar, the point
[(d + 1) 2^{wj}] IC_i is selected from a constant table by a case tree on the digit bits and added with a
hinted slope.  The +1 keeps the point at infinity out of the tables; a constant offset folded into IC_0
compensates for it.
"""
from . import bn254
from .dsl import ensure
from .fp import Val, P, P_SECP, to_mont, mult_of_p_at_least, WORD_MAX
from .sym import E, flat, is_sym

R_ORDER = bn254.R
THREE_HALVES = 3 * pow(2, -1, P) % P
MSM_X_HI, MSM_Y_HI = 2 * P - 1, 3 * P - 1 # bounds of the MSM accumulator between windows


def fold_tree(be, state_shape, n, step, leaf_w=256):
    """Fold a state over the n leaves of a balanced tree.  The result is an E over (state, tree);
    step(k)(accs) is an E over (state, leaf k) with accs = (state accessors, leaf accessor).  Each node
    copies the state and its own subtree, never the whole tree."""
    state_w = sum(e.w for e in flat(state_shape))

    def go(lo, hi):
        if hi - lo == 1:
            be._push_env(state_w + leaf_w)
            try:
                res = step(lo)((be._unpack('O', state_shape), be.proj('IH', leaf_w)))
            finally:
                be._pop_env()
            return res
        mid = lo + (hi - lo + 1) // 2
        lw, rw = leaf_w * (mid - lo), leaf_w * (hi - mid)
        # env = (state, (left, right)): fold the left subtree, then the right one
        inner = be.comp(be.pair(be.proj('OH', state_w), be.proj('IOH', lw)), go(lo, mid))
        return be.comp(be.pair(inner, be.proj('IIH', rw)), go(mid, hi))
    return go(0, n)


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

    # fixed-base MSM of the public inputs
    def select_point(self, word, lo, w, table):
        """Table entry (x, y) indexed by bits lo .. lo+w-1 of the projected scalar `word`, as a 512-bit
        value: a case tree on the bits, most significant first, with constant pairs as leaves."""
        be = self.be
        if not is_sym(be):
            d = (word.e >> lo) & ((1 << w) - 1)
            x, y = table[d]
            return Val([to_mont(x), to_mont(y)], 0)
        bits = [be.bit(word.e, lo + i) for i in range(w - 1, -1, -1)]
        env = be.unit()
        for b in reversed(bits):
            env = be.pair(b, env)

        # case s t : (A + B) x C -> D.  A bit is 1 + 1, so each branch sees (1, rest) and the next level
        # reads rest with `drop`.
        def tree(depth, prefix):
            if depth == w:
                x, y = table[prefix]
                return be.consts(256, [[to_mont(x), to_mont(y)]])
            l, r = tree(depth + 1, prefix << 1), tree(depth + 1, (prefix << 1) | 1)
            if depth + 1 < w:
                l, r = be.drop(l), be.drop(r)
            # named every few levels, so that no line of the program text is long (the parser is slow on those)
            return be.share(be.case(l, r)) if (w - depth) % 4 == 0 else be.case(l, r)
        return Val(be.comp(env, tree(0, 0)), 0)

    def msm_window_steps(self, j, w, table):
        """One window: select the table point by the digit of scalar 's' and add it with hint 'lam'.
        ctx: 'x', 'y', 's', 'lam'; results 'x', 'y'.  Each coordinate is a single dot, with the plain terms
        written as products with the Montgomery constants [-1] and [1], so no normalisation is needed
        (x stays below 1.7 p, y below 2.4 p)."""
        fp = self.fp
        # a shared node belongs to one environment, so constants are created where they are used
        def m1(): return fp.const(P - 1) # [-1]_M
        def one(): return fp.const(1) # [1]_M = R mod p, a small word (0.29 p)

        def qx(c): return Val(self.be.sub(c['_sel'].e, 'O', 256), P - 1)
        def qy(c): return Val(self.be.sub(c['_sel'].e, 'I', 256), P - 1)
        return [
            ('let', ['_sel', 'lam'], lambda c: [self.select_point(c['s'], j * w, w, table), fp.normalize(c['lam'])]),
            ('check', lambda c: self.neq_check(qx(c), c['x'])),
            # lam (qx - x) - (qy - y) = 0 as one reduced dot, then x2 = lam^2 - x - qx
            ('check', lambda c: self.zero_check(fp.reduce_dot([(c['lam'], fp.sub(qx(c), c['x'])), (qy(c), m1()), (c['y'], one())]))),
            ('let', ['x2'], lambda c: [fp.reduce_dot([(c['lam'], c['lam']), (c['x'], m1()), (qx(c), m1())])]),
            ('drop', ['_sel']),
            ('let', ['y2'], lambda c: [fp.reduce_dot([(c['lam'], c['x']), (c['lam'], fp.neg(c['x2'])), (c['y'], m1())])]),
            ('let', ['x', 'y'], lambda c: [c['x2'], c['y2']]),
            ('drop', ['x2', 'y2', 'lam']),
        ]

    def msm(self, scalars, hints, tables, start, w, nbits=254):
        """Numeric MSM: start + sum_ij [(d_ij + 1) 2^{wj}] base_i over the digits d_ij of the scalars,
        with hints[i][j] the slopes.  Returns (x, y) and the checks.  msm_sym is the symbolic version."""
        fp = self.fp
        nwin = (nbits + w - 1) // w
        x, y = fp.const(start[0]), fp.const(start[1])
        all_checks = []
        for i, sc in enumerate(scalars):
            for j in range(nwin):
                ctx = {'x': Val(x.e, MSM_X_HI), 'y': Val(y.e, MSM_Y_HI), 's': sc, 'lam': Val(hints[i][j].e, WORD_MAX)}

                def final(c, checks):
                    all_checks.extend(checks)
                    ensure(c['x'].hi <= MSM_X_HI and c['y'].hi <= MSM_Y_HI, 'MSM state bound')
                    return (c['x'], c['y'])
                x, y = chain(fp, ctx, self.msm_window_steps(j, w, tables[i][j]), final)
        return (x, y), all_checks

    def msm_sym(self, scalars, hints_root, tables, start, w, nbits=254):
        """Symbolic MSM.  The hints (scalar-major) are the leaves of the balanced tree at hints_root; the
        state (x, y, scalars) is folded over that tree, so each step sees only its own hint.  Returns the
        E of the final state, all checks executed."""
        be, fp = self.be, self.fp
        nwin = (nbits + w - 1) // w
        n = len(scalars)
        state = be.pack([fp.const(start[0]).e, fp.const(start[1]).e, [sc.e for sc in scalars]])
        shape = [E('', 256, 0), E('', 256, 0), [E('', 256, 0)] * n]

        def step(k):
            i, j = divmod(k, nwin)

            def body(accs):
                st, hint = accs
                # the state bounds are a fixed point of the window step (checked in final)
                ctx = {'x': Val(st[0], MSM_X_HI), 'y': Val(st[1], MSM_Y_HI), 'S': [Val(e, R_ORDER - 1) for e in st[2]],
                       's': Val(st[2][i], R_ORDER - 1), 'lam': Val(hint, WORD_MAX)}

                def final(c, checks):
                    ensure(c['x'].hi <= MSM_X_HI and c['y'].hi <= MSM_Y_HI, 'MSM state bound')
                    new_state = be.pack([c['x'].e, c['y'].e, [v.e for v in c['S']]])
                    chk = be.checks([v.e for v in checks]) if checks else be.unit()
                    return be.comp(be.pair(chk, new_state), be.proj('IH', 512 + 256 * n))
                return chain(fp, ctx, self.msm_window_steps(j, w, tables[i][j]), final)
            return body
        return be.comp(be.pair(state, hints_root), fold_tree(be, shape, n * nwin, step))

    @staticmethod
    def msm_tables(bases, w, nbits=254):
        """tables[i][j][d] = [(d + 1) 2^{wj}] base_i, and the offset -sum_ij [2^{wj}] base_i that cancels
        the +1."""
        nwin = (nbits + w - 1) // w
        tables, offset = [], None
        for base in bases:
            tab = []
            for j in range(nwin):
                step = bn254.g1_mul(base, 1 << (w * j))
                offset = bn254.g1_add(offset, bn254.g1_neg(step))
                entries, acc = [], None
                for d in range(1 << w):
                    acc = bn254.g1_add(acc, step)
                    entries.append(acc)
                tab.append(entries)
            tables.append(tab)
        return tables, offset

    @staticmethod
    def msm_hints(start, scalars, tables, w, nbits=254):
        """Prover side: the slopes of the MSM additions and the result, (hints[i][j], L)."""
        nwin = (nbits + w - 1) // w
        acc = start
        hints = []
        for i, sc in enumerate(scalars):
            hi = []
            for j in range(nwin):
                d = (sc >> (w * j)) & ((1 << w) - 1)
                q = tables[i][j][d]
                hi.append(Curve.g1_add_hint(acc, q))
                acc = bn254.g1_add(acc, q)
            hints.append(hi)
        return hints, acc

    @staticmethod
    def g1_add_hint(Pt, Q):
        """Prover side: the slope of the addition Pt + Q."""
        x1, y1 = Pt
        x2, y2 = Q
        assert x1 != x2
        return (y2 - y1) * pow(x2 - x1, -1, P) % P
