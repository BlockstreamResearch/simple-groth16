"""The tower F_p2 < F_p6 < F_p12 on top of fp.py.

An element is a list of 12 F_p coefficients (fp.Val, or None for a coefficient known to be zero) in the
basis u^a v^b w^c, stored at index a + 2b + 6c, with

    u^2 = -1,   v^3 = xi = 9 + u,   w^2 = v          (the same tower as bn254.py)

A product of two elements is a sum of F_p products a_i b_j.  Each lands in one output coefficient,
with a sign (from u^2 = -1) and possibly a factor xi (from v^3 = xi).  The terms of a coefficient are
summed in CRT form and reduced once, so a product costs one reduction per output coefficient.

Signs and factors xi are moved into the right operand.  For each coefficient that needs them, the
generator prepares variants: 'neg' (c - x for a multiple c of p), 'xi' (xi times the F_p2 coefficient,
reduced: an "xi-copy"), 'xineg' (both), and for the left operand of a squaring '2' (doubled).  Then every
term is a plain product.  xi cannot be applied lazily: 9x would overflow the CRT bound.

Bounds: n terms with operands below beta p and beta' p give an accumulator of n beta beta' p^2, which
must stay below 22.7 p^2, and a reduced result below (n beta beta' / 5.29 + 1) p.  Operands are
normalised (fp.normalize, 8.9 k mWU per word) when an accumulator would overflow.
"""
from collections import defaultdict
from . import bn254


def idx(a, b, c):
    """Flat index of the basis element u^a v^b w^c."""
    return a + 2 * b + 6 * c


def coords(i):
    return i % 2, (i // 2) % 3, i // 6


def basis_mul(i, j):
    """Product of basis elements i and j as (k, sign, xi): sign * xi^xi * basis_k."""
    a, b, c = coords(i)
    a2, b2, c2 = coords(j)
    A, B, C = a + a2, b + b2, c + c2
    if C == 2:
        C = 0
        B += 1
    xi = 0
    if B >= 3:
        B -= 3
        xi = 1
    sign = 1 if A < 2 else -1
    A %= 2
    return idx(A, B, C), sign, xi


def fp2_index_of(j):
    """The F_p2 coefficient (b, c) that holds basis index j."""
    _, b, c = coords(j)
    return b, c


class Tower:
    """Products of tower elements.  An operand is a dict of variant lists ('1' is the element itself; see
    the module docstring for the others), so every term is a plain product and every output coefficient
    one fp.reduce_dot.  `needed` lists the variants a product uses, `variants` builds them."""

    def __init__(self, fp):
        self.fp = fp
        self.be = fp.be

    # term generation
    @staticmethod
    def _terms_general(nA, nB):
        """(i, j, k, sign, xi, mult) for every coefficient pair of a general product."""
        out = []
        for i in range(nA):
            for j in range(nB):
                k, sign, xi = basis_mul(i, j)
                out.append((i, j, k, sign, xi, 1))
        return out

    @staticmethod
    def _terms_square():
        """Terms of a squaring, with a_i a_j + a_j a_i merged into (2 a_i) a_j (for the xi terms at the
        F_p2 level: xi A_J A_J' + xi A_J' A_J = (2 A_J) (xi A_J'))."""
        out = []
        fp2 = [(b, c) for c in range(2) for b in range(3)]
        for J in fp2:
            for Jp in fp2:
                if Jp < J:
                    continue
                for a in range(2):
                    for ap in range(2):
                        i, j = idx(a, *J), idx(ap, *Jp)
                        k, sign, xi = basis_mul(i, j)
                        if J < Jp:
                            out.append((i, j, k, sign, xi, 2))
                        elif xi:
                            out.append((i, j, k, sign, xi, 1)) # all four a_a (xi a)_a' terms
                        else:
                            if a == ap:
                                out.append((i, j, k, sign, 0, 1)) # x x, y y
                            elif a < ap:
                                out.append((i, j, k, sign, 0, 2)) # x y twice
        return out

    def _pairs(self, A, B, terms):
        """Operand pairs per output coefficient; terms with a None coefficient are dropped."""
        per = defaultdict(list)
        for i, j, k, sign, xi, mult in terms:
            akey = '2' if mult == 2 else '1'
            bkey = ('xi' if xi else '') + ('neg' if sign < 0 else '')
            bkey = bkey or '1'
            if A['1'][i] is None or B['1'][j] is None:
                continue
            a = A[akey][i]
            b = B[bkey][j]
            assert a is not None, f'left variant {akey}[{i}] missing'
            assert b is not None, f'right variant {bkey}[{j}] missing'
            per[k].append((a, b))
        return per

    def needed(self, A1, B1, symmetric=False):
        """Variants used by A * B: {'A' | 'B': {variant: set of indices}}."""
        terms = self._terms_square() if symmetric else self._terms_general(len(A1), len(B1))
        need = {'A': defaultdict(set), 'B': defaultdict(set)}
        for i, j, k, sign, xi, mult in terms:
            if A1[i] is None or B1[j] is None:
                continue
            need['A']['2' if mult == 2 else '1'].add(i)
            bkey = ('xi' if xi else '') + ('neg' if sign < 0 else '')
            need['B'][bkey or '1'].add(j)
        return need

    def mul(self, A, B, symmetric=False):
        """The reduced product: 12 Val or None."""
        terms = self._terms_square() if symmetric else self._terms_general(len(A['1']), len(B['1']))
        per = self._pairs(A, B, terms)
        return [self.fp.reduce_dot(per[k]) if per.get(k) else None for k in range(12)]

    # variants
    def xi_copy(self, x, y):
        """xi (x + y u) = (9x - y) + (x + 9y) u, reduced: two fp.lin_const, about 30 k mWU."""
        fp = self.fp
        return fp.lin_const([(x, 9), (y, -1)]), fp.lin_const([(x, 1), (y, 9)])

    def mul_fp2_const(self, x, y, g0, g1):
        """(x + y u)(g0 + g1 u) for a constant g0 + g1 u: two lin_const."""
        fp = self.fp
        return fp.lin_const([(x, g0), (y, -g1)]), fp.lin_const([(x, g1), (y, g0)])

    def variants(self, elem, need, tight_neg=False):
        """The variant lists of `elem` for a `need` dict {variant: indices}.  Negation is fp.neg, or
        mul_const(x, -1) with tight_neg (a tighter bound).  The values are expressions: the caller must
        let-bind them before use."""
        fp = self.fp
        out = {'1': elem}
        xi_full = [None] * 12
        if need.get('xi') or need.get('xineg'):
            js = set(need.get('xi', ())) | set(need.get('xineg', ()))
            for j in js:
                j0 = idx(0, *fp2_index_of(j))
                if xi_full[j0] is None:
                    x = elem[j0] if elem[j0] is not None else fp.const(0)
                    y = elem[j0 + 1] if elem[j0 + 1] is not None else fp.const(0)
                    xi_full[j0], xi_full[j0 + 1] = self.xi_copy(x, y)
        if need.get('xi'):
            out['xi'] = [xi_full[j] if j in need['xi'] else None for j in range(12)]
        negf = (lambda v: fp.mul_const(v, -1)) if tight_neg else fp.neg
        if need.get('neg'):
            out['neg'] = [negf(elem[j]) if (j in need['neg'] and elem[j] is not None) else None for j in range(12)]
        if need.get('xineg'):
            out['xineg'] = [negf(xi_full[j]) if j in need['xineg'] else None for j in range(12)]
        if need.get('2'):
            out['2'] = [fp.double(elem[j]) if (j in need['2'] and elem[j] is not None) else None for j in range(12)]
        return out

    # products with the variants prepared and bound
    def mul_bound(self, A, B, body, symmetric=False, tight_neg=False):
        """Bind the variants A * B needs and run body(C, lift) with the product C in the new environment;
        lift re-expresses outer values.  For a squaring pass B = A and symmetric=True."""
        need = self.needed(A, B, symmetric)
        needA = {k: v for k, v in need['A'].items() if k != '1'}
        needB = {k: v for k, v in need['B'].items() if k != '1'}
        if symmetric:
            varsA = varsB = self.variants(A, {**needA, **needB}, tight_neg)
        else:
            varsA, varsB = self.variants(A, needA, tight_neg), self.variants(B, needB, tight_neg)
        keys = [('A', k) for k in varsA if k != '1'] + ([] if symmetric else [('B', k) for k in varsB if k != '1'])
        if not keys:
            return body(self.mul(varsA, varsB, symmetric), lambda v: v)

        def inner(bound, lift):
            A2 = {'1': [lift(a) if a is not None else None for a in A]}
            B2 = A2 if symmetric else {'1': [lift(b) if b is not None else None for b in B]}
            for (side, k), lst in zip(keys, bound):
                (A2 if side == 'A' else B2)[k] = lst
            return body(self.mul(A2, B2, symmetric), lift)
        return let_masked(self.fp, [(varsA if side == 'A' else varsB)[k] for side, k in keys], inner)

    # Frobenius
    def frobenius(self, A, n=1, tight_neg=False):
        """A^(p^n) for n in {1, 2, 3}: conjugate every F_p2 coefficient (odd n) and multiply coefficient
        (b, c) by bn254.FROBn[2b + c].  Two lin_const per coefficient for odd n, two mul_const for n = 2.
        tight_neg as in `variants`."""
        fp = self.fp
        g = {1: bn254.FROB1, 2: bn254.FROB2, 3: bn254.FROB3}[n]
        out = [None] * 12
        for c in range(2):
            for b in range(3):
                j = idx(0, b, c)
                x, y = A[j], A[j + 1]
                if x is None and y is None:
                    continue
                x = x if x is not None else fp.const(0)
                y = y if y is not None else fp.const(0)
                gi = g[2 * b + c]
                g0, g1 = gi.c0, gi.c1
                if n % 2 == 0:
                    assert g1 == 0
                    if g0 == 1:
                        out[j], out[j + 1] = x, y
                    else:
                        out[j], out[j + 1] = fp.mul_const(x, g0), fp.mul_const(y, g0)
                elif (b, c) == (0, 0):
                    out[j] = x
                    out[j + 1] = fp.mul_const(y, -1) if tight_neg else fp.neg(y)
                else:
                    # (x - y u)(g0 + g1 u) = (x g0 + y g1) + (x g1 - y g0) u
                    out[j] = fp.lin_const([(x, g0), (y, g1)])
                    out[j + 1] = fp.lin_const([(x, g1), (y, -g0)])
        return out


def let_masked(fp, lists, body):
    """fp.let over lists of Val or None: the Nones are dropped for the binding and restored for the body."""
    masks = [[v is not None for v in l] for l in lists]
    compact = [[v for v in l if v is not None] for l in lists]

    def inner(accs, lift):
        full = []
        for acc, mask in zip(accs, masks):
            it = iter(acc)
            full.append([next(it) if m else None for m in mask])
        return body(full, lift)
    return fp.let(compact, inner)


def embed_fp2(x, y):
    """An F_p2 element as a 12-coefficient list."""
    out = [None] * 12
    out[0], out[1] = x, y
    return out


def embed_fp6(coeffs):
    """An F_p6 element (x0, y0, x1, y1, x2, y2) as a 12-coefficient list."""
    out = [None] * 12
    out[:6] = coeffs
    return out


def ref_to_list(f):
    """bn254.Fp12 -> 12 field values in basis order."""
    out = []
    for c6 in (f.c0, f.c1):
        for c2 in (c6.c0, c6.c1, c6.c2):
            out += [c2.c0, c2.c1]
    return out

