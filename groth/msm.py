"""G1 multi-scalar multiplication, checked with hints, for the fflonk verifier.

The group law.  Points are affine, coordinates in F_p in Montgomery form.  The prover gives each
operation's slope lambda, and for an addition also d, the inverse of x_Q - x_T; the program checks

    addition T + Q:   lambda (x_Q - x_T) = y_Q - y_T   and   d (x_Q - x_T) = 1
    doubling 2T:      lambda y_T = 3/2 x_T^2

each relation directly (its value is compared with the multiples of p below its bound), and computes
x' = lambda^2 - x_T - x_Q, y' = lambda (x_T - x') - y_T.  The inverse makes x_Q != x_T, so the slope is
the chord's and the result is T + Q; a doubling needs no inverse, since y_T = 0 would make 3 x_T^2 = 0,
and (0, 0) is not on the curve.  So every point the program computes from points on the curve is on the
curve, and is the group-law result.  An addition where x_Q = x_T has no witness: an honest prover meets
one with negligible probability.  The hints are words below 2^254 (two bits checked), so that lambda^2
fits the CRT bound.  ADD and DBL are functions of the program, shared by every operation.

The variable-base part (VarMsm): sum_i k_i P_i for points from the proof and scalars in F_r.  Each scalar
is split by the GLV endomorphism phi(x, y) = (beta x, y) = [lambda] P into k = n1 + lambda n2 (mod r)
with n1, n2 odd and |n| < 2^128, so each point gives two columns, P and phi(P), of 128-bit scalars.  An
odd n < 2^128 in absolute value is sum_j d_j 2^j with every digit d_j = 2 c_j - 1 in {-1, 1}, c the bits
of C = (n + 2^128 - 1) / 2: the prover gives C, one word per column.  Columns are grouped by four; a
group's runtime table holds the 8 sums Q1 +- Q2 +- Q3 +- Q4, and the digits of step j select
d_1 (Q1 + d_1 d_2 Q2 + d_1 d_3 Q3 + d_1 d_4 Q4): the entry by the bits c_1 xor c_k, the sign by c_1.  So
the loop is 128 steps, each a doubling and one addition per group, with no digit 0 to skip.

The fixed-base part (FixedMsm): v G for a canonical word v (< r): windows of 8 bits (the top one 6),
each selecting a constant (d + 1) 2^(8 j) G from a table by its digit (curve.select_const), starting from
-sum_j 2^(8 j) G, so that no entry is the point at infinity.  Given `extra`, the start is that much lower:
the verifier passes the variable-base part's offset (var_offset, below), which the sum then loses.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from . import bn254 as B
from .curve import Curve, chain
from .dsl import Tbalanced, balanced_paths, ensure
from .fp import WORD_MAX, Fp, Val, to_mont
from .pairing import F_HI, KB
from .sym import E, is_sym, words

P, R = B.P, B.R
G1Point = tuple[int, int]

# ---------------------------------------------------------------------------------------------------
# GLV for BN254's G1: phi(x, y) = (BETA x, y) = [LAMBDA] (x, y); a short basis of the lattice of (a, b)
# with a + LAMBDA b = 0 (mod r).
GLV_BETA = 2203960485148121921418603742825762020974279258880205651966
GLV_LAMBDA = 4407920970296243842393367215006156084916469457145843978461
GLV_V1 = (0x89D3256894D213E3, -0x6F4D8248EEB859FC8211BBEB7D4F1128)
GLV_V2 = (0x6F4D8248EEB859FD0BE4E1541221250B, 0x89D3256894D213E3)
HALF_BITS = 128  # digits per column
assert (GLV_BETA**3 - 1) % P == 0 and (GLV_LAMBDA**2 + GLV_LAMBDA + 1) % R == 0
assert all((v[0] + GLV_LAMBDA * v[1]) % R == 0 for v in (GLV_V1, GLV_V2))
assert GLV_V1[0] * GLV_V2[1] - GLV_V1[1] * GLV_V2[0] == R


def _offset_point() -> G1Point:
    """A point of G1 by try-and-increment from a label: the MSM's accumulator starts here."""
    import hashlib

    x = int.from_bytes(hashlib.sha256(b'simple-groth16 fflonk MSM start').digest(), 'big') % P
    while True:
        y2 = (x**3 + 3) % P
        y = pow(y2, (P + 1) // 4, P)
        if y * y % P == y2:
            return (x, y)
        x += 1


# The accumulator starts at a fixed point, not at the first entry.  With every digit +-1, the first steps
# of a scalar much shorter than its 128 digits add back what they double (2Q - Q = Q), so the accumulator
# would repeat, and with it the hints: two witness nodes of equal value break the maximal sharing a
# program's encoding must have.  From a start point S, the accumulator is 2^k S + ..., which never
# repeats; the sum is off by 2^(bits - 1) S, which the fixed-base part's start takes back.
START = _offset_point()


def var_offset(bits: int = HALF_BITS) -> G1Point:
    """2^(bits - 1) START: what the variable-base sum carries besides the products."""
    out = B.g1_mul(START, 1 << (bits - 1))
    assert out is not None
    return out


def phi(pt: G1Point) -> G1Point:
    return (GLV_BETA * pt[0] % P, pt[1])


def glv_halves(k: int) -> tuple[int, int]:
    """(n1, n2), both odd, |n| < 2^128, with k = n1 + LAMBDA n2 (mod r): Babai's rounding on the basis,
    then the basis vector (or their sum) that makes both odd.  The basis vectors' parities are (1, 0),
    (1, 1), and their sum's (0, 1), so one of them always does."""
    det = R
    rnd = lambda a: (2 * a + det) // (2 * det)
    c1, c2 = rnd(GLV_V2[1] * k), rnd(-GLV_V1[1] * k)
    k1 = k - c1 * GLV_V1[0] - c2 * GLV_V2[0]
    k2 = -c1 * GLV_V1[1] - c2 * GLV_V2[1]
    best = None
    for a in (0, 1, -1):
        for b in (0, 1, -1):
            n1, n2 = k1 + a * GLV_V1[0] + b * GLV_V2[0], k2 + a * GLV_V1[1] + b * GLV_V2[1]
            if n1 % 2 and n2 % 2 and (best is None or max(abs(n1), abs(n2)) < max(map(abs, best))):
                best = (n1, n2)
    assert best is not None
    n1, n2 = best
    ensure((n1 + GLV_LAMBDA * n2 - k) % R == 0 and max(abs(n1), abs(n2)) < 2**HALF_BITS, 'GLV decomposition')
    return n1, n2


def half_word(n: int, bits: int = HALF_BITS) -> int:
    """C with n = 2 C - (2^bits - 1), for odd n with |n| < 2^bits: the column's digits are its bits."""
    ensure(n % 2 == 1 and abs(n) < 2**bits, 'an odd half below 2^bits')
    return (n + 2**bits - 1) // 2


def half_value(c: int, bits: int = HALF_BITS) -> int:
    return 2 * c - (2**bits - 1)


# ---------------------------------------------------------------------------------------------------
# The prover's side: the group law with its hints, on affine points (x, y) as integers
def add_hint(t: G1Point, q: G1Point) -> tuple[G1Point, list[int]]:
    """T + Q and its hints [lambda, d] (plain integers mod p)."""
    dx = (q[0] - t[0]) % P
    ensure(dx != 0, 'an addition with x_Q = x_T')
    d = pow(dx, -1, P)
    lam = (q[1] - t[1]) * d % P
    x3 = (lam * lam - t[0] - q[0]) % P
    return (x3, (lam * (t[0] - x3) - t[1]) % P), [lam, d]


def dbl_hint(t: G1Point) -> tuple[G1Point, list[int]]:
    ensure(t[1] != 0, 'doubling a point with y = 0')
    lam = 3 * t[0] * t[0] * pow(2 * t[1], -1, P) % P
    x3 = (lam * lam - 2 * t[0]) % P
    return (x3, (lam * (t[0] - x3) - t[1]) % P), [lam]


def neg(pt: G1Point) -> G1Point:
    return (pt[0], (-pt[1]) % P)


def group_table(qs: Sequence[G1Point]) -> tuple[list[G1Point], list[list[int]]]:
    """The 2^(g-1) sums Q1 +- Q2 ... +- Qg, entry index with the sign of Q2 as its top bit (1: minus), and
    the hints of the additions in the order the program makes them: level by level, + then -."""
    level, hints = [qs[0]], []
    for q in qs[1:]:
        nxt = []
        for e in level:
            for sq in (q, neg(q)):
                s, h = add_hint(e, sq)
                nxt.append(s)
                hints.append(h)
        level = nxt
    return level, hints


def var_witness(points: Sequence[G1Point], scalars: Sequence[int], bits: int = HALF_BITS) -> dict[str, Any]:
    """The hints of sum_i scalars[i] points[i]: the column words, the tables' hints, each step's.  With
    bits < 128 (tests), the scalars are taken as given halves: columns (P_i, 2 C_i - (2^bits - 1))."""
    if bits == HALF_BITS:
        cols: list[tuple[G1Point, int]] = []
        for pt, k in zip(points, scalars):
            n1, n2 = glv_halves(k % R)
            cols += [(pt, n1), (phi(pt), n2)]
    else:
        cols = list(zip(points, scalars))
    ensure(len(cols) % 4 == 0, 'columns in groups of 4')
    groups = [cols[i : i + 4] for i in range(0, len(cols), 4)]
    tables, table_hints = [], []
    for g in groups:
        tab, h = group_table([q for q, _ in g])
        tables.append(tab)
        table_hints.append(h)
    cw = [half_word(n, bits) for _, n in cols]
    steps: list[list[list[int]]] = []
    t: G1Point | None = None
    for j in range(bits - 1, -1, -1):
        if t is None:
            t = START  # a doubling of START would add nothing: the first step only adds
        hs: list[list[int]] = []
        if j != bits - 1:
            t, hd = dbl_hint(t)
            hs.append(hd)
        for gi in range(len(groups)):
            c = [(cw[4 * gi + k] >> j) & 1 for k in range(4)]
            idx = (c[0] ^ c[1]) * 4 + (c[0] ^ c[2]) * 2 + (c[0] ^ c[3])
            e = tables[gi][idx] if c[0] else neg(tables[gi][idx])
            t, ha = add_hint(t, e)
            hs.append(ha)
        steps.append(hs)
    expect: G1Point | None = var_offset(bits)
    for q, n in cols:
        expect = B.g1_add(expect, B.g1_mul(q, n % R))
    ensure(t == expect, 'the MSM')
    return {'cols': cw, 'tables': table_hints, 'steps': steps, 'result': t}  # the sum plus var_offset(bits)


# fixed base: windows of 8 bits, the top one 6
FIXED_WINDOWS = [(lo, 8) for lo in range(0, 248, 8)] + [(248, 6)]


def fixed_tables(g: G1Point, extra: G1Point | None = None) -> tuple[G1Point, list[list[G1Point]]]:
    """-(sum_j 2^lo_j G + extra), and per window the entries (d + 1) 2^lo G for its digits d."""
    offset = extra
    tabs = []
    for lo, w in FIXED_WINDOWS:
        base = B.g1_mul(g, 1 << lo)
        offset = B.g1_add(offset, base)
        tab: list[G1Point] = []
        e = base
        for _ in range(1 << w):
            assert e is not None
            tab.append(e)
            e = B.g1_add(e, base)
        tabs.append(tab)
    assert offset is not None
    return neg(offset), tabs


_FIXED: dict[tuple[G1Point, G1Point | None], tuple[G1Point, list[list[G1Point]]]] = {}


def fixed(g: G1Point, extra: G1Point | None = None) -> tuple[G1Point, list[list[G1Point]]]:
    if (g, extra) not in _FIXED:
        _FIXED[(g, extra)] = fixed_tables(g, extra)
    return _FIXED[(g, extra)]


def fixed_witness(g: G1Point, v: int, extra: G1Point | None = None) -> dict[str, Any]:
    """The hints of v g - extra for a canonical v < r."""
    ensure(0 <= v < R, 'a canonical scalar')
    start, tabs = fixed(g, extra)
    t, hints = start, []
    for (lo, w), tab in zip(FIXED_WINDOWS, tabs):
        t, h = add_hint(t, tab[(v >> lo) & ((1 << w) - 1)])
        hints.append(h)
    ensure(t == B.g1_add(B.g1_mul(g, v), None if extra is None else neg(extra)), 'the fixed-base product')
    return {'hints': hints, 'result': t}


# ---------------------------------------------------------------------------------------------------
# The program
YQ_HI = 2 * P  # the bound of y_Q: a table entry with its sign, 2p - y


def mont(xs: Sequence[int]) -> list[int]:
    return [to_mont(x % P) for x in xs]


def point_type() -> str:
    return Tbalanced(['2^256'] * 2)


class G1:
    """The group law: ADD ((T, Q), (lambda, d)) -> T + Q and DBL (T, lambda) -> 2T, functions of the
    program (Sym) or bodies (Num); points are pairs of words, T's below KB, Q's x below KB and y below
    2p."""

    def __init__(self, fp: Fp) -> None:
        self.fp, self.be, self.cv = fp, fp.be, Curve(fp)
        be = self.be
        if 'G1ADD' in getattr(be, 'fns', {}):
            self.ADD, self.DBL = be.fns['G1ADD'], be.fns['G1DBL']
            return
        self.ADD = be.function('G1ADD', [[words(2), words(2)], words(2)], self.add_body)
        self.DBL = be.function('G1DBL', [words(2), E('', 256, 0)], self.dbl_body)
        if is_sym(be):
            be.fns['G1ADD'], be.fns['G1DBL'] = self.ADD, self.DBL

    def top2(self, w: Any) -> Any:
        """The word is below 2^254."""
        be = self.be
        if not is_sym(be):
            ensure(w >> 254 == 0, 'hint above 2^254')
            return 0
        return be.verify(be.not1(be.jet('or_1', be.sub(w, 'OOOOOOO', 2), 1)))

    def _norm(self, v: Val) -> Val:
        return v if v.hi <= KB else self.fp.normalize(v)

    def add_body(self, accs: Any) -> Any:
        fp, cv, be = self.fp, self.cv, self.be
        ((xt, yt), (xq, yq)), (lam, d) = accs
        rd = fp.reduce_dot
        one, m1 = (lambda: fp.const(1)), (lambda: fp.const(P - 1))
        c = {
            'xt': Val(xt, KB),
            'yt': Val(yt, KB),
            'xq': Val(xq, KB),
            'yq': Val(yq, YQ_HI),
            'lam': Val(lam, F_HI),
            'd': Val(d, F_HI),
        }
        steps = [
            ('push', ['dx'], lambda c: [fp.sub(c['xq'], c['xt'])]),
            (
                'check',
                lambda c: [
                    cv.zero_check(rd([(c['lam'], c['dx']), (c['yq'], m1()), (c['yt'], one())])),
                    cv.zero_check(rd([(c['d'], c['dx']), (one(), m1())])),
                ],
            ),
            ('push', ['x3'], lambda c: [self._norm(rd([(c['lam'], c['lam']), (c['xt'], m1()), (c['xq'], m1())]))]),
        ]

        def final(c, checks):
            y3 = self._norm(rd([(c['lam'], fp.sub(c['xt'], c['x3'])), (c['yt'], m1())]))
            ensure(c['x3'].hi <= KB and y3.hi <= KB, 'G1ADD output bound')
            return be.seq(be.checks([ch.e for ch in checks]), fp.pack([c['x3'], y3]))

        out = chain(fp, c, steps, final)
        return be.seq(be.checks([self.top2(lam), self.top2(d)]), out) if is_sym(be) else self._num_top2(out, lam, d)

    def _num_top2(self, out: Any, *ws: int) -> Any:
        for w in ws:
            self.top2(w)
        return out

    def dbl_body(self, accs: Any) -> Any:
        fp, cv, be = self.fp, self.cv, self.be
        (xt, yt), lam = accs
        rd = fp.reduce_dot
        m1 = lambda: fp.const(P - 1)
        c = {'xt': Val(xt, KB), 'yt': Val(yt, KB), 'lam': Val(lam, F_HI)}
        th = (-3 * pow(2, -1, P)) % P
        steps = [
            ('check', lambda c: cv.zero_check(rd([(c['lam'], c['yt']), (c['xt'], fp.mul_const(c['xt'], th))]))),
            ('push', ['x3'], lambda c: [self._norm(rd([(c['lam'], c['lam']), (c['xt'], fp.const(P - 2))]))]),
        ]

        def final(c, checks):
            y3 = self._norm(rd([(c['lam'], fp.sub(c['xt'], c['x3'])), (c['yt'], m1())]))
            ensure(c['x3'].hi <= KB and y3.hi <= KB, 'G1DBL output bound')
            return be.seq(be.checks([ch.e for ch in checks]), fp.pack([c['x3'], y3]))

        out = chain(fp, c, steps, final)
        return be.seq(self.top2(lam), out) if is_sym(be) else self._num_top2(out, lam)

    def add(self, t: Any, q: Any, leaf: Any) -> Any:
        return self.be.call(self.ADD, [[t, q], leaf])

    def dbl(self, t: Any, leaf: Any) -> Any:
        return self.be.call(self.DBL, [t, leaf])

    def neg_point(self, pt: Any) -> Any:
        """(x, 2p - y) for a point with y below KB: in Sym, pt is a projected pair of words."""
        fp, be = self.fp, self.be
        if not is_sym(be):
            return [pt[0], fp.neg(Val(pt[1], KB)).e]
        x, y = be.split(pt, words(2))
        return be.pair(x, fp.neg(Val(y, KB)).e)


def _xor1(be: Any, a: Any, b: Any) -> Any:
    return be.jet('xor_1', be.pair(a, b), 1)


class VarMsm:
    """sum_i k_i P_i over the program's backend, with the hints of var_witness.  `prefix` names the
    witness nodes of the hints: <prefix>t<g>_<k> for the tables, <prefix>s<j>_<op> for the steps.  bits:
    digits per column (128; tests use fewer)."""

    def __init__(self, fp: Fp, prefix: str = 'wv', bits: int = HALF_BITS) -> None:
        self.fp, self.be, self.g1 = fp, fp.be, G1(fp)
        self.prefix, self.bits = prefix, bits
        be = self.be
        from .sym import JET_COST

        JET_COST.setdefault('xor_1', 67)
        if is_sym(be):
            self.SEL, self.SIGN = self._sel_fn(), self._sign_fn()

    # Sym: the case trees that select a table entry and give it its sign
    def _sel_fn(self) -> E:
        """SEL8: (s2, (s3, (s4, table))) -> the entry at s2 s3 s4 (s2 the top bit), as select_const does on
        bits, with the entries projected from the table instead of constant."""
        be = self.be
        if 'SEL8' in be.fns:
            return be.fns['SEL8']
        paths = balanced_paths(8)

        def tree(depth, prefix):
            if depth == 3:
                return be.proj(paths[prefix][:-1] + 'H', 512)  # in (table)
            l, r = tree(depth + 1, prefix << 1), tree(depth + 1, (prefix << 1) | 1)
            return be.case(be.drop(l), be.drop(r))

        be.fns['SEL8'] = be.define('SEL8', tree(0, 0))
        return be.fns['SEL8']

    def _sign_fn(self) -> E:
        """SIGN: (c, entry) -> the entry if c = 1 (digit +1), its negation (x, 2p - y) if c = 0."""
        be, fp = self.be, self.fp
        if 'SIGN' in be.fns:
            return be.fns['SIGN']
        be._push_env(1 + 512)
        try:
            x, y = be.proj('IOH', 256), be.proj('IIH', 256)
            minus = be.pair(x, fp.neg(Val(y, KB)).e)
            plus = be.proj('IH', 512)
        finally:
            be._pop_env()
        be.fns['SIGN'] = be.define('SIGN', be.case(minus, plus))
        return be.fns['SIGN']

    def select(self, table: Any, cs: Sequence[Any]) -> Any:
        """The signed entry for the bits c_1 .. c_4 of a step (Sym: E's of type 2)."""
        be = self.be
        if not is_sym(be):
            idx = (cs[0] ^ cs[1]) * 4 + (cs[0] ^ cs[2]) * 2 + (cs[0] ^ cs[3])
            e = table[idx]
            return e if cs[0] else self.g1.neg_point(e)
        s = [_xor1(be, cs[0], cs[k]) for k in (1, 2, 3)]
        entry = be.comp(be.pair(s[0], be.pair(s[1], be.pair(s[2], be.subtree(table)))), self.SEL)
        return be.comp(be.pair(cs[0], entry), self.SIGN)

    def _wit(self, name: str, n: int, value: Any = None) -> Any:
        """A hint: a witness node of n words (Sym), or the value (Num)."""
        be = self.be
        if not is_sym(be):
            return value
        return be.witness(name, Tbalanced(['2^256'] * n), 256 * n)

    def col_checks(self, cols: Sequence[Any]) -> list[Any]:
        """Each column word is below 2^bits."""
        be = self.be
        if not is_sym(be):
            for c in cols:
                ensure(c >> self.bits == 0, 'column word too large')
            return []
        out = []
        for c in cols:
            if self.bits == 128:  # the top half is 0
                for pth in ('OO', 'OI'):
                    out.append(be.verify(be.jet('eq_64', be.pair(be.sub(c, pth, 64), be.const(64, 0)), 1)))
            else:
                ensure(self.bits % 8 == 0 and self.bits < 128, 'bits')
                for i in range(self.bits, 256):
                    out.append(be.verify(be.not1(be.bit(c, i))))
        return out

    def program(self, points: Sequence[Any], cols: Sequence[Any], wit: dict[str, Any] | None = None) -> Any:
        """The sum plus var_offset(bits), from the points (pairs of projected words below KB, Sym; [x, y]
        Montgomery ints, Num) and the column words (projections; ints).  With 128 bits each point gives the columns P, phi(P);
        with fewer (tests), one column each.  wit: var_witness's hints (Num only).  Returns (point,
        checks): an E of the pair (x, y) and a list of unit E's (Sym), or the [x, y] ints and [] (Num)."""
        fp, be = self.fp, self.be
        glv = self.bits == HALF_BITS
        ensure(len(cols) == len(points) * (2 if glv else 1) and len(cols) % 4 == 0, 'columns in groups of 4')
        checks = self.col_checks(cols)
        qs = []
        for pt in points:
            qs.append(list(pt))
            if glv:
                qs.append([fp.mul_const(Val(pt[0], KB), GLV_BETA).e, pt[1]])
        if not is_sym(be):
            return self._num(qs, cols, wit or {}), []
        return be.scope(
            [qs, list(cols)],
            lambda a: self._tables(1, [[be.subtree(a[0][4 * g])] for g in range(len(cols) // 4)], a[0], a[1]),
        ), checks

    def _tables(self, k: int, cur: list[list[E]], qs: list[Any], cw: list[E]) -> E:
        """Level k of the groups' tables (k = 1, 2, 3): every entry plus and minus column k of its group.
        Each level is bound (let) before the next reads it twice; after the last, the loop runs in an
        environment of the tables and the column words alone."""
        be, g1 = self.be, self.g1
        if k == 4:
            return be.scope([cur, cw], self._loop)
        nxt = []
        for g, entries in enumerate(cur):
            q = be.subtree(qs[4 * g + k])
            lst: list[E] = []
            for e in entries:
                for sgn in (0, 1):
                    j = len(lst) + 2**k - 2
                    leaf = self._wit(f'{self.prefix}t{g}_{j}', 2)
                    lst.append(g1.add(e, q if sgn == 0 else g1.neg_point(q), leaf))
            nxt.append(lst)

        def body(accs, lift):
            qs2 = [[lift(w) for w in pt] for pt in qs]
            return self._tables(
                k + 1,
                [[be.subtree(e) if isinstance(e, list) else e for e in g] for g in accs],
                qs2,
                [lift(w) for w in cw],
            )

        return be.let(nxt, body)

    def _step_bits(self, cw: Sequence[E], g: int, j: int) -> list[E]:
        return [self.be.bit(cw[4 * g + k], j) for k in range(4)]

    def _loop(self, run: Any) -> E:
        """The steps, from the top digit down.  The state is (T, run); a step doubles T and adds each
        group's signed entry."""
        be, g1 = self.be, self.g1
        tables, cw = run
        n_groups = len(tables)
        run_shape = [[[E('', 512, 0)] * 8 for _ in range(n_groups)], [E('', 256, 0)] * len(cw)]
        run_w = 512 * 8 * n_groups + 256 * len(cw)
        top = self.bits - 1
        t = be.words_const(mont(START))
        for g in range(n_groups):
            t = g1.add(t, self.select(tables[g], self._step_bits(cw, g, top)), self._wit(f'{self.prefix}s{top}a{g}', 2))
        e = be.pair(t, be.iden())
        for j in range(top - 1, -1, -1):
            be._push_env(512 + run_w)
            try:
                tabs, cws = be._unpack('I', run_shape)
                t = g1.dbl(be.proj('OH', 512), self._wit(f'{self.prefix}s{j}d', 1))
                for g in range(n_groups):
                    q = self.select(tabs[g], self._step_bits(cws, g, j))
                    t = g1.add(t, q, self._wit(f'{self.prefix}s{j}a{g}', 2))
                step = be.pair(t, be.proj('IH', run_w))
            finally:
                be._pop_env()
            e = be.share(be.comp(e, step))
        return be.comp(e, be.proj('OH', 512))

    def _num(self, qs: list[list[int]], cols: Sequence[int], wit: dict[str, Any]) -> list[int]:
        """The same on numbers, with the hints of var_witness."""
        g1 = self.g1
        n_groups = len(cols) // 4
        tables = []
        for g in range(n_groups):
            level, j = [qs[4 * g]], 0
            for k in (1, 2, 3):
                nxt = []
                for e in level:
                    for sgn in (0, 1):
                        q = qs[4 * g + k] if sgn == 0 else g1.neg_point(qs[4 * g + k])
                        nxt.append(g1.add(e, q, mont(wit['tables'][g][j])))
                        j += 1
                level = nxt
            tables.append(level)
        t = mont(START)
        for si, j in enumerate(range(self.bits - 1, -1, -1)):
            hs = iter(wit['steps'][si])
            if si:
                t = g1.dbl(t, mont(next(hs))[0])
            for g in range(n_groups):
                q = self.select(tables[g], [(cols[4 * g + k] >> j) & 1 for k in range(4)])
                t = g1.add(t, q, mont(next(hs)))
        return t


class FixedMsm:
    """v G - extra for the canonical word v (a projection, checked below r by the caller), a constant
    point G and an optional constant point extra (the variable-base part's offset), with the hints of
    fixed_witness: witness nodes <prefix><j> for window j."""

    def __init__(self, fp: Fp, g: G1Point = B.G1_GEN, prefix: str = 'wf', extra: G1Point | None = None) -> None:
        self.fp, self.be, self.g1, self.cv = fp, fp.be, G1(fp), Curve(fp)
        self.prefix = prefix
        start, tabs = fixed(g, extra)
        self.start = mont(start)
        self.tables = [[[mont(e)] for e in tab] for tab in tabs]  # leaves: one group of 2 words

    def program(self, v: Any, hints: Sequence[Sequence[int]] | None = None) -> Any:
        """The product as a pair of words (Sym: an E; Num: ints).  hints: fixed_witness's (Num)."""
        be, g1 = self.be, self.g1
        num = not is_sym(be)
        t = list(self.start) if num else be.words_const(self.start)
        for j, ((lo, w), tab) in enumerate(zip(FIXED_WINDOWS, self.tables)):
            entry = self.cv.select_const(Val(v, WORD_MAX), lo, w, tab)
            entry = entry[0] if num else entry
            leaf = mont(hints[j]) if num and hints is not None else be.witness(f'{self.prefix}{j}', point_type(), 512)
            t = g1.add(t, entry, leaf)
        return t
