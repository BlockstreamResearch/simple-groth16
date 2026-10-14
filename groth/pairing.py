"""The pairing check e(-A, B) e(L, gamma) e(C, delta) e(alpha, beta) = 1 as one polynomial identity.

F_p12 is F_p[w] / M(w), M = w^12 - 18 w^6 + 82 (poly.py), so every product the check needs, in F_p12 and
in the F_p2 arithmetic of B's points, is a polynomial product modulo M.

The check is on u = E(f) = f^(p^6 - 1) = conj(f) / f, the Miller value f in the torus T2 = {u : u conj(u)
= 1}, and on c' = E(c) for the residue witness c (Novakovic and Eagen).  conj is w -> -w, and an element
of T2 other than 1 is (a + w) / (a - w) for one a in F_p6, a polynomial in w^2: 6 words where f takes 12.
The prover writes a for the values after some of the steps (COMMIT) and for c', and each step becomes a
few relations R(w) = 0 (mod M), with u kept as a fraction N / D:

    doubling     N' = N^2 conj(L),  D' = D^2 L,           lambda y - 3/2 x^2
    addition     N' = N g_N conj(L),  D' = D g_D L,       lambda (xQ - x) - (yQ - y)
    committed    N' (a - w) - D' (a + w),  then N, D = a + w, a - w
    at the end   x - x(-psi^3(B)),   y - y(-psi^3(B)),   u pi(c'^-1) pi^2(c') pi^3(c'^-1) - tau as a fraction

L is the product of the lines at P = -A, L, C, and E(L) = conj(L) / L; a line is yP + o with o its odd
part, so conj of it is yP - o.  g = E(c^-1) = (a_c - w) / (a_c + w) at A+, E(c) at A-; c^-1 is a
conjugation.  N and D are never 0: a line's constant term yP is not, and a +- w is not, since w is not
in F_p6.  tau = E(e(alpha, beta))^-1: T2 has order p^6 + 1, which 3 does not divide, so E(W27) = 1 and
the residue's 27th root of unity drops out.  If the relations hold, E(y) = c'^lambda for the Miller value
y of all four pairs, and so y^h = E(y)^((p^6 + 1) / r) = (c'^(p^6 + 1))^(lambda / r) = 1.  Conversely
gcd(lambda / r, (p^6 + 1) / r) = 1, so every honest y has such a c' (E of Novakovic and Eagen's c).

Only B's slopes lambda are committed: x' = lambda^2 - 2x and y' = lambda (x - x') - y are polynomials in
them.  A slope that satisfies its relation is the true one, so every step is the group law: y is never
0 (the twist has no 2-torsion), and xQ != x at every addition, for every point B of the twist.  That
needs no witness: the twist's group is cyclic, so at an addition T = [k] B and Q = [q] B, and T = Q only
if the order of B divides k - q, which tests/test_g2_check.py shows no order does (for the Frobenius
additions, q is an eigenvalue of psi).  After a step whose value is not committed, N and D are products
of higher degree, which the next committed relation carries.

The prover combines the relations with powers of a challenge r, S = sum r^k R_k, and supplies the
quotient Q = S / M.  The program evaluates everything at one point z and checks S(z) = Q(z) M(z).  It
multiplies only in F_p: an F_p12 product becomes one product of two evaluations.

Soundness.  r is the SHA-256 of the public inputs, the proof and everything committed, and z the
SHA-256 of r and Q.  If some R_k is not 0 modulo M, S is not 0 modulo M except for at most 128 values of
r; then S - Q M is a nonzero polynomial of degree at most 219, which vanishes at z with probability at
most 219 / p.  The program gets r and z as witness words and compares them with the two hashes at the
end.

`relations` is written once over an abstract ring: the prover runs it on polynomials to get S and Q,
the tests run it on numbers to compare with the program.
"""
import hashlib
from . import bn254, poly
from .curve import Curve, chain
from .dsl import ensure, balanced, Tbalanced, wv, wpair, wbalanced
from .fp import Fp, Val, P, WORD_MAX, to_mont, from_mont
from .sym import E, Num, words, is_sym, flat, SHA_CTX_W

F_HI = 2**254 - 1 # bound of a committed word: the program checks that its top two bits are 0
KB = 130 * P // 100 # bound of every run value (z^k, r, ...) carried through the loop
THREE_HALVES = 3 * pow(2, -1, P) % P


# ---------------------------------------------------------------------------------------------------
# The loop: 88 steps along the NAF of 6x + 2
def loop_steps():
    """'D' doubling, 'A+' / 'A-' addition of +-Q, then the Frobenius additions 'F1' (pi(Q)), 'F2' (-pi^2(Q))."""
    digits = bn254.ATE_NAF
    steps = []
    for i in range(len(digits) - 2, -1, -1):
        steps.append('D')
        if digits[i]:
            steps.append('A+' if digits[i] > 0 else 'A-')
    return steps + ['F1', 'F2']


STEPS = loop_steps() # 65 doublings, 8 + 13 additions, 2 Frobenius additions
N_STEPS = len(STEPS)
ADDS = ('A+', 'A-', 'F1', 'F2')


def step_points(Q):
    """The point added at each kind of step, for the G2 point Q."""
    Q1 = bn254.g2_frobenius(Q)
    return {'D': None, 'A+': Q, 'A-': bn254.g2_neg(Q), 'F1': Q1, 'F2': bn254.g2_neg(bn254.g2_frobenius(Q1))}


def slopes(Q):
    """(lambda, (c3, c4)) of every step of the G2 point Q, as in bn254.multi_miller_loop_affine."""
    pts, T, out = step_points(Q), Q, []
    for kind in STEPS:
        Qk = pts[kind]
        lam = bn254.affine_double_slope(T) if Qk is None else bn254.affine_add_slope(T, Qk)
        T, coeffs = bn254.affine_step(T, lam, Qk)
        out.append((lam, coeffs))
    return out


def fixed_lines(Q):
    """The line coefficients (c3, c4) = (-lambda, lambda xT - yT) of every step of a fixed point."""
    return [coeffs for _, coeffs in slopes(Q)]


# ---------------------------------------------------------------------------------------------------
# The relations, over a ring
class PolyRing:
    """Polynomials over F_p."""
    X = poly.X
    add, sub, mul = staticmethod(poly.add), staticmethod(poly.sub), staticmethod(poly.mul)
    k = staticmethod(poly.const)
    elem = staticmethod(poly.trim)

    @staticmethod
    def even(a): # an element of F_p6: a polynomial in w^2, given by its 6 coefficients
        return poly.trim([x for c in a for x in (c, 0)])


class NumRing:
    """F_p, the variable set to z."""
    def __init__(self, z):
        self.X = z % P

    add = staticmethod(lambda a, b: (a + b) % P)
    sub = staticmethod(lambda a, b: (a - b) % P)
    mul = staticmethod(lambda a, b: a * b % P)
    k = staticmethod(lambda c: c % P)

    def elem(self, coeffs):
        return poly.evaluate(coeffs, self.X)

    def even(self, a):
        return poly.evaluate(a, self.X * self.X % P)


class DegRing:
    """Degrees: the shape of S, hence the size of Q."""
    X = 1
    add = sub = staticmethod(max)
    mul = staticmethod(lambda a, b: a + b)
    k = staticmethod(lambda c: 0)
    elem = staticmethod(lambda coeffs: 11)
    even = staticmethod(lambda a: 10)


def relations(R, v, lines, tau, commit=None):
    """The relations R_k in order, over the ring R.  v: the values (Prover.witness); lines: fixed_lines of
    gamma and delta; tau: E(T) compressed (Prover); commit: the steps whose Miller value is committed
    (COMMIT).  The values are u = E(f), kept as fractions N / D of polynomials; at a committed step
    u = (a + w) / (a - w), and N, D start again from a + w and a - w."""
    commit = COMMIT if commit is None else commit
    X = R.X
    X3 = R.mul(R.mul(X, X), X)
    U = R.sub(R.mul(X3, X3), R.k(9)) # u = w^6 - 9

    def phi(a): # an F_p2 element as a polynomial
        a = bn254._fp2(a)
        return R.add(R.k(a.c0), R.mul(R.k(a.c1), U))

    def odd(Pt, c3, c4): # c3 xP w + c4 w^3: the line yP + c3 xP w + c4 w^3 without yP, its odd part
        return R.add(R.mul(R.mul(R.k(Pt[0]), X), c3), R.mul(X3, c4))

    xb, yb = v['B']
    ac = R.even(v['ac'])
    cp, cm = R.add(ac, X), R.sub(ac, X) # c' = E(c) = cp / cm
    rels = []
    pts = step_points(v['B'])
    x, y, N, D = phi(xb), phi(yb), cm, cp # u = E(c^-1) = cm / cp
    for i, kind in enumerate(STEPS):
        lam = phi(v['lam'][i])
        if kind == 'D':
            rels.append(R.sub(R.mul(lam, y), R.mul(R.k(THREE_HALVES), R.mul(x, x))))
            x2 = R.sub(R.mul(lam, lam), R.mul(R.k(2), x))
            N, D = R.mul(N, N), R.mul(D, D)
        else:
            xq, yq = phi(pts[kind][0]), phi(pts[kind][1])
            rels.append(R.sub(R.mul(lam, R.sub(xq, x)), R.sub(yq, y)))
            x2 = R.sub(R.sub(R.mul(lam, lam), x), xq)
            if kind in ('A+', 'A-'): # times E(c^-1) or E(c)
                N, D = (R.mul(N, cm), R.mul(D, cp)) if kind == 'A+' else (R.mul(N, cp), R.mul(D, cm))
        m = R.sub(R.mul(lam, x), y) # lambda x - y, the c4 of B's line
        ln = [(v['P'][1], odd(v['P'], R.sub(R.k(0), lam), m)),
              (v['L'][1], odd(v['L'], phi(lines[0][i][0]), phi(lines[0][i][1]))),
              (v['C'][1], odd(v['C'], phi(lines[1][i][0]), phi(lines[1][i][1])))]
        lp = R.mul(R.mul(R.add(R.k(ln[0][0]), ln[0][1]), R.add(R.k(ln[1][0]), ln[1][1])), R.add(R.k(ln[2][0]), ln[2][1]))
        lm = R.mul(R.mul(R.sub(R.k(ln[0][0]), ln[0][1]), R.sub(R.k(ln[1][0]), ln[1][1])), R.sub(R.k(ln[2][0]), ln[2][1]))
        N, D = R.mul(N, lm), R.mul(D, lp) # E(l) = conj(l) / l, and conj(l)(w) = l(-w)
        if commit[i]:
            a = R.even(v['a'][i])
            rels.append(R.sub(R.mul(N, R.sub(a, X)), R.mul(D, R.add(a, X))))
            N, D = R.add(a, X), R.sub(a, X)
        x, y = x2, R.sub(m, R.mul(lam, x2))
    rels.append(R.sub(x, phi(xb.conj() * bn254.FROB3[2])))
    rels.append(R.sub(y, phi(yb.conj() * -bn254.FROB3[3])))
    # u pi(c'^-1) pi^2(c') pi^3(c'^-1) = tau, with pi^n(c') = (a(t_n) + t_n) / (a(t_n) - t_n)
    t = [frob_w(R, n) for n in (1, 2, 3)]
    a = [frob_even(R, v['ac'], n) for n in (1, 2, 3)]
    at = R.even(tau)
    num = R.mul(R.mul(R.mul(R.mul(N, R.sub(a[0], t[0])), R.add(a[1], t[1])), R.sub(a[2], t[2])), R.sub(at, X))
    den = R.mul(R.mul(R.mul(R.mul(D, R.add(a[0], t[0])), R.sub(a[1], t[1])), R.add(a[2], t[2])), R.add(at, X))
    rels.append(R.sub(num, den))
    return rels


def frob_w(R, n):
    """t_n = pi^n(w) (poly.FROB_W)."""
    t = R.k(0)
    for k, g in poly.FROB_W[n]:
        xk = R.X
        for _ in range(k - 1):
            xk = R.mul(xk, R.X)
        t = R.add(t, R.mul(R.k(g), xk))
    return t


def frob_even(R, a, n):
    """pi^n(a) for a in F_p6 given by its 6 coefficients, as a(t_n) = sum a_k t_n^2k: pi^n is a ring
    homomorphism fixing F_p, so a(t_n) = pi^n(a) modulo M.  It has degree 70 for n = 1, 3 and 10 for
    n = 2; the program evaluates it by Horner's rule in t_n(z)^2."""
    t = frob_w(R, n)
    t2 = R.mul(t, t)
    acc = R.k(0)
    for c in reversed(a):
        acc = R.add(R.mul(acc, t2), R.k(c))
    return acc


def horner(R, rels, r):
    """sum r^(n-1-k) R_k, the combination the program accumulates."""
    acc = R.k(0)
    for rel in rels:
        acc = R.add(R.mul(acc, R.k(r)), rel)
    return acc


def _shape(commit):
    """The number of relations and the degree of S (DegRing reads only the structure)."""
    z = bn254.Fp2(0)
    v = dict(P=(0, 0), B=bn254.G2_GEN, C=(0, 0), L=(0, 0), ac=[0] * 6, lam=[z] * N_STEPS, a=[[0] * 6] * N_STEPS)
    rels = relations(DegRing, v, [[(z, z)] * N_STEPS] * 2, [0] * 6, commit)
    return len(rels), max(rels)


def schedule(cap):
    """The steps whose Miller value is committed: every addition, and left to right, a doubling is skipped
    whenever S stays within the degree cap.  A committed value costs 12 words of witness, a degree of S
    one word of Q.  The additions would mostly be committed anyway; committing all of them leaves the
    program three step functions."""
    commit = [True] * N_STEPS
    for i in range(N_STEPS):
        if STEPS[i] in ADDS:
            continue
        commit[i] = False
        if _shape(commit)[1] > cap:
            commit[i] = True
    return commit


DEG_CAP = 216 # the cap with the fewest committed words: 37 Miller values of 6 words, Q of 205 words
COMMIT = schedule(DEG_CAP)
N_RELS, DEG_S = _shape(COMMIT) # 128 relations, degree 216
N_Q = -((11 - DEG_S) // 8) * 8 # coefficients of Q, at least DEG_S - 11, read in chunks of 8 (QCHUNK)


# ---------------------------------------------------------------------------------------------------
# The transcript: r = SHA-256(inputs, points, s, c, c^-1, leaves), z = SHA-256(r, Q), all words big-endian
def wbytes(ws):
    return b''.join(w.to_bytes(32, 'big') for w in ws)


def blocks(n):
    """The hashing blocks of n words: blocks of 16, then powers of two."""
    out = []
    for k in (16, 8, 4, 2, 1):
        while n >= k:
            out.append(k)
            n -= k
            if k < 16:
                break
    return out


def leaf_words(kind, commit):
    """lambda (2 words), a (6) if committed."""
    return 2 + 6 * commit


def miller_values(pairs, c=None):
    """The Miller value after each step of the loop, as the relations have it: from f = c^-1, times c^-1 / c
    at the A+ / A- steps (from 1 and without them if c is None)."""
    (nA, B), _, _ = pairs
    lines = [[bn254.affine_line(cf, Pt) for _, cf in slopes(Q)] for Pt, Q in pairs]
    lams = [lam for lam, _ in slopes(B)]
    ci = c.inv() if c is not None else None
    pts, T, f, out = step_points(B), B, (ci if c is not None else bn254.Fp12.one()), []
    for i, kind in enumerate(STEPS):
        if kind == 'D':
            f = f.square()
        elif c is not None:
            f = f * ci if kind == 'A+' else f * c if kind == 'A-' else f
        T, _ = bn254.affine_step(T, lams[i], pts[kind])
        for k in range(3):
            f = f.mul_by_034(*lines[k][i])
        out.append(f)
    return out


def easy(f):
    """E(f) = f^(p^6 - 1) = conj(f) / f, in the torus T2: E(f) conj(E(f)) = 1."""
    return f.conj() * f.inv()


W_TOWER = bn254.Fp12(bn254.Fp6(0), bn254.Fp6(1)) # w


def compress(u):
    """a in F_p6 with u = (a + w) / (a - w), for u != 1 in T2: a = w (u + 1) / (u - 1), as the 6
    coefficients of a polynomial in w^2."""
    ensure(u != bn254.Fp12.one(), 'u = 1 has no compressed form')
    d = poly.from_tower(W_TOWER * (u + bn254.Fp12.one()) * (u - bn254.Fp12.one()).inv())
    ensure(all(d[k] == 0 for k in range(1, 12, 2)), 'not in F_p6')
    return d[0::2]


class Prover:
    """The witness for the pairs (-A, B), (L, gamma), (C, delta); const is the Miller value of
    (alpha, beta)."""

    def __init__(self, gamma, delta, const):
        self.lines = [fixed_lines(gamma), fixed_lines(delta)]
        self.tau = compress(easy(const).conj()) # E(T_s) = E(e(alpha, beta))^-1 for every s: E(W27) = 1
        self.const = const

    def witness(self, pairs, inputs, residue=None, check=True):
        """The witness, or None if the product of the pairings is not 1.  Tests may give the residue
        witness (c, s) and seal without checking the relations (seal).  The relations hold for
        E(c) and E(f), so s is not needed."""
        (nA, B), (L, _), (C, _) = pairs
        res = residue or bn254.residue_witness(miller_values(pairs)[-1] * self.const)
        if res is None:
            return None
        c, _ = res
        a = [compress(easy(f)) if COMMIT[i] else None for i, f in enumerate(miller_values(pairs, c))]
        v = dict(P=nA, B=B, C=C, L=L, ac=compress(easy(c)), lam=[lam for lam, _ in slopes(B)], a=a)
        return self.seal(v, inputs, check)

    def seal(self, v, inputs, check=True):
        """The witness words of the values v: the committed words, then r, Q and z.  check=False lets a
        test seal values whose relations do not hold (Q is then S / M without its remainder)."""
        mont = lambda xs: [to_mont(x % P) for x in xs]
        fp2 = lambda a: mont([a.c0, a.c1])
        nA, B, C = v['P'], v['B'], v['C']
        w = dict(points=mont([nA[0], nA[1], B[0].c0, B[0].c1, B[1].c0, B[1].c1, C[0], C[1]]), ac=mont(v['ac']),
                 leaves=[fp2(v['lam'][i]) + (mont(v['a'][i]) if COMMIT[i] else []) for i in range(N_STEPS)])
        t = wbytes(inputs) + wbytes(w['points']) + wbytes(w['ac']) + b''.join(map(wbytes, w['leaves']))
        w['r'] = int.from_bytes(hashlib.sha256(t).digest(), 'big')
        q, rem = poly.divmod_m(horner(PolyRing, relations(PolyRing, v, self.lines, self.tau), from_mont(w['r'])))
        ensure(not check or rem == [0] * 12, 'the relations do not hold')
        w['q'] = mont(q + [0] * (N_Q - len(q)))
        w['z'] = int.from_bytes(hashlib.sha256(wbytes([w['r']] + w['q'])).digest(), 'big')
        w['values'] = v
        return w


# ---------------------------------------------------------------------------------------------------
# The program
#
# The loop state is ((e, acc, x, y), h, run): e = f(z), acc the Horner sum of the relations so far,
# (x, y) = B's point at z, h the SHA-256 context of the transcript, and the run values below, computed
# once from z, r and the points.  zeta = z^6 - 9 is u at z; X, Y are the x, y of a point at zeta.
Z_RUN = (1, 2, 3, 4, 5, 6, 7, 8, 10) # the powers of z the steps and Q(z) use
RUN = ([f'z{k}' for k in Z_RUN] +
       ['zeta', 'z3zeta', 'nxpz', 'yp', 'xlz', 'xlzz', 'yl', 'xcz', 'xczz', 'yc', 'r', 'r2', 'r3', 'cp', 'cm',
        'XB', 'YB', 'nYB', 'X1', 'Y1', 'X2'])
END = ['pn', 'npd'] # computed in the setup, used at the end only: the last relation is N pn + D npd
# (xQ, yQ, gN, gD): u times E(c^-1) = cm / cp at A+, E(c) = cp / cm at A-, 1 at the Frobenius additions.
# -pi^2(B) = (omega x, y) for the cube root of unity omega = FROB2[2], so it shares YB.
Q_KEYS = {'A+': ('XB', 'YB', 'cm', 'cp'), 'A-': ('XB', 'nYB', 'cp', 'cm'), 'F1': ('X1', 'Y1', None, None), 'F2': ('X2', 'YB', None, None)}
N_STATE = 5 # N, D, acc, x, y


class PairingCheck:
    """Generator of the check over a backend.  gamma, delta: the fixed G2 points; const: the Miller value
    of (alpha, beta); b: the bounds of the loop state (bounds())."""

    def __init__(self, fp, gamma, delta, const, b=None):
        self.fp, self.be, self.cv = fp, fp.be, Curve(fp)
        self.prover = Prover(gamma, delta, const)
        # per step, the line constants of gamma and delta: c3 and c4, two Montgomery words each
        self.data = [[to_mont(a % P) for k in (0, 1) for cf in self.prover.lines[k][i] for a in (cf.c0, cf.c1)]
                     for i in range(N_STEPS)]
        self.b = dict(b) if b is not None else {}
        if not self.b:
            ensure(not is_sym(self.be), 'the bounds are computed with the numeric backend')
            self.sample_bounds()
        be = self.be
        self.TOP2 = be.function('TOP2', [words(4), words(2)], lambda a: be.checks([self.top2_zero(w) for w in flat(a)]))
        st = self.state_shape()
        self.steps = {}
        for kind, args in (('D', None), ('A', words(4)), ('F', words(4))):
            for commit in sorted({COMMIT[k] for k in range(N_STEPS) if self.fn_of(k)[0] == kind}):
                shape = [[st, leaf_shape({'D': 'D', 'A': 'A+', 'F': 'F1'}[kind], commit)], words(8) if args is None else [args, words(8)]]
                name = f'STEP_{kind}' + ('' if commit else '_')
                self.steps[(kind, commit)] = be.function(name, shape, self.step_body(kind, commit))
        self.QCHUNK = be.function('QCHUNK', [[words(2), words(7)], words(8)], self.qchunk_body)
        self.EVAL = be.function('EVAL', [[words(4), words(2)], E('', 256, 0)], self.eval_body)
        if is_sym(be):
            self.costs = {fn.t: fn.c for fn in list(self.steps.values()) + [self.QCHUNK, self.EVAL]}

    @staticmethod
    def fn_of(k):
        """(function kind, commit) of step k.  A Frobenius addition with a committed value runs the addition's
        function with g = 1, which saves a function."""
        kind = STEPS[k][0]
        return ('A' if kind == 'F' and COMMIT[k] else kind), COMMIT[k]

    def one(self): return self.fp.const(1)
    def m1(self): return self.fp.const(P - 1)
    def rd(self, pairs): return self.fp.reduce_dot(pairs)

    # hashing and the committed words
    def top2_zero(self, w):
        """The word is below 2^254: its two top bits are 0.  Committed words are multiplied in long dot
        products, whose CRT bound a full 256-bit word would exceed."""
        be = self.be
        if not is_sym(be):
            ensure(w >> 254 == 0, 'committed word above 2^254')
            return 0
        return be.verify(be.not1(be.jet('or_1', be.sub(w, 'OOOOOOO', 2), 1)))

    def top2_6(self, ws):
        """top2_zero of 6 projected words (4 + 2), by TOP2."""
        be = self.be
        if not is_sym(be):
            for w in flat(ws):
                self.top2_zero(w)
            return 0
        return be.call(self.TOP2, [be.subtree(ws)])

    def sha_init(self):
        be = self.be
        return be.jet('sha_256_ctx_8_init', be.unit(), SHA_CTX_W) if is_sym(be) else b''

    def sha_add(self, h, parts):
        """Absorb projections of 1, 2, 4, 8 or 16 words."""
        be = self.be
        if not is_sym(be):
            return h + b''.join(wbytes(flat(x)) for x in parts)
        for x in parts:
            x = be.subtree(x) if isinstance(x, list) else x
            h = be.jet(f'sha_256_ctx_8_add_{x.w // 8}', be.pair(h, x), SHA_CTX_W)
        return h

    def sha_final(self, h):
        be = self.be
        return be.jet('sha_256_ctx_8_finalize', h, 256) if is_sym(be) else int.from_bytes(hashlib.sha256(h).digest(), 'big')

    # one step
    def state_shape(self):
        return [words(N_STATE), E('', SHA_CTX_W, 0), words(len(RUN))]

    def step_body(self, kind, commit):
        """Body of a step function: ((state, leaf), args) -> state.  Evaluates lambda and the lines at z and
        -z, the next N and D, and a committed value at z, and adds the step's relations to acc in the order
        of `relations`; absorbs the leaf into h."""
        fp, be, b = self.fp, self.be, self.b
        rd, one, m1 = self.rd, self.one, self.m1
        add = kind != 'D'

        def body(accs):
            (st, leaf), args = accs
            (N, D, acc, x, y), h, run = st
            aw = flat(leaf[1]) if commit else []
            data = args if kind == 'D' else args[1]
            run = dict(zip(RUN, run))
            c = {'N': Val(N, b['N']), 'D': Val(D, b['D']), 'acc': Val(acc, b['acc']), 'x': Val(x, b['x']), 'y': Val(y, b['y']),
                 'l': [Val(w, WORD_MAX) for w in leaf[0]],
                 'dg': [Val(w, P - 1) for w in data[:4]], 'dd': [Val(w, P - 1) for w in data[4:]]}
            if commit:
                c['a'] = [Val(w, F_HI) for w in aw]
                c['zp'] = [Val(run[f'z{k}'], KB) for k in (1, 2, 4, 6, 8, 10)]
            for nm in ('z3', 'zeta', 'z3zeta', 'nxpz', 'yp', 'xlz', 'xlzz', 'yl', 'xcz', 'xczz', 'yc', 'r') + (('r2',) if commit else ()):
                c[nm] = Val(run[nm], KB)
            if add:
                c['xq'], c['yq'], c['gn'], c['gd'] = (Val(w, KB) for w in args[0])
            at_zeta = lambda c, a: rd([(a[1], c['zeta']), (a[0], one())]) # a0 + a1 zeta

            def first(c):
                out = [at_zeta(c, c['l'])]
                if commit: # a(z) = sum a_k z^2k
                    a, zp = c['a'], c['zp']
                    out.append(rd([(a[0], one())] + [(a[k], zp[k]) for k in range(1, 6)]))
                return out + ([fp.sub(c['xq'], c['x'])] if add else [])
            minus_x3 = (lambda c: [(c['x'], m1()), (c['xq'], m1())]) if add else (lambda c: [(c['x'], fp.const(P - 2))])
            steps = [('push', ['lam'] + (['az'] if commit else []) + (['dx'] if add else []), first),
                     ('drop', ['l'] + (['a'] if commit else [])),
                     ('push', ['x2', 'm'] + (['azp', 'azm'] if commit else []), lambda c: [
                         rd([(c['lam'], c['lam'])] + minus_x3(c)), rd([(c['lam'], c['x']), (c['y'], m1())])] +
                         ([fp.normalize(fp.add(c['az'], c['zp'][0])), fp.normalize(fp.sub(c['az'], c['zp'][0]))] if commit else [])),
                     # the odd parts of the lines; a line at z is yP + o, at -z (its conjugate) yP - o
                     ('push', ['oB', 'og', 'od'], lambda c: [
                         rd([(c['nxpz'], c['lam']), (c['z3'], c['m'])]),
                         rd([(c['xlz'], c['dg'][0]), (c['xlzz'], c['dg'][1]), (c['z3'], c['dg'][2]), (c['z3zeta'], c['dg'][3])]),
                         rd([(c['xcz'], c['dd'][0]), (c['xczz'], c['dd'][1]), (c['z3'], c['dd'][2]), (c['z3zeta'], c['dd'][3])])])]

            def final(c, _):
                lam, m, x2 = c['lam'], c['m'], c['x2']
                y2 = rd([(m, one()), (lam, fp.neg(x2))])
                odd = [c['oB'], c['og'], c['od']]
                ys = [c['yp'], c['yl'], c['yc']]
                lp = [fp.add(yv, o) for yv, o in zip(ys, odd)]
                lm = [fp.sub(yv, o) for yv, o in zip(ys, odd)]
                Lp = rd([(rd([(lp[0], lp[1])]), lp[2])])
                Lm = rd([(rd([(lm[0], lm[1])]), lm[2])])
                if kind == 'D':
                    N2, D2 = rd([(c['N'], c['N'])]), rd([(c['D'], c['D'])])
                    rels = [[(lam, c['y']), (c['x'], fp.mul_const(c['x'], -THREE_HALVES))]] # as dot products
                else:
                    N2, D2 = rd([(c['N'], c['gn'])]), rd([(c['D'], c['gd'])])
                    rels = [[(lam, c['dx']), (c['yq'], m1()), (c['y'], one())]]
                Nn, Dn = rd([(N2, Lm)]), rd([(D2, Lp)])
                # Horner: acc r^n + the step's relations; a relation of weight 1 joins the sum unreduced
                r_pow = lambda j: one() if j == 0 else c['r' if j == 1 else f'r{j}']
                n = len(rels) + commit
                terms = [(c['acc'], r_pow(n))]
                for k, rel in enumerate(rels):
                    terms += rel if n - 1 - k == 0 else [(rd(rel), r_pow(n - 1 - k))]
                if commit: # N (a - z) - D (a + z), then N, D = a + z, a - z
                    acc2 = rd(terms + [(Nn, c['azm']), (Dn, fp.neg(c['azp']))])
                    N3, D3 = c['azp'], c['azm']
                else:
                    acc2 = rd(terms)
                    N3, D3 = Nn, Dn
                outs = [N3, D3, acc2, x2, y2]
                for nm, v in zip(('N', 'D', 'acc', 'x', 'y'), outs):
                    b[nm + '_out'] = max(b.get(nm + '_out', 0), v.hi)
                return fp.pack(outs)
            new = chain(fp, c, steps, final)
            h2 = self.sha_add(h, [leaf[0]] + ([leaf[1][0], leaf[1][1]] if commit else []))
            out = be.pack([new, h2, be.subtree(list(run.values()))])
            return be.seq(self.top2_6(leaf[1]), out) if commit else out
        return body

    def qchunk_body(self, accs):
        """Body of QCHUNK: ((qz, z^8), (z .. z^7)), 8 coefficients of Q -> qz z^8 + their polynomial at z.
        Q(z) is this step from the top chunk down; the coefficients are checked below 2^254."""
        ((qz, z8), zp), q = accs
        one, b = self.one(), self.b
        out = self.rd([(Val(qz, b['qz']), Val(z8, KB)), (Val(q[0], F_HI), one)] +
                      [(Val(q[k], F_HI), Val(zp[k - 1], KB)) for k in range(1, 8)])
        b['qz_out'] = max(b.get('qz_out', 0), out.hi)
        return self.be.seq(self.be.checks([self.top2_zero(w) for w in q]), out.e)

    def eval_body(self, accs):
        """Body of EVAL: ((a_0 .. a_3, a_4 a_5), t^2) -> a(t) = sum a_k t^2k by Horner, for an element a of F_p6
        (words below 2^254: committed words, or constants) and t^2 below KB."""
        a, t2 = accs
        a = flat(a)
        t2 = Val(t2, KB)
        acc = Val(a[5], F_HI)
        for k in range(4, -1, -1):
            acc = self.rd([(acc, t2), (Val(a[k], F_HI), self.one())])
        self.eval_hi = acc.hi
        return acc.e

    def eval_at(self, coeffs, t2):
        """a(t) for the 6 words of a (projected, one subtree, 4 + 2 words; or a constant) and t^2, by EVAL."""
        t2 = t2 if t2.hi <= KB else self.fp.normalize(t2)
        be = self.be
        if not is_sym(be):
            a = [[x.e if isinstance(x, Val) else x for x in g] for g in coeffs]
        elif isinstance(coeffs, E):
            a = coeffs
        else:
            a = be.subtree([v.e for v in flat(coeffs)])
        return Val(be.call(self.EVAL, [a, t2.e]), self.eval_hi)

    def sample_bounds(self):
        """The bounds of the loop state: a fixed point of the step bodies, found on the numeric backend by
        widening the inputs (1% slack) until the outputs fit."""
        b = self.b
        names = ('N', 'D', 'acc', 'x', 'y', 'qz')
        b.update({nm: KB for nm in names})
        st = [[0] * N_STATE, b'', [0] * len(RUN)]
        for _ in range(30):
            for nm in names:
                b[nm + '_out'] = 0
            for kind, n_args in (('D', 0), ('A', 4)):
                for commit in (False, True):
                    leaf = [[0, 0]] + ([[[0] * 4, [0] * 2]] if commit else [])
                    self.step_body(kind, commit)([[st, leaf], [[0] * n_args, [0] * 8] if n_args else [0] * 8])
            self.qchunk_body([[[0, 0], [0] * 7], [0] * 8])
            if all(b[nm + '_out'] <= b[nm] for nm in names):
                return
            for nm in names:
                b[nm] = max(b[nm], b[nm + '_out'] * 101 // 100)
        raise RuntimeError('no fixed point for the loop bounds')

    # the loop
    def step_value(self, k, st, env):
        be = self.be
        kind = STEPS[k]
        data = be.words_const(self.data[k]) if is_sym(be) else self.data[k]
        fk = self.fn_of(k)
        fn = self.steps[fk]
        if kind == 'D':
            return be.call(fn, [env, data])
        run = dict(zip(RUN, st[2]))
        args = [self.one().e if nm is None else be.subtree(run[nm]) if is_sym(be) else run[nm] for nm in Q_KEYS[kind]]
        return be.call(fn, [env, [args, data]])

    def loop(self, state0, leaves):
        be = self.be
        if not is_sym(be):
            for k, leaf in enumerate(leaves):
                state0 = self.step_value(k, state0, [state0, leaf])
            return state0
        widths = [256 * leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS)]
        return be.comp(be.pair(state0, leaves), fold_leaves(be, self.state_shape(), widths,
                                                          lambda k: lambda accs: self.step_value(k, accs[0], be.iden())))

    # before the loop
    def setup(self, inputs, pts, ac, rz):
        """((N, D, acc, x, y), h, run) and the END values.  Checks A, B, C on their curves and the words of
        a_c, computes the run values, starts u = E(c^-1) as N / D = (a_c(z) - z) / (a_c(z) + z), and starts
        h with the public inputs, the points and a_c."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, m1, lc = self.rd, self.one, self.m1, fp.lin_const
        z = lambda k: 'z' if k == 1 else f'z{k}'
        raw = lambda w: Val(w, WORD_MAX)
        ctx = {'raw': [raw(rz[1]), raw(rz[0]), [raw(w) for w in flat(pts)], inputs['L'][0], inputs['L'][1]],
               'ac': [[Val(w, F_HI) for w in g] for g in ac]}
        tau = [[to_mont(v) for v in self.prover.tau[:4]], [to_mont(v) for v in self.prover.tau[4:]]]
        tau = be.consts(256, tau) if is_sym(be) else tau

        def at_zeta_conj(c, a0, a1, g):
            """conj(a) g at zeta: a0 (g0 + g1 zeta) + a1 (g1 - g0 zeta)"""
            return rd([(a0, lc([(one(), g.c0), (c['zeta'], g.c1)])), (a1, lc([(one(), g.c1), (c['zeta'], -g.c0)]))])

        t_at = lambda n, c: lc([(c[z(k)], g) for k, g in poly.FROB_W[n]]) # t_n(z)
        sq = lambda a: lambda c: rd([(c[a], c[a])])
        mu = lambda a, b: lambda c: rd([(c[a], c[b])])
        layers = [[('z2', sq('z'))], [('z3', mu('z2', 'z')), ('z4', sq('z2'))],
                  [('z5', mu('z4', 'z')), ('z6', sq('z3')), ('z7', mu('z4', 'z3')), ('z8', sq('z4'))], [('z10', sq('z5'))]]
        # The first layer normalises the inputs into a fresh environment, which the on-curve checks then read;
        # every later layer pushes its values in front of it, so a_c and the points are not copied along.
        norm = lambda c: [fp.normalize(c['raw'][0]), fp.normalize(c['raw'][1]), [fp.normalize(v) for v in c['raw'][2]],
                          fp.normalize(c['raw'][3]), fp.normalize(c['raw'][4])]
        on_curve = lambda c: [Val(e, 0) for e in (cv.g1_on_curve_check(c['p'][0], c['p'][1]), cv.g2_on_curve_check(
            (c['p'][2], c['p'][3]), (c['p'][4], c['p'][5])), cv.g1_on_curve_check(c['p'][6], c['p'][7]))]
        steps = [('let', ['z', 'r', 'p', 'xl', 'yl'], norm, ['raw']), ('check', on_curve)] + [
            ('push', [n for n, _ in L], (lambda L: lambda c: [f(c) for _, f in L])(L)) for L in layers] + [
            ('push', ['zeta', 'nz', 't1', 't2'], lambda c: [lc([(c['z6'], 1), (one(), -9)]), fp.mul_const(c['z'], -1), t_at(1, c), t_at(2, c)]),
            ('push', ['acz', 'r2', 't3', 't1s', 't2s'], lambda c: [self.eval_at(c['ac'], c['z2']), rd([(c['r'], c['r'])]),
                                                            fp.mul_const(c['t1'], poly.FROB_W[2][0][1]), # t3 = g t1
                                                            rd([(c['t1'], c['t1'])]), rd([(c['t2'], c['t2'])])]),
            ('push', ['xlz', 'xcz', 'XB', 'YB', 'r3', 'z3zeta', 't3s', 'A1', 'A2'], lambda c: [
                rd([(c['xl'], c['z'])]), rd([(c['p'][6], c['z'])]), rd([(c['p'][2], one()), (c['p'][3], c['zeta'])]),
                rd([(c['p'][4], one()), (c['p'][5], c['zeta'])]), rd([(c['r2'], c['r'])]), rd([(c['z3'], c['zeta'])]),
                rd([(c['t3'], c['t3'])]), self.eval_at(c['ac'], c['t1s']), self.eval_at(c['ac'], c['t2s'])])]
        end_hi = []

        def final(c, checks):
            g1, g2 = bn254.FROB1, bn254.FROB2
            vals = {f'z{k}': c[z(k)] for k in Z_RUN}
            vals.update({nm: c[nm] for nm in ('zeta', 'z3zeta', 'xlz', 'yl', 'xcz', 'r', 'r2', 'r3', 'XB', 'YB')})
            vals.update(nxpz=rd([(c['p'][0], c['nz'])]), yp=c['p'][1], xlzz=rd([(c['xlz'], c['zeta'])]),
                        xczz=rd([(c['xcz'], c['zeta'])]), yc=c['p'][7], nYB=fp.mul_const(c['YB'], -1),
                        X1=at_zeta_conj(c, c['p'][2], c['p'][3], g1[2]), Y1=at_zeta_conj(c, c['p'][4], c['p'][5], g1[3]),
                        X2=fp.mul_const(c['XB'], g2[2].c0),
                        cp=fp.add(c['acz'], c['z']), cm=fp.sub(c['acz'], c['z'])) # E(c) = cp / cm at z
            run = []
            for nm in RUN:
                v = vals[nm] if vals[nm].hi <= KB else fp.normalize(vals[nm])
                ensure(v.hi <= KB, f'run value bound: {nm}')
                run.append(v)
            rv = dict(zip(RUN, run))
            start = [rv['cm'], rv['cp'], fp.const(0), rv['XB'], rv['YB']] # u = E(c^-1) = cm / cp
            for nm, v in zip(('N', 'D', 'acc', 'x', 'y'), start):
                ensure(v.hi <= self.b[nm], f'initial bound: {nm}')
            # the last relation N pn - D pd: pi(c'^-1) pi^2(c') pi^3(c'^-1) / tau, numerator and denominator
            A3, At = self.eval_at(c['ac'], c['t3s']), self.eval_at(tau, c['z2'])
            prod = lambda vs: rd([(rd([(rd([(vs[0], vs[1])]), vs[2])]), vs[3])])
            pn = prod([fp.sub(c['A1'], c['t1']), fp.add(c['A2'], c['t2']), fp.sub(A3, c['t3']), fp.sub(At, c['z'])])
            pd = prod([fp.add(c['A1'], c['t1']), fp.sub(c['A2'], c['t2']), fp.add(A3, c['t3']), fp.add(At, c['z'])])
            end = [pn, fp.mul_const(pd, -1)]
            end_hi.extend(v.hi for v in end)
            return be.seq(be.checks([ch.e for ch in checks]), be.pack([fp.pack([start, run]), fp.pack(end)]))
        out = chain(fp, ctx, steps, final)
        self.end_hi = end_hi
        h = self.sha_add(self.sha_init(), list(inputs['words']) + [pts])
        h = self.sha_add(h, [ac[0], ac[1]])
        return be.seq(self.top2_6(ac), self._with_h(out, h))

    def _with_h(self, out, h):
        """((start, run), end) and h -> ((start, h, run), end)"""
        be = self.be
        if not is_sym(be):
            (start, run), end = out
            return [[start, h, run], end]
        shape = [[[words(N_STATE), words(len(RUN))], words(len(END))], E('', SHA_CTX_W, 0)]
        return be.with_env(be.pair(out, h), shape, lambda a: be.pack(
            [[be.subtree(a[0][0][0]), a[1], be.subtree(a[0][0][1])], be.subtree(a[0][1])]))

    # after the loop
    def final(self, state, end, q, rz):
        """The last three relations, S(z) = Q(z) M(z), and r, z against the two hashes."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, m1 = self.rd, self.one, self.m1
        (N, D, acc, x, y), h, run = state
        run = {nm: Val(w, KB) for nm, w in zip(RUN, run)}
        b = self.b
        chunks = [half for blk in q for half in ([blk] if len(blk) == 8 else [blk[:8], blk[8:]])]
        ensure(len(blocks(N_Q)) == len(q) and all(len(ch) == 8 for ch in chunks), 'Q is read in chunks of 8 words')
        qz = be.word(0)
        for ch in reversed(chunks):
            zs = [run[f'z{k}'].e for k in range(1, 8)]
            qz = be.call(self.QCHUNK, [[[qz, run['z8'].e], zs], be.subtree(ch) if is_sym(be) else ch])
        c = {'N': Val(N, b['N']), 'D': Val(D, b['D']), 'acc': Val(acc, b['acc']), 'x': Val(x, b['x']), 'y': Val(y, b['y']),
             'qz': Val(qz, b['qz'])}
        c.update({nm: Val(w, hi) for nm, w, hi in zip(END, end, self.end_hi)})
        c.update({nm: run[nm] for nm in ('r', 'r2', 'r3', 'z6', 'X1', 'Y1')})

        def horner_end(c):
            # -psi^3(B) = psi^2(psi(B)) negated, and psi^2 (x, y) = (omega x, -y): its point at zeta is (omega X1, Y1)
            X3 = fp.mul_const(c['X1'], bn254.FROB2[2].c0)
            g2 = rd([(c['x'], c['r2']), (X3, fp.mul_const(c['r2'], -1)), (c['y'], c['r']), (c['Y1'], fp.mul_const(c['r'], -1))])
            return rd([(c['acc'], c['r3']), (g2, one()), (c['N'], c['pn']), (c['D'], c['npd'])])

        steps = [('let', ['s', 'z12'], lambda c: [horner_end(c), rd([(c['z6'], c['z6'])])]),
                 ('drop', ['acc', 'x', 'y', 'N', 'D', 'r', 'r2', 'r3', 'X1', 'Y1'] + END)]

        def check(c, _):
            minus_m = fp.lin_const([(c['z12'], -1), (c['z6'], 18), (one(), -82)])
            return cv.zero_check(rd([(c['s'], one()), (c['qz'], minus_m)])).e
        identity = chain(fp, c, steps, check)
        r_hash = self.sha_final(h)
        z_hash = self.sha_final(self.sha_add(self.sha_add(self.sha_init(), [rz[0]]), list(q)))
        if not is_sym(be):
            ensure(r_hash == rz[0] and z_hash == rz[1], 'challenge')
            return 0
        return be.checks([identity, be.verify(be.eq256(r_hash, rz[0])), be.verify(be.eq256(z_hash, rz[1]))])

    def program(self, inputs, pts, ac, rz, leaves, q):
        """The whole check.  inputs: {'L': (x, y) Vals, 'words': the public input accessors}; the rest as
        in witness_shape().  Sym: a unit-typed E over the environment; Num: runs the checks."""
        be = self.be
        s0 = self.setup(inputs, pts, ac, rz)
        if not is_sym(be):
            st0, end = s0
            return self.final(self.loop(st0, leaves), end, q, rz)
        lw = sum(256 * leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS))
        qshape = [words(n) for n in blocks(N_Q)]
        parts = {}

        def body(a):
            (st0, end), (lv, (qa, rza)) = a
            st = self.loop(be.subtree(st0), lv)
            out = be.with_env(be.pack([st, be.subtree(end), be.subtree(qa), be.subtree(rza)]),
                              [self.state_shape(), words(len(END)), qshape, words(2)], lambda a: self.final(*a))
            parts.update(loop=st.c, final=out.c - st.c)
            return out
        out = be.with_env(be.pack([s0, [be.subtree(leaves), [be.subtree(q), be.subtree(rz)]]]),
                          [[self.state_shape(), words(len(END))], [E('', lw, 0), [qshape, words(2)]]], body)
        self.parts = {'setup': s0.c, **parts}
        return out


def fold_leaves(be, state_shape, widths, step):
    """Fold a state over the leaves of a balanced tree, of the given widths (as curve.fold_tree)."""
    state_w = sum(e.w for e in flat(state_shape))

    def go(lo, hi):
        if hi - lo == 1:
            be._push_env(state_w + widths[lo])
            try:
                return step(lo)((be._unpack('O', state_shape), be.proj('IH', widths[lo])))
            finally:
                be._pop_env()
        mid = lo + (hi - lo + 1) // 2
        inner = be.comp(be.pair(be.proj('OH', state_w), be.proj('IOH', sum(widths[lo:mid]))), go(lo, mid))
        return be.comp(be.pair(inner, be.proj('IIH', sum(widths[mid:hi]))), go(mid, hi))
    return go(0, len(widths))


_BOUNDS = None


def bounds():
    """The bounds of the loop state (they depend on the structure only), computed once."""
    global _BOUNDS
    if _BOUNDS is None:
        G = bn254.G2_GEN
        _BOUNDS = PairingCheck(Fp(Num()), G, G, bn254.Fp12(bn254.Fp6(1), bn254.Fp6(1))).b # any constant outside F_p6
    return _BOUNDS


# ---------------------------------------------------------------------------------------------------
# The witness of the check: ((points, a_c), ((r, z), (leaves, Q))).  a_c and a committed value: 4 + 2 words;
# a leaf: lambda, or (lambda, a); Q in hashing blocks.
def leaf_shape(kind, commit):
    """(lambda, a): a (4 + 2 words) if committed."""
    return [words(2)] + ([[words(4), words(2)]] if commit else [])


def witness_shape():
    leaves = [leaf_shape(kind, COMMIT[k]) for k, kind in enumerate(STEPS)]
    return [[words(8), [words(4), words(2)]], [words(2), [leaves, [words(n) for n in blocks(N_Q)]]]]


def witness_type():
    T = lambda n: Tbalanced(['2^256'] * n)
    a = f'({T(4)} * {T(2)})'
    leaf = lambda kind, commit: Tbalanced([T(2)] + ([a] if commit else []))
    leaves = Tbalanced([leaf(kind, COMMIT[k]) for k, kind in enumerate(STEPS)])
    return f'(({T(8)} * {a}) * ({T(2)} * ({leaves} * {Tbalanced([T(n) for n in blocks(N_Q)])})))'


def witness_bits():
    return 256 * (8 + 6 + 2 + N_Q + sum(leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS)))


def _split(w):
    def leaf(k, lf):
        return [lf[:2]] + ([[lf[2:6], lf[6:8]]] if COMMIT[k] else [])
    qs, i = [], 0
    for n in blocks(N_Q):
        qs.append(w['q'][i:i + n])
        i += n
    return w['points'], [w['ac'][:4], w['ac'][4:]], [leaf(k, lf) for k, lf in enumerate(w['leaves'])], qs


def witness_num(w):
    """The witness as the nested value the numeric backend takes."""
    pts, ac, leaves, qs = _split(w)
    return [[pts, ac], [[w['r'], w['z']], [leaves, qs]]]


def witness_value(w):
    """The witness as a harness value spec (tools/harness)."""
    pts, ac, leaves, qs = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    pair2 = lambda a: wpair(W(a[0]), W(a[1]))
    leaf = lambda lf: balanced([W(lf[0])] + [pair2(x) for x in lf[1:]], wpair)
    return wpair(wpair(W(pts), pair2(ac)),
                 wpair(W([w['r'], w['z']]), wpair(wbalanced([leaf(lf) for lf in leaves]), wbalanced([W(x) for x in qs]))))
