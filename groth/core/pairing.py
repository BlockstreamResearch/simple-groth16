"""The pairing check e(-A, B) e(C, delta) e(alpha, beta) e(L, gamma) = 1 as one polynomial identity.

F_p12 is F_p[w] / M(w), M = w^12 - 18 w^6 + 82 (poly.py), so every product the check needs, in F_p12 and
in the F_p2 arithmetic of B's points, is a polynomial product modulo M.

The check is on u = E(f) = f^(p^6 - 1) = conj(f) / f, the Miller value f in the torus T2 = {u : u conj(u)
= 1}, and on c' = E(c) for the residue witness c (Novakovic and Eagen).  conj is w -> -w, and an element
of T2 other than 1 is (a + w) / (a - w) for one a in F_p6, a polynomial in w^2: 6 words where f takes 12.
The prover writes a for the values after some of the steps (COMMIT) and for c', and each step becomes a
few relations R(w) = 0 (mod M), with u kept as a fraction N / D:

    doubling     N' = N^2 conj(l),  D' = D^2 l,           lambda y - 3/2 x^2
    addition     N' = N g_N conj(l),  D' = D g_D l,       lambda (xQ - x) - (yQ - y)
    committed    N' (a - w) - D' (a + w),  then N, D = a + w, a - w
    at the end   x - x(-psi^3(B)),   y - y(-psi^3(B)),   u pi(c'^-1) pi^2(c') pi^3(c'^-1) - tau as a fraction

l is the product of the lines at P = -A and C, and E(l) = conj(l) / l; a line is yP + o with o its odd
part, so conj of it is yP - o.  g = E(c^-1) = (a_c - w) / (a_c + w) at A+, E(c) at A-; c^-1 is a
conjugation.  N and D are never 0: a line's constant term yP is not, and a +- w is not, since w is not
in F_p6.  T2 has order p^6 + 1, which 3 does not divide, so E(W27) = 1 and the residue's 27th root of
unity drops out.

The public inputs' term.  By bilinearity e(L, gamma) = e(IC_0, gamma) prod_i e(IC_i, gamma)^(x_i), a
product of constants of GT: so gamma has no Miller loop, and L is never computed.  Each input is cut into
windows of 8 bits, and for the digit d of a window the program selects a constant from a table by the
bits of the input (curve.select_const).  The constants are E-images of order r, so they lie in the
cyclotomic subgroup T6, where (s + 1) / (s - 1), s = b0 w + b1 w^3 + b2 w^5 (b_i in F_p2), satisfies
b0 b2 - b1^2 = kappa = 1 / (3 xi): b1 and b2 suffice, 4 words.  Scaled by b2, the factor is
(sigma + b2) / (sigma - b2) with sigma = (kappa + b1^2) w + b1 b2 w^3 + b2^2 w^5, and the additions
multiply N and D by such factors (in g_N, g_D above), as many as each relation has room for under the
degree cap; a factor multiplied in before k more doublings is the 2^k-th root of the one it stands for.
An addition with an odd number of factors multiplies N and D by w as well, which keeps D(w) = N(-w).
The top window of the first input is merged with the end's constant: tau_d, one per digit d of that
window (64), is E(f K_0 prod_i K_i^-offset_i K_1^((d + 1) 2^248))^-1, f the Miller value of (alpha, beta)
and K_i the element of order r with K_i^h = e(IC_i, gamma) (gt_constants).

If the relations hold, E(f) = c'^LAMBDA (bn254.LAMBDA = 6x + 2 + p - p^2 + p^3) for the product f of
the pairs' Miller values, the inputs' term and the constant, and so f^h = E(f)^((p^6 + 1) / r) =
(c'^(p^6 + 1))^(LAMBDA / r) = 1.  Conversely gcd(LAMBDA / r, (p^6 + 1) / r) = 1, so every honest f has
such a c' (E of Novakovic and Eagen's c).

Only B's slopes lambda are committed: x' = lambda^2 - 2x and y' = lambda (x - x') - y are polynomials in
them.  A slope that satisfies its relation is the true one, so every step is the group law: y is never
0 (the twist has no 2-torsion), and xQ != x at every addition, for every point B of the twist.  That
needs no witness: the twist's group is cyclic, so at an addition T = [k] B and Q = [q] B, and T = Q only
if the order of B divides k - q, which tests/test_g2_check.py shows no order does (for the Frobenius
additions, q is an eigenvalue of psi).  After a step whose value is not committed, N and D are products
of higher degree, which the next committed relation carries.

The prover combines the relations with powers of a challenge rho (the witness word `r`) into one
polynomial S, and supplies the quotient Q = S / M.  The program evaluates everything at one point z and
checks S(z) = Q(z) M(z).  It multiplies only in F_p: an F_p12 product becomes one product of two
evaluations.  D is N with w -> -w, so a committed relation keeps only the odd part of N (a - w): its
degree is 9 less than the product's (DegRing tracks both parts).

Every relation is an even or an odd polynomial: a slope's and the two of the G2 check are polynomials in
w^6, a committed value's and the last one are odd.  `combine` multiplies the even ones by w: S = S_o +
rho w S_e, with S_o = sum rho^2j O_j over the odd relations and S_e = sum rho^2i E_i over the even ones,
so S is odd.  M is even, so Q is odd as well, Q = w Q'(w^2), and the witness has the coefficients of Q'
only: half the words, and the check is S(z) = z Q'(z^2) M(z).  The odd relations get the even powers of
rho and the even ones the odd powers, so each relation has a power of its own.

Soundness.  rho is the SHA-256 of the public inputs, the proof and everything committed, and z the
SHA-256 of rho and Q'.  If some relation is not 0 modulo M, S is not 0 modulo M except for at most 179
values of rho, its degree in rho (w is a unit, so w E_i is 0 only if E_i is); then S - w Q'(w^2) M is a
nonzero polynomial of degree at most max(deg S, 2 n_Q + 11), n_Q the words of Q' (the bound is 171 for
one input, 235 for three), which vanishes at z with probability at most that degree over p.  The program
gets rho and z as witness words and compares them with the two hashes at the end.

`relations` is written once over an abstract ring: the prover runs it on polynomials to get S and Q,
the tests run it on numbers to compare with the program.
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from typing import Any

from . import bn254, poly
from .curve import Curve, chain
from .dsl import Tbalanced, WSpec, balanced, ensure, wbalanced, wpair, wv
from .fp import CRT_MAX, WORD_MAX, Fp, P, Val, from_mont, to_mont
from .sym import SHA_CTX_W, E, Num, Shape, Term, flat, is_sym, words

Ring = Any  # PolyRing, NumRing or DegRing: add, sub, mul, k (a constant), even (an element of F_p6), conj_sub, X
Window = tuple[int, int, int]  # (input, lowest bit, width)

F_HI = 2**254 - 1  # bound of a committed word: the program checks that its top two bits are 0
KB = 130 * P // 100  # bound of every run value (z^k, r, ...) carried through the loop
THREE_HALVES = 3 * pow(2, -1, P) % P


# ---------------------------------------------------------------------------------------------------
# The loop: 88 steps along the NAF of 6x + 2
def loop_steps() -> list[str]:
    """'D' doubling, 'A+' / 'A-' addition of +-Q, then the Frobenius additions 'F1' (pi(Q)), 'F2' (-pi^2(Q))."""
    digits = bn254.ATE_NAF
    steps = []
    for i in range(len(digits) - 2, -1, -1):
        steps.append('D')
        if digits[i]:
            steps.append('A+' if digits[i] > 0 else 'A-')
    return steps + ['F1', 'F2']


STEPS = loop_steps()  # 65 doublings, 8 + 13 additions, 2 Frobenius additions
N_STEPS = len(STEPS)
ADDS = ('A+', 'A-', 'F1', 'F2')

# The twist E'(F_p2) is cyclic of order r h, h = 2p - r squarefree, the product of COFACTOR_PRIMES, and
# psi multiplies its points of prime order l by PSI_EIGEN[l] (tests/test_g2_check.py derives them).
COFACTOR_PRIMES = (10069, 5864401, 1875725156269, 197620364512881247228717050342013327560683201906968909)
PSI_EIGEN = {
    10069: 5166,
    5864401: 5415174,
    1875725156269: 1368874307508,
    197620364512881247228717050342013327560683201906968909: 158432335229605513038047029902729871849380703471871696,
    bn254.R: bn254.P % bn254.R,
}


def additions_avoid_q(steps: Sequence[str]) -> bool:
    """Whatever the point B of the twist, no addition of the loop `steps` meets T = Q, and the loop reaches
    [6x + 2] B before its two Frobenius additions.  The slope relations need the first (they have no
    inverse of xQ - x, so T = Q would leave the prover a free slope), and the G2 check after the loop the
    second.  With T = [k] B and Q = [q] B (q = +-1, then psi(B) and -psi^2(B)), T = Q needs k = q modulo
    a prime of the group order."""
    if list(steps[-2:]) != ['F1', 'F2'] or any(kind not in ('D', 'A+', 'A-') for kind in steps[:-2]):
        return False
    k = 1
    for kind in steps[:-2]:
        if kind == 'D':
            k *= 2
        else:
            q = 1 if kind == 'A+' else -1
            if any((k - q) % l == 0 for l in PSI_EIGEN):
                return False
            k += q
    return k == 6 * bn254.X + 2 and all((k - mu) % l and (k + mu + mu * mu) % l for l, mu in PSI_EIGEN.items())


def step_points(Q: bn254.G2Point) -> dict[str, bn254.G2Point | None]:
    """The point added at each kind of step, for the G2 point Q."""
    Q1 = bn254.g2_frobenius(Q)
    return {'D': None, 'A+': Q, 'A-': bn254.g2_neg(Q), 'F1': Q1, 'F2': bn254.g2_neg(bn254.g2_frobenius(Q1))}


def slopes(Q: bn254.G2Point) -> list[tuple[bn254.Fp2, tuple[bn254.Fp2, bn254.Fp2]]]:
    """(lambda, (c3, c4)) of every step of the G2 point Q, as in bn254.multi_miller_loop_affine."""
    pts, T, out = step_points(Q), Q, []
    for kind in STEPS:
        Qk = pts[kind]
        lam = bn254.affine_double_slope(T) if Qk is None else bn254.affine_add_slope(T, Qk)
        T, coeffs = bn254.affine_step(T, lam, Qk)
        out.append((lam, coeffs))
    return out


def fixed_lines(Q: bn254.G2Point) -> list[tuple[bn254.Fp2, bn254.Fp2]]:
    """The line coefficients (c3, c4) = (-lambda, lambda xT - yT) of every step of a fixed point."""
    return [coeffs for _, coeffs in slopes(Q)]


# ---------------------------------------------------------------------------------------------------
# The relations, over a ring
class PolyRing:
    """Polynomials over F_p."""

    X = poly.X
    add, sub, mul = staticmethod(poly.add), staticmethod(poly.sub), staticmethod(poly.mul)
    k = staticmethod(poly.const)

    @staticmethod
    def even(a: Sequence[int]) -> poly.Poly:  # an element of F_p6: a polynomial in w^2, given by its 6 coefficients
        return poly.trim([x for c in a for x in (c, 0)])

    @staticmethod
    def conj_sub(x: poly.Poly, y: poly.Poly) -> poly.Poly:  # x - y, where y(w) = x(-w) (DegRing uses it)
        return poly.sub(x, y)


class NumRing:
    """F_p, the variable set to z."""

    def __init__(self, z: int) -> None:
        self.X = z % P

    add = staticmethod(lambda a, b: (a + b) % P)
    sub = staticmethod(lambda a, b: (a - b) % P)
    mul = staticmethod(lambda a, b: a * b % P)
    k = staticmethod(lambda c: c % P)
    conj_sub = staticmethod(lambda x, y: (x - y) % P)

    def even(self, a: Sequence[int]) -> int:
        return poly.evaluate(a, self.X * self.X % P)


NEG = -(10**9)  # the degree of 0


class DegRing:
    """Degrees, of the even and of the odd part of each value: the shape of S, hence the size of Q.  The
    parts matter because D is N with w -> -w (see relations), so in N (a - w) - D (a + w) the even part of
    N (a - w) cancels."""

    X = (NEG, 1)
    add = sub = staticmethod(lambda a, b: (max(a[0], b[0]), max(a[1], b[1])))
    mul = staticmethod(lambda a, b: (max(a[0] + b[0], a[1] + b[1]), max(a[0] + b[1], a[1] + b[0])))
    k = staticmethod(lambda c: (0, NEG))
    even = staticmethod(lambda a: (10, NEG))

    @staticmethod
    def conj_sub(
        x: tuple[int, int], y: tuple[int, int]
    ) -> tuple[int, int]:  # x - y for y(w) = x(-w): twice the odd part of x
        return (NEG, x[1])


def relations(
    R: Ring, v: dict[str, Any], lines: Sequence[tuple[bn254.Fp2, bn254.Fp2]], commit: Sequence[bool] | None = None
) -> list[Any]:
    """The relations R_k in order, over the ring R.  v: the values (Prover.witness(...)['values']); lines: fixed_lines of
    delta; commit: the steps whose Miller value is committed (COMMIT).  The values are u = E(f), kept as
    fractions N / D of polynomials; at a committed step u = (a + w) / (a - w), and N, D start again from
    a + w and a - w.  v['win'][i]: the compressed factors of the public inputs' term multiplied in at step
    i; v['tau']: the compressed constant of the end.

    A slope's relation and the two of the G2 check are even polynomials (in w^6), a committed value's and
    the last one are odd (`parities`): `combine` relies on it."""
    commit = COMMIT if commit is None else commit
    X = R.X
    X3 = R.mul(R.mul(X, X), X)
    X5 = R.mul(R.mul(X3, X), X)
    U = R.sub(R.mul(X3, X3), R.k(9))  # u = w^6 - 9

    def phi(a):  # an F_p2 element as a polynomial
        a = bn254._fp2(a)
        return R.add(R.k(a.c0), R.mul(R.k(a.c1), U))

    def odd(Pt, c3, c4):  # c3 xP w + c4 w^3: the line yP + c3 xP w + c4 w^3 without yP, its odd part
        return R.add(R.mul(R.mul(R.k(Pt[0]), X), c3), R.mul(X3, c4))

    xb, yb = v['B']
    ac = R.even(v['ac'])
    cp, cm = R.add(ac, X), R.sub(ac, X)  # c' = E(c) = cp / cm
    win = v.get('win', {})
    rels = []
    pts = step_points(v['B'])
    x, y, N, D = phi(xb), phi(yb), cm, cp  # u = E(c^-1) = cm / cp
    # D(w) = N(-w) throughout: true at the start, and kept by every factor g / h, for which h(w) = g(-w).
    # A window's factor has h(w) = -g(-w) instead, so a step with an odd number of windows multiplies N
    # and D by w as well.  Then N (a - w) - D (a + w) is twice the odd part of N (a - w); DegRing uses it
    for i, kind in enumerate(STEPS):
        lam = phi(v['lam'][i])
        if kind == 'D':
            rels.append(R.sub(R.mul(lam, y), R.mul(R.k(THREE_HALVES), R.mul(x, x))))
            x2 = R.sub(R.mul(lam, lam), R.mul(R.k(2), x))
            N, D = R.mul(N, N), R.mul(D, D)
        else:
            q = pts[kind]
            assert q is not None
            xq, yq = phi(q[0]), phi(q[1])
            rels.append(R.sub(R.mul(lam, R.sub(xq, x)), R.sub(yq, y)))
            x2 = R.sub(R.sub(R.mul(lam, lam), x), xq)
            if kind in ('A+', 'A-'):  # times E(c^-1) or E(c)
                N, D = (R.mul(N, cm), R.mul(D, cp)) if kind == 'A+' else (R.mul(N, cp), R.mul(D, cm))
        wins = win.get(i, ())
        for b1, b2 in wins:  # times (sigma + b2) / (sigma - b2), sigma = (kappa + b1^2) w + b1 b2 w^3 + b2^2 w^5
            B1, B2 = phi(b1), phi(b2)
            sig = R.add(
                R.add(R.mul(R.add(phi(KAPPA), R.mul(B1, B1)), X), R.mul(R.mul(B1, B2), X3)), R.mul(R.mul(B2, B2), X5)
            )
            N, D = R.mul(N, R.add(sig, B2)), R.mul(D, R.sub(sig, B2))
        if len(wins) % 2:  # times w / w
            N, D = R.mul(N, X), R.mul(D, X)
        m = R.sub(R.mul(lam, x), y)  # lambda x - y, the c4 of B's line
        ln = [
            (v['P'][1], odd(v['P'], R.sub(R.k(0), lam), m)),
            (v['C'][1], odd(v['C'], phi(lines[i][0]), phi(lines[i][1]))),
        ]
        lp = R.mul(R.add(R.k(ln[0][0]), ln[0][1]), R.add(R.k(ln[1][0]), ln[1][1]))
        lm = R.mul(R.sub(R.k(ln[0][0]), ln[0][1]), R.sub(R.k(ln[1][0]), ln[1][1]))
        N, D = R.mul(N, lm), R.mul(D, lp)  # E(l) = conj(l) / l, and conj(l)(w) = l(-w)
        if commit[i]:
            a = R.even(v['a'][i])
            rels.append(R.conj_sub(R.mul(N, R.sub(a, X)), R.mul(D, R.add(a, X))))
            N, D = R.add(a, X), R.sub(a, X)
        x, y = x2, R.sub(m, R.mul(lam, x2))
    rels.append(R.sub(x, phi(xb.conj() * bn254.FROB3[2])))
    rels.append(R.sub(y, phi(yb.conj() * -bn254.FROB3[3])))
    # u pi(c'^-1) pi^2(c') pi^3(c'^-1) = tau, with pi^n(c') = (a(t_n) + t_n) / (a(t_n) - t_n)
    t = [frob_w(R, n) for n in (1, 2, 3)]
    a = [frob_even(R, v['ac'], n) for n in (1, 2, 3)]
    at = R.even(v['tau'])
    num = R.mul(R.mul(R.mul(R.mul(N, R.sub(a[0], t[0])), R.add(a[1], t[1])), R.sub(a[2], t[2])), R.sub(at, X))
    den = R.mul(R.mul(R.mul(R.mul(D, R.add(a[0], t[0])), R.sub(a[1], t[1])), R.add(a[2], t[2])), R.add(at, X))
    rels.append(R.conj_sub(num, den))
    return rels


def frob_w(R: Ring, n: int) -> Any:
    """t_n = pi^n(w) (poly.FROB_W): odd, of degree 7, 1, 7."""
    t = None
    for k, g in poly.FROB_W[n]:
        xk = R.X
        for _ in range(k - 1):
            xk = R.mul(xk, R.X)
        t = R.mul(R.k(g), xk) if t is None else R.add(t, R.mul(R.k(g), xk))
    return t


def frob_even(R: Ring, a: Sequence[int], n: int) -> Any:
    """pi^n(a) for a in F_p6 given by its 6 coefficients, as a(t_n) = sum a_k t_n^2k: pi^n is a ring
    homomorphism fixing F_p, so a(t_n) = pi^n(a) modulo M.  It has degree 70 for n = 1, 3 and 10 for
    n = 2; the program evaluates it by Horner's rule in t_n(z)^2."""
    t = frob_w(R, n)
    t2 = R.mul(t, t)
    acc = R.k(a[-1])
    for c in reversed(a[:-1]):
        acc = R.add(R.mul(acc, t2), R.k(c))
    return acc


def parities(commit: Sequence[bool] | None = None) -> list[bool]:
    """For each relation in the order of `relations`, whether it is an odd polynomial: a committed value's
    and the last one are; a slope's and the two of the G2 check are even."""
    out: list[bool] = []
    for c in COMMIT if commit is None else commit:
        out += [False, True] if c else [False]
    return out + [False, False, True]


def combine(R: Ring, rels: Sequence[Any], r: int, commit: Sequence[bool] | None = None) -> Any:
    """S = S_o + r w S_e, the combination the program accumulates: S_o and S_e are the sums of the odd and
    of the even relations by Horner's rule in r^2.  The odd ones get the even powers of r and the even
    ones the odd powers, so every relation has a power of its own, and S is an odd polynomial."""
    r2 = R.k(r * r % P)
    acc = {False: R.k(0), True: R.k(0)}
    for rel, odd in zip(rels, parities(commit), strict=True):
        acc[odd] = R.add(R.mul(acc[odd], r2), rel)
    return R.add(acc[True], R.mul(R.mul(R.k(r), R.X), acc[False]))


def _degrees(commit: Sequence[bool], win: dict[int, int] | None = None) -> list[int]:
    """The degrees of the relations (DegRing reads only the structure); win: step -> number of factors."""
    z = bn254.Fp2(0)
    v = {
        'P': (0, 0),
        'B': bn254.G2_GEN,
        'C': (0, 0),
        'ac': [0] * 6,
        'lam': [z] * N_STEPS,
        'a': [[0] * 6] * N_STEPS,
        'tau': [0] * 6,
        'win': {i: [(bn254.Fp2(0), bn254.Fp2(0))] * k for i, k in (win or {}).items()},
    }
    return [max(d) for d in relations(DegRing, v, [(z, z)] * N_STEPS, commit)]


def _shape(commit: Sequence[bool], win: dict[int, int] | None = None) -> tuple[int, int]:
    """The number of relations and the degree of S (`combine` multiplies the even relations by w)."""
    rels = _degrees(commit, win)
    return len(rels), max(d + (not odd) for d, odd in zip(rels, parities(commit), strict=True))


def schedule(cap: int) -> list[bool]:
    """The steps whose Miller value is committed: every addition, and left to right, a doubling is skipped
    whenever S stays within the degree cap.  A committed value costs 6 words of witness, two degrees of S
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


# the degree of a committed relation that spans two uncommitted doublings and an addition (D D A); under
# this cap, 37 of the 88 Miller values are committed
DEG_CAP = 171
COMMIT = schedule(DEG_CAP)
N_RELS, DEG_S = _shape(COMMIT)  # 128 relations, degree 171


def q_words(deg: int) -> int:
    """The words of Q for S of degree deg.  S is odd and M even, so Q is odd: only its coefficients of odd
    degree, up to deg - 12, are written, (deg - 11) // 2 of them, read in chunks of 8 (QCHUNK)."""
    return -(-((deg - 11) // 2) // 8) * 8


# ---------------------------------------------------------------------------------------------------
# The public inputs' term.  e(L, gamma) = e(IC_0, gamma) prod_i e(IC_i, gamma)^(x_i): a product of
# constants of GT, selected by the bits of the inputs.  Each input is cut into windows of 8 bits (the top
# one, bits 248 .. 253, has 6: an input is below r < 2^254).  A window with digit d contributes a factor
# with E-image T_i^((d + 1) 2^lo), stored as its 4 words in T6 (compress6_all); the +1 keeps 1, which has
# no compressed form, out of the tables, and the end's constant takes the offset.  The top window of the
# first input is merged with that constant (a table of 64 taus); the others are multiplied in at addition
# steps, as many as each step's relation leaves room for under the degree cap.  A factor multiplied in
# before k more doublings is the 2^k-th root of what it must contribute, which exists: the factors lie in
# the group of order r.
#
# An input known to be shorter (the Groth16 verifier's bound signal, when it is a hash cut to fewer bits)
# has windows for its own bits only, the top one with what is left of them.  The program must then check
# that the input has no bit above: the tables do not read those.
W_BITS, INPUT_BITS = 8, 254


def input_bits(n: int | Sequence[int]) -> tuple[int, ...]:
    """The bit lengths of the inputs: of n whole inputs, or those given."""
    bits = (INPUT_BITS,) * n if isinstance(n, int) else tuple(n)
    ensure(all(1 <= b <= INPUT_BITS for b in bits), 'an input has 1 to 254 bits')
    return bits


def windows(n: int | Sequence[int]) -> list[Window]:
    """(input, lowest bit, width) of the windows of the inputs (their number, or their bit lengths), the
    top one of the first input first."""
    bits = input_bits(n)

    def top(i: int) -> Window:
        lo = (bits[i] - 1) // W_BITS * W_BITS
        return (i, lo, bits[i] - lo)

    out = [top(0)] if bits else []
    for i in range(len(bits)):
        out += [(i, lo, W_BITS) for lo in range(0, top(i)[1], W_BITS)] + ([top(i)] if i else [])
    return out


def add_capacities(cap: int) -> dict[int, int]:
    """step -> the number of window factors its committed relation takes within the degree cap (each factor
    adds 17 to the degree, and an odd number of them one more, for the w)."""
    j, rel = 0, {}
    for i, kind in enumerate(STEPS):
        j += 1  # its slope relation
        if COMMIT[i]:
            if kind != 'D':
                rel[i] = j
            j += 1
    room = {}
    for i, j in rel.items():
        k = 0
        while _degrees(COMMIT, {i: k + 1})[j] <= cap:
            k += 1
        room[i] = k
    return room


_PLANS: dict[tuple[int, ...], tuple[int, Window | None, dict[int, list[Window]]]] = {}


def window_plan(n: int | Sequence[int]) -> tuple[int, Window | None, dict[int, list[Window]]]:
    """(the degree of S, the window merged with the end's constant or None, step -> its windows) for n
    public inputs (or inputs of the bit lengths n): the steps with the most room first, so that few steps
    carry windows, under the cap DEG_S, or under a higher one if the windows need it (more inputs; Q grows
    with it)."""
    n = input_bits(n)
    if n not in _PLANS:
        wins = windows(n)
        top = wins[0] if n else None
        for cap in range(DEG_S, 4 * DEG_S):
            rest, plan = wins[1:], {}
            for s, k in sorted(add_capacities(cap).items(), key=lambda sk: (-sk[1], -sk[0])):
                if not rest:
                    break
                plan[s], rest = rest[:k], rest[k:]
            if not rest:
                break
        ensure(not rest, 'too many public inputs')
        _PLANS[n] = (_shape(COMMIT, {s: len(w) for s, w in plan.items()})[1], top, dict(sorted(plan.items())))
    return _PLANS[n]


def doublings_after(s: int) -> int:
    return sum(1 for kind in STEPS[s + 1 :] if kind == 'D')


# ---------------------------------------------------------------------------------------------------
# The transcript: r = SHA-256(inputs, points, a_c, leaves), z = SHA-256(r, Q'), all words big-endian
def wbytes(ws: Sequence[int]) -> bytes:
    return b''.join(w.to_bytes(32, 'big') for w in ws)


def blocks(n: int) -> list[int]:
    """The hashing blocks of n words: blocks of 16, then powers of two."""
    out = []
    for k in (16, 8, 4, 2, 1):
        while n >= k:
            out.append(k)
            n -= k
            if k < 16:
                break
    return out


def leaf_words(commit: bool) -> int:
    """lambda (2 words), a (6) if committed."""
    return 2 + 6 * commit


def miller_values(
    pairs: Sequence[tuple[bn254.G1Point, bn254.G2Point]],
    c: bn254.Fp12 | None = None,
    factors: dict[int, list[bn254.Fp12]] | None = None,
) -> list[bn254.Fp12]:
    """The Miller value after each step of the loop, as the relations have it: from f = c^-1, times c^-1 / c
    at the A+ / A- steps (from 1 and without them if c is None), times factors[i] at step i."""
    lines = [[bn254.affine_line(cf, Pt) for _, cf in slopes(Q)] for Pt, Q in pairs]
    f = bn254.Fp12.one() if c is None else c.inv()
    ci, out = f, []  # c^-1, if c is given
    for i, kind in enumerate(STEPS):
        if kind == 'D':
            f = f.square()
        elif c is not None:
            f = f * ci if kind == 'A+' else f * c if kind == 'A-' else f
        for g in (factors or {}).get(i, ()):
            f = f * g
        for k in range(2):
            f = f.mul_by_034(*lines[k][i])
        out.append(f)
    return out


def easy(f: bn254.Fp12) -> bn254.Fp12:
    """E(f) = f^(p^6 - 1) = conj(f) / f, in the torus T2: E(f) conj(E(f)) = 1."""
    return f.conj() * f.inv()


W_TOWER = bn254.Fp12(bn254.Fp6(0), bn254.Fp6(1))  # w


def batch_inv(xs: Sequence[bn254.Fp12]) -> list[bn254.Fp12]:
    """The inverses of the nonzero xs in F_p12, with one inversion (Montgomery's trick)."""
    pre = [bn254.Fp12.one()]
    for x in xs:
        pre.append(pre[-1] * x)
    inv, out = pre[-1].inv(), [bn254.Fp12.one()] * len(xs)
    for k in range(len(xs) - 1, -1, -1):
        out[k] = inv * pre[k]
        inv = inv * xs[k]
    return out


def compress(u: bn254.Fp12, inv: bn254.Fp12 | None = None) -> list[int]:
    """a in F_p6 with u = (a + w) / (a - w), for u != 1 in T2: a = w (u + 1) / (u - 1), as the 6
    coefficients of a polynomial in w^2.  inv: (u - 1)^-1 if known."""
    ensure(u != bn254.Fp12.one(), 'u = 1 has no compressed form')
    d = poly.from_tower(W_TOWER * (u + bn254.Fp12.one()) * (inv or (u - bn254.Fp12.one()).inv()))
    ensure(all(d[k] == 0 for k in range(1, 12, 2)), 'not in F_p6')
    return d[0::2]


def compress_all(us: Sequence[bn254.Fp12]) -> list[list[int]]:
    """compress of each, with one inversion."""
    one = bn254.Fp12.one()
    return [compress(u, inv) for u, inv in zip(us, batch_inv([u - one for u in us]))]


KAPPA = (bn254.Fp2(3) * bn254.XI).inv()


def compress6_all(us: Sequence[bn254.Fp12]) -> list[tuple[bn254.Fp2, bn254.Fp2]]:
    """(b1, b2) in F_p2 for each u != 1 of the cyclotomic subgroup T6 (which holds the group of order r):
    u = (s + 1) / (s - 1) with s = b0 w + b1 w^3 + b2 w^5 odd, and on T6, b0 b2 - b1^2 = kappa = 1 / (3 xi),
    so b0 follows from b1 and b2 (b2 != 0 but for about p^2 of the p^4 - p^2 + 1 elements).  4 words
    where the torus T2 takes 6.  One inversion for all."""
    one = bn254.Fp12.one()
    out = []
    for u, inv in zip(us, batch_inv([u - one for u in us])):
        sv = (u + one) * inv
        ensure(sv.c0 == bn254.Fp6(0), 'not in T2')
        b0, b1, b2 = sv.c1.c0, sv.c1.c1, sv.c1.c2
        ensure(b2 != bn254.Fp2(0) and b0 * b2 - b1 * b1 == KAPPA, 'not in T6, or b2 = 0')
        out.append((b1, b2))
    return out


def gt_constants(ic: Sequence[bn254.G1Point], gamma: bn254.G2Point) -> list[bn254.Fp12]:
    """K_i in F_p12 with K_i^h = e(IC_i, gamma), h = (p^12 - 1) / r: the pairing itself to the power
    h^-1 mod r, so in the group of order r.  The Miller loop of (L, gamma) is replaced by a product of
    their powers."""
    hinv = pow(bn254.H % bn254.R, -1, bn254.R)
    return [bn254.final_exponentiation(bn254.multi_miller_loop_affine([(pt, gamma)])) ** hinv for pt in ic]


class Prover:
    """The witness for the pairs (-A, B), (C, delta) and the public inputs' term: gt = gt_constants(ic,
    gamma) (K_0 .. K_n for n inputs); const is the Miller value of (alpha, beta).  The tables: for each
    window, the compressed E-images of its factors by digit, and the end's constants (tau) by the digit of
    the window merged with them.  bits: the bit lengths of the inputs, if some are shorter than a whole
    input."""

    def __init__(
        self, delta: bn254.G2Point, const: bn254.Fp12, gt: Sequence[bn254.Fp12], bits: Sequence[int] | None = None
    ) -> None:
        self.lines = fixed_lines(delta)
        self.const, self.gt, self.n = const, gt, len(gt) - 1
        self.bits = input_bits(self.n if bits is None else bits)
        ensure(len(self.bits) == self.n, 'a bit length for each public input')
        deg, self.top, self.plan = window_plan(self.bits)
        self.n_q = q_words(deg)
        offset = [sum(1 << lo for i2, lo, _ in windows(self.bits) if i2 == i) for i in range(self.n)]
        inv2 = pow(2, -1, bn254.R)
        # a window at step s: digit d multiplies in K_i^((d + 1) 2^lo / 2^k), k the doublings after s
        self.expo = {
            (s, win): (1 << win[1]) * pow(inv2, doublings_after(s), bn254.R) % bn254.R
            for s, wins in self.plan.items()
            for win in wins
        }
        self.tables: dict[tuple[int, Window], list[tuple[bn254.Fp2, bn254.Fp2]]] = {}
        for (s, (i, lo, width)), e in self.expo.items():
            base = gt[i + 1] ** e
            us, g = [], base
            for _ in range(1 << width):
                us.append(easy(g))
                g = g * base
            self.tables[(s, (i, lo, width))] = compress6_all(us)
        # the end: E(const K_0 prod_i K_i^-offset_i, times the top window's factor)^-1 by its digit
        rest = const * gt[0]
        for i in range(self.n):
            rest = rest * gt[i + 1] ** (-offset[i] % bn254.R)
        if self.top is None:
            self.tau_consts = [rest]
        else:
            i, lo, width = self.top
            base, g = gt[i + 1] ** (1 << lo), rest * gt[i + 1] ** (1 << lo)
            self.tau_consts = []
            for _ in range(1 << width):
                self.tau_consts.append(g)
                g = g * base
        self.taus = compress_all([easy(t).conj() for t in self.tau_consts])  # E(W27) = 1: no selector

    @staticmethod
    def digit(inputs: Sequence[int], win: Window) -> int:
        i, lo, width = win
        return (inputs[i] >> lo) & ((1 << width) - 1)

    def factors(self, inputs: Sequence[int]) -> dict[int, list[bn254.Fp12]]:
        """step -> the factors of F_p12 its windows multiply in, for these inputs."""
        return {
            s: [self.gt[win[0] + 1] ** ((self.digit(inputs, win) + 1) * self.expo[(s, win)] % bn254.R) for win in wins]
            for s, wins in self.plan.items()
        }

    def end_digit(self, inputs: Sequence[int]) -> int:
        """The digit that selects the end's constant."""
        return 0 if self.top is None else self.digit(inputs, self.top)

    def product(self, pairs: Sequence[tuple[bn254.G1Point, bn254.G2Point]], inputs: Sequence[int]) -> bn254.Fp12:
        """The Miller value of everything: the pairs, the inputs' term and (alpha, beta).  Its h-th power is 1
        iff the pairing check holds."""
        return miller_values(pairs, factors=self.factors(inputs))[-1] * self.tau_consts[self.end_digit(inputs)]

    def witness(
        self,
        pairs: Sequence[tuple[bn254.G1Point, bn254.G2Point]],
        inputs: Sequence[int],
        residue: tuple[bn254.Fp12, int] | None = None,
        check: bool = True,
    ) -> dict[str, Any] | None:
        """The witness, or None if the product of the pairings is not 1.  Tests may give the residue
        witness (c, s) and seal without checking the relations (seal).  The relations hold for
        E(c) and E(f), so s is not needed."""
        (nA, B), (C, _) = pairs
        ensure(len(inputs) == self.n and all(0 <= x < bn254.R for x in inputs), 'public inputs')
        ensure(all(x >> b == 0 for x, b in zip(inputs, self.bits)), 'a public input is longer than its bits')
        res = residue or bn254.residue_witness(self.product(pairs, inputs))
        if res is None:
            return None
        c, _ = res
        a = [
            compress(easy(f)) if COMMIT[i] else None
            for i, f in enumerate(miller_values(pairs, c, self.factors(inputs)))
        ]
        win = {s: [self.tables[(s, w)][self.digit(inputs, w)] for w in wins] for s, wins in self.plan.items()}
        v = {
            'P': nA,
            'B': B,
            'C': C,
            'ac': compress(easy(c)),
            'lam': [lam for lam, _ in slopes(B)],
            'a': a,
            'win': win,
            'tau': self.taus[self.end_digit(inputs)],
        }
        return self.seal(v, inputs, check)

    def seal(self, v: dict[str, Any], inputs: Sequence[int], check: bool = True) -> dict[str, Any]:
        """The witness words of the values v: the committed words, then r, Q (its coefficients of odd
        degree) and z.  check=False lets a test seal values whose relations do not hold (Q is then S / M
        without its remainder)."""
        mont = lambda xs: [to_mont(x % P) for x in xs]
        fp2 = lambda a: mont([a.c0, a.c1])
        nA, B, C = v['P'], v['B'], v['C']
        w: dict[str, Any] = {
            'points': mont([nA[0], nA[1], B[0].c0, B[0].c1, B[1].c0, B[1].c1, C[0], C[1]]),
            'ac': mont(v['ac']),
            'leaves': [fp2(v['lam'][i]) + (mont(v['a'][i]) if COMMIT[i] else []) for i in range(N_STEPS)],
        }
        t = wbytes(inputs) + wbytes(w['points']) + wbytes(w['ac']) + b''.join(map(wbytes, w['leaves']))
        w['r'] = int.from_bytes(hashlib.sha256(t).digest(), 'big')
        q, rem = poly.divmod_m(combine(PolyRing, relations(PolyRing, v, self.lines), from_mont(w['r'])))
        ensure(not check or rem == [0] * 12, 'the relations do not hold')
        ensure(not any(q[0::2]), 'Q is not odd')
        q = q[1::2]  # Q = w Q'(w^2): the coefficients of Q'
        ensure(len(q) <= self.n_q, 'Q is longer than its words')
        w['q'] = mont(q + [0] * (self.n_q - len(q)))
        w['z'] = int.from_bytes(hashlib.sha256(wbytes([w['r']] + w['q'])).digest(), 'big')
        w['values'] = v
        return w


# ---------------------------------------------------------------------------------------------------
# The program
#
# The loop state is ((((N, D, se, x, y), so), h), run): N / D = u at z, se and so the Horner sums in r^2
# of the even and of the odd relations so far (`combine`), (x, y) = B's point at z, h the SHA-256 context
# of the transcript, and the run values, computed once in the setup from z, r and the points.  zeta =
# z^6 - 9 is the tower's u (u^2 = -1) at z; X, Y are the x, y of a point at zeta.
#
# run = (RUN_STEP, the rest).  A step function gets RUN_STEP only, and the loop passes the rest around it.
# RUN_STEP is two subtrees: RUN_ANY, which every step reads, and RUN_COMMIT, which only a committed step
# reads (the powers of z for a(z)), so a step without a commitment gets RUN_ANY alone; so, which only a
# committed step changes, is passed around it as well.  The rest (PairingCheck.run_rest) is RUN_FIELD,
# for the additions' arguments, then the public inputs whose windows are multiplied in at addition steps
# ('in0', ...: words, not field elements).
RUN_ANY = ['z3', 'zeta', 'z3zeta', 'nxpz', 'yp', 'xcz', 'xczz', 'yc', 'r2']
RUN_COMMIT = ['z1', 'z2', 'z4', 'z6', 'z8', 'z10']
RUN_STEP = RUN_ANY + RUN_COMMIT
RUN_FIELD = ['cp', 'cm', 'XB', 'YB', 'X1', 'Y1']
# computed in the setup, used at the end only, so they are not carried through the loop: the last
# relation is N pn + D npd; r^4 and z r close the two sums; z^12, z^14 and z^16 are read by Q(z)
END = ['pn', 'npd', 'r4', 'zr', 'z12', 'z14', 'z16']
# (xQ, yQ, gN, gD): u times E(c^-1) = cm / cp at A+, E(c) = cp / cm at A-, 1 at the Frobenius additions.
# -B = (XB, -YB), and -pi^2(B) = (omega XB, YB) for the cube root of unity omega = FROB2[2]: these two
# are computed where they are used, from the run values (DERIVED: run value, constant factor).
Q_KEYS = {
    'A+': ('XB', 'YB', 'cm', 'cp'),
    'A-': ('XB', 'nYB', 'cp', 'cm'),
    'F1': ('X1', 'Y1', None, None),
    'F2': ('X2', 'YB', None, None),
}
DERIVED = {'nYB': ('YB', -1), 'X2': ('XB', bn254.FROB2[2].c0)}
CORE = ('N', 'D', 'se', 'x', 'y')  # what every step changes
STATE = (*CORE, 'so')


class PairingCheck:
    """Generator of the check over a backend.  delta: the fixed G2 point; const: the Miller value of
    (alpha, beta); gt: gt_constants of the IC points and gamma; b: the bounds of the loop state
    (bounds()); bits: the bit lengths of the inputs, if some are shorter than a whole input.  The tables
    do not read an input above its length, so the caller must check that it has no bit there."""

    def __init__(
        self,
        fp: Fp,
        delta: bn254.G2Point,
        const: bn254.Fp12,
        gt: Sequence[bn254.Fp12],
        b: dict[str, int] | None = None,
        bits: Sequence[int] | None = None,
    ) -> None:
        ensure(additions_avoid_q(STEPS), 'an addition of the loop can meet T = Q')
        self.fp, self.be, self.cv = fp, fp.be, Curve(fp)
        self.prover = pr = Prover(delta, const, gt, bits)
        # per step, the line constants of delta: c3 and c4, two Montgomery words each
        self.data = [[to_mont(a % P) for cf in pr.lines[i] for a in (cf.c0, cf.c1)] for i in range(N_STEPS)]
        mont6 = lambda a: [[to_mont(x) for x in a[:4]], [to_mont(x) for x in a[4:]]]
        mont4 = lambda b: [[to_mont(x) for x in (b[0].c0, b[0].c1, b[1].c0, b[1].c1)]]  # one wide constant
        self.win_tables = {key: [mont4(b) for b in tab] for key, tab in pr.tables.items()}
        self.tau_table = [mont6(a) for a in pr.taus]
        self.ins = sorted({i for wins in pr.plan.values() for i, _, _ in wins})  # inputs read in the loop
        self.run_rest = RUN_FIELD + [f'in{i}' for i in self.ins]
        self.run = RUN_STEP + self.run_rest
        self.b = dict(b) if b is not None else {}
        if not self.b:
            ensure(not is_sym(self.be), 'the bounds are computed with the numeric backend')
            self.sample_bounds()
        be = self.be
        self.TOP2 = be.function('TOP2', [words(4), words(2)], lambda a: be.checks([self.top2_zero(w) for w in flat(a)]))
        self.steps: dict[tuple[str, bool], Any] = {}
        for kind, args in (('D', None), ('A', words(4)), ('F', words(4))):
            for commit in sorted({COMMIT[k] for k in range(N_STEPS) if self.fn_of(k)[0] == kind}):
                st = self.state_shape(run_rest=False, commit=commit)
                shape = [[st, leaf_shape(commit)], words(4) if args is None else [args, words(4)]]
                name = f'STEP_{kind}' + ('' if commit else '_')
                self.steps[(kind, commit)] = be.function(name, shape, self.step_body(kind, commit))
        self.QCHUNK = be.function('QCHUNK', [[words(2), words(7)], words(8)], self.qchunk_body)
        # the step functions and QCHUNK take the loop state within these bounds and must give it back within
        # them (sample_bounds found them so; a stale or hand-made bounds dict must not slip through)
        for nm in (*STATE, 'qz'):
            ensure(self.b.get(nm + '_out', 0) <= self.b[nm], f'the loop state {nm} exceeds its bound')
        self.EVAL = be.function('EVAL', [[words(4), words(2)], E('', 256, 0)], self.eval_body)
        self.T6 = be.function('T6', [words(4), words(4)], self.t6_body) if pr.plan else None
        if is_sym(be):
            self.costs = {
                fn.t: fn.c
                for fn in list(self.steps.values()) + [self.QCHUNK, self.EVAL] + ([self.T6] if self.T6 else [])
            }

    @staticmethod
    def fn_of(k: int) -> tuple[str, bool]:
        """(function kind, commit) of step k.  A Frobenius addition with a committed value runs the addition's
        function with g = 1, which saves a function."""
        kind = STEPS[k][0]
        return ('A' if kind == 'F' and COMMIT[k] else kind), COMMIT[k]

    def one(self) -> Val:
        return self.fp.const(1)

    def m1(self) -> Val:
        return self.fp.const(P - 1)

    def rd(self, pairs: Sequence[tuple[Val, Val]]) -> Val:
        return self.fp.reduce_dot(pairs)

    def rd_plus(self, pairs: Sequence[tuple[Val, Val]], v: Val) -> Val:
        """rd(pairs) + v: a term v 1 is added after the reduction, which saves its two products."""
        return self.fp.add(self.rd(pairs), v)

    # hashing and the committed words
    def top2_zero(self, w: Term) -> Term:
        """The word is below 2^254: its two top bits are 0.  Committed words are multiplied in long dot
        products, whose CRT bound a full 256-bit word would exceed."""
        be = self.be
        if not is_sym(be):
            ensure(w >> 254 == 0, 'committed word above 2^254')
            return 0
        return be.verify(be.not1(be.jet('or_1', be.sub(w, 'OOOOOOO', 2), 1)))

    def top2_6(self, ws: Any) -> Term:
        """top2_zero of 6 projected words (4 + 2), by TOP2."""
        be = self.be
        if not is_sym(be):
            for w in flat(ws):
                self.top2_zero(w)
            return 0
        return be.call(self.TOP2, [be.subtree(ws)])

    def sha_init(self) -> Any:
        be = self.be
        return be.jet('sha_256_ctx_8_init', be.unit(), SHA_CTX_W) if is_sym(be) else b''

    def sha_add(self, h: Any, parts: Sequence[Any]) -> Any:
        """Absorb projections of 1, 2, 4, 8 or 16 words."""
        be = self.be
        if not is_sym(be):
            return h + b''.join(wbytes(flat(x)) for x in parts)
        for x in parts:
            x = be.subtree(x) if isinstance(x, list) else x
            h = be.jet(f'sha_256_ctx_8_add_{x.w // 8}', be.pair(h, x), SHA_CTX_W)
        return h

    def sha_final(self, h: Any) -> Term:
        be = self.be
        return (
            be.jet('sha_256_ctx_8_finalize', h, 256)
            if is_sym(be)
            else int.from_bytes(hashlib.sha256(h).digest(), 'big')
        )

    # one step
    @staticmethod
    def run_shape(commit: bool = True) -> Shape:
        """The shape of RUN_STEP, or of RUN_ANY alone."""
        return [words(len(RUN_ANY)), words(len(RUN_COMMIT))] if commit else words(len(RUN_ANY))

    @staticmethod
    def core_shape(commit: bool = True) -> Shape:
        """((N, D, se, x, y), so), or (N, D, se, x, y) alone."""
        return [words(len(CORE)), E('', 256, 0)] if commit else words(len(CORE))

    def state_shape(self, run_rest: bool = True, commit: bool = True) -> Shape:
        """(((N, D, se, x, y), so), h), (the run values); a step function's state is ((N, D, se, x, y), so)
        and RUN_STEP, or (N, D, se, x, y) and RUN_ANY if the step commits nothing."""
        if run_rest:
            return [[self.core_shape(), E('', SHA_CTX_W, 0)], [self.run_shape(), words(len(self.run_rest))]]
        return [self.core_shape(commit), self.run_shape(commit)]  # the step function: h is updated around it

    def step_body(self, kind: str, commit: bool) -> Any:
        """Body of a step function: (((state, RUN_STEP values), leaf), args) -> state, the state being
        ((N, D, se, x, y), so), or without so if the step commits nothing.  Evaluates lambda and the lines
        at z and -z, the next N and D, and a committed value at z, and adds the slope's relation to se and
        a committed value's to so, as `combine` does.  The loop absorbs the leaf into h."""
        fp, be, b = self.fp, self.be, self.b
        rd, one, m1 = self.rd, self.one, self.m1
        add = kind != 'D'

        def body(accs):
            (st, leaf), args = accs
            run = st[1]
            aw = flat(leaf[1]) if commit else []
            data = args if kind == 'D' else args[1]
            run = dict(zip(RUN_STEP if commit else RUN_ANY, flat(run)))
            c: dict[str, Any] = {
                nm: Val(w, b[nm]) for nm, w in zip(STATE if commit else CORE, flat(st[0]), strict=True)
            }
            c['l'] = [Val(w, WORD_MAX) for w in leaf[0]]
            c['dd'] = [Val(w, P - 1) for w in data]
            if commit:
                c['a'] = [Val(w, F_HI) for w in aw]
                c['zp'] = [Val(run[f'z{k}'], KB) for k in (1, 2, 4, 6, 8, 10)]
            for nm in RUN_ANY:
                c[nm] = Val(run[nm], KB)
            if add:
                c['xq'], c['yq'], c['gn'], c['gd'] = (Val(w, KB) for w in args[0])
            at_zeta = lambda c, a: rd([(a[1], c['zeta']), (a[0], one())])  # a0 + a1 zeta

            def first(c):
                out = [at_zeta(c, c['l'])]
                if commit:  # a(z) = sum a_k z^2k
                    a, zp = c['a'], c['zp']
                    out.append(rd([(a[0], one())] + [(a[k], zp[k]) for k in range(1, 6)]))
                return out + ([fp.sub(c['xq'], c['x'])] if add else [])

            minus_x3 = (lambda c: [(c['x'], m1()), (c['xq'], m1())]) if add else (lambda c: [(c['x'], fp.const(P - 2))])
            steps = [
                ('push', ['lam'] + (['az'] if commit else []) + (['dx'] if add else []), first),
                ('drop', ['l'] + (['a'] if commit else [])),
                (
                    'push',
                    ['x2', 'm'] + (['azp', 'azm'] if commit else []),
                    lambda c: (
                        [rd([(c['lam'], c['lam'])] + minus_x3(c)), rd([(c['lam'], c['x']), (c['y'], m1())])]
                        + (
                            [fp.normalize(fp.add(c['az'], c['zp'][0])), fp.normalize(fp.sub(c['az'], c['zp'][0]))]
                            if commit
                            else []
                        )
                    ),
                ),
                # the odd parts of the lines; a line at z is yP + o, at -z (its conjugate) yP - o
                (
                    'push',
                    ['oB', 'od'],
                    lambda c: [
                        rd([(c['nxpz'], c['lam']), (c['z3'], c['m'])]),
                        rd(
                            [
                                (c['xcz'], c['dd'][0]),
                                (c['xczz'], c['dd'][1]),
                                (c['z3'], c['dd'][2]),
                                (c['z3zeta'], c['dd'][3]),
                            ]
                        ),
                    ],
                ),
            ]

            def final(c, _):
                lam, m, x2 = c['lam'], c['m'], c['x2']
                y2 = rd([(m, one()), (lam, fp.neg(x2))])
                odd = [c['oB'], c['od']]
                ys = [c['yp'], c['yc']]
                lp = [fp.add(yv, o) for yv, o in zip(ys, odd)]
                lm = [fp.sub(yv, o) for yv, o in zip(ys, odd)]
                Lp, Lm = rd([(lp[0], lp[1])]), rd([(lm[0], lm[1])])
                if kind == 'D':
                    N2, D2 = rd([(c['N'], c['N'])]), rd([(c['D'], c['D'])])
                    slope = [(lam, c['y']), (c['x'], fp.mul_const(c['x'], -THREE_HALVES))]  # as a dot product
                else:
                    N2, D2 = rd([(c['N'], c['gn'])]), rd([(c['D'], c['gd'])])
                    slope = [(lam, c['dx']), (c['yq'], m1()), (c['y'], one())]
                Nn, Dn = rd([(N2, Lm)]), rd([(D2, Lp)])
                # Horner in r^2, each sum on its own: the slope's relation joins its sum unreduced
                se2 = rd([(c['se'], c['r2'])] + slope)
                if commit:  # N (a - z) - D (a + z), then N, D = a + z, a - z
                    so2 = rd([(c['so'], c['r2']), (Nn, c['azm']), (Dn, fp.neg(c['azp']))])
                    outs = [c['azp'], c['azm'], se2, x2, y2, so2]
                else:
                    outs = [Nn, Dn, se2, x2, y2]
                for nm, v in zip(STATE, outs):
                    b[nm + '_out'] = max(b.get(nm + '_out', 0), v.hi)
                return fp.pack([outs[:-1], outs[-1]] if commit else outs)

            new = chain(fp, c, steps, final)
            return be.seq(self.top2_6(leaf[1]), new) if commit else new

        return body

    def qchunk_body(self, accs: Any) -> Term:
        """Body of QCHUNK: ((qz, z^16), (z^2, z^4 .. z^14)), 8 words of Q -> qz z^16 + their polynomial at
        z^2.  Q(z) = z Q'(z^2), and Q'(z^2) is this step from the top chunk down; the words are checked
        below 2^254."""
        ((qz, z16), zp), q = accs
        one, b = self.one(), self.b
        out = self.rd(
            [(Val(qz, b['qz']), Val(z16, KB)), (Val(q[0], F_HI), one)]
            + [(Val(q[k], F_HI), Val(zp[k - 1], KB)) for k in range(1, 8)]
        )
        b['qz_out'] = max(b.get('qz_out', 0), out.hi)
        return self.be.seq(self.be.checks([self.top2_zero(w) for w in q]), out.e)

    def eval_body(self, accs: Any) -> Term:
        """Body of EVAL: ((a_0 .. a_3, a_4 a_5), t^2) -> a(t) = sum a_k t^2k by Horner, for an element a of F_p6
        (words below 2^254: committed words, or constants) and t^2 below KB."""
        a, t2 = accs
        a = flat(a)
        t2 = Val(t2, KB)
        acc = Val(a[5], F_HI)
        for k in range(4, -1, -1):
            # the inner terms join after the reduction; the last one inside it, so that a(t) is reduced
            acc = (
                self.rd([(acc, t2), (Val(a[k], F_HI), self.one())])
                if k == 0
                else self.rd_plus([(acc, t2)], Val(a[k], F_HI))
            )
        self.eval_hi = acc.hi
        return acc.e

    def eval_at(self, coeffs: Any, t2: Val) -> Val:
        """a(t) for the 6 words of a (projected, one subtree, 4 + 2 words; or a constant) and t^2, by EVAL."""
        t2 = t2 if t2.hi <= KB else self.fp.normalize(t2)
        be = self.be
        a: Any
        if not is_sym(be):
            a = [[x.e if isinstance(x, Val) else x for x in g] for g in coeffs]
        elif isinstance(coeffs, E):
            a = coeffs
        else:
            a = be.subtree([v.e for v in flat(coeffs)])
        return Val(be.call(self.EVAL, [a, t2.e]), self.eval_hi)

    def sample_bounds(self) -> None:
        """The bounds of the loop state: a fixed point of the step bodies, found on the numeric backend by
        widening the inputs (1% slack) until the outputs fit."""
        b = self.b
        names = (*STATE, 'qz')
        b.update(dict.fromkeys(names, KB))
        core, run = [0] * len(CORE), [0] * len(RUN_STEP)  # a step without a commitment reads the first len(RUN_ANY)
        for _ in range(30):
            for nm in names:
                b[nm + '_out'] = 0
            for kind, n_args in (('D', 0), ('A', 4)):
                for commit in (False, True):
                    st = [[core, 0] if commit else core, run]
                    leaf = [[0, 0]] + ([[[0] * 4, [0] * 2]] if commit else [])
                    self.step_body(kind, commit)([[st, leaf], [[0] * n_args, [0] * 4] if n_args else [0] * 4])
            self.qchunk_body([[[0, 0], [0] * 7], [0] * 8])
            if all(b[nm + '_out'] <= b[nm] for nm in names):
                return
            for nm in names:
                b[nm] = max(b[nm], b[nm + '_out'] * 101 // 100)
        raise RuntimeError('no fixed point for the loop bounds')

    # the loop
    def step_value(self, k: int, st: Any, leaf: Any, data: Any = None) -> Any:
        """The state after step k: the step function on the state without self.run_rest (and without so, if
        the step commits nothing), which are put back.  data: the step's line constants of delta, if they
        are given (an accessor), else constants here."""
        be = self.be
        kind = STEPS[k]
        if data is None:
            data = be.words_const(self.data[k]) if is_sym(be) else self.data[k]
        fn = self.steps[self.fn_of(k)]
        sub = be.subtree if is_sym(be) else (lambda v: v)
        (core, so), h = st[0]
        env = [[sub([core, so] if COMMIT[k] else core), sub(st[1][0] if COMMIT[k] else st[1][0][0])], leaf]
        if kind == 'D':
            out = be.call(fn, [env, data])
        else:
            run = dict(zip(self.run, flat(st[1])))

            def arg(nm):
                if nm is None:
                    return self.one().e
                if nm in DERIVED:
                    src, factor = DERIVED[nm]
                    v = self.fp.mul_const(Val(run[src], KB), factor)
                    ensure(v.hi <= KB, f'run value bound: {nm}')
                    return v.e
                return sub(run[nm])

            q = [arg(nm) for nm in Q_KEYS[kind][:2]]
            if k in self.prover.plan:  # g_N, g_D times the factors of the step's windows
                g = self.win_factors(k, run, Q_KEYS[kind][2:])
                q = [q, g] if is_sym(be) else q + g
            else:
                q += [arg(nm) for nm in Q_KEYS[kind][2:]]
            out = be.call(fn, [env, [q, data]])
        # the transcript absorbs the leaf: lambda, and a if committed
        lf = be.split(leaf, leaf_shape(COMMIT[k])) if is_sym(be) else leaf
        h2 = self.sha_add(h, [lf[0]] + ([lf[1][0], lf[1][1]] if COMMIT[k] else []))
        if not COMMIT[k]:
            out = [out, so]
        return be.pack([[out, h2], sub(st[1])]) if is_sym(be) else [[out, h2], st[1]]

    def prod(self, vs: Sequence[Val]) -> Val:
        """The product of the values, as a balanced tree of products.  A product of two values reduced from
        large bounds has a bound about as large, so with many factors (a step with ten windows, from three
        public inputs) a product would exceed the CRT bound: then its larger operand is normalised first."""

        def mul(a: Val, b: Val) -> Val:
            if a.hi * b.hi >= CRT_MAX:
                a, b = (self.fp.normalize(a), b) if a.hi >= b.hi else (a, self.fp.normalize(b))
            return self.rd([(a, b)])

        while len(vs) > 1:
            vs = [mul(vs[k], vs[k + 1]) if k + 1 < len(vs) else vs[k] for k in range(0, len(vs), 2)]
        return vs[0]

    def t6_body(self, accs: Any) -> Term:
        """Body of T6: ((b1, b2 as 4 words), (z, z^2, zeta, K)) -> (sigma + B2, sigma - B2) at z, for the
        window factor (sigma + b2) / (sigma - b2), sigma = (kappa + b1^2) w + b1 b2 w^3 + b2^2 w^5: B1, B2
        are b1, b2 at zeta, K is kappa at zeta, and sigma(z) = z (K + B1^2 + z^2 B2 (B1 + z^2 B2))."""
        fp, rd = self.fp, self.rd
        bw, (z, z2, zeta, k) = accs
        c = {
            'b': [Val(w, P - 1) for w in bw],
            'z': Val(z, KB),
            'z2': Val(z2, KB),
            'zeta': Val(zeta, KB),
            'K': Val(k, KB),
        }
        steps = [
            (
                'push',
                ['B1', 'B2'],
                lambda c: [
                    self.rd_plus([(c['b'][1], c['zeta'])], c['b'][0]),
                    rd([(c['b'][3], c['zeta']), (c['b'][2], self.one())]),
                ],
            ),  # reduced: sigma - B2 is multiplied
            ('push', ['T'], lambda c: [rd([(c['z2'], c['B2'])])]),  # read twice below
            (
                'push',
                ['S'],
                lambda c: [
                    rd(
                        [
                            (c['K'], c['z']),
                            (rd([(c['B1'], c['B1'])]), c['z']),
                            (rd([(c['T'], fp.add(c['B1'], c['T']))]), c['z']),
                        ]
                    )
                ],
            ),
        ]

        def final(c, _):
            out = [fp.add(c['S'], c['B2']), fp.sub(c['S'], c['B2'])]
            self.t6_hi = [v.hi for v in out]
            return fp.pack(out)

        return chain(fp, c, steps, final)

    def win_factors(self, s: int, run: dict[str, Term], base: Sequence[str | None]) -> Term:
        """(g_N, g_D) at addition step s: base (the names of E(c^-1) or E(c) at z as numerator and
        denominator, or None) times prod (sigma + B2) and prod (sigma - B2) over the step's windows (T6), each
        with the (b1, b2) its digit selects from its table, and both times z if the windows are odd in
        number (relations).  Computed in an environment of its own: the inputs, z, z^2, zeta, the base."""
        fp, be = self.fp, self.be
        wins = self.prover.plan[s]
        vals = [
            [Val(run[f'in{i}'], WORD_MAX) for i in self.ins],
            Val(run['z1'], KB),
            Val(run['z2'], KB),
            Val(run['zeta'], KB),
        ]
        g = [nm for nm in base if nm is not None]
        if g:
            vals.append([Val(run[nm], KB) for nm in g])
        sel = lambda c, i, lo, width: self.cv.select_const(
            c['in'][self.ins.index(i)], lo, width, self.win_tables[(s, (i, lo, width))]
        )

        def t6(c, win):
            b = sel(c, *win)
            b = b if is_sym(be) else b[0]
            return be.call(self.T6, [b, [c['z'].e, c['z2'].e, c['zeta'].e, c['K'].e]])

        def half(v, k):  # sigma +- B2 of one window
            return Val(be.sub(v.e, 'OI'[k], 256) if is_sym(be) else v.e[k], self.t6_hi[k])

        def body(acc):
            c = {'in': acc[0], 'z': acc[1], 'z2': acc[2], 'zeta': acc[3], 'b': acc[4] if len(acc) > 4 else None}
            k = fp.lin_const([(self.one(), KAPPA.c0), (c['zeta'], KAPPA.c1)])
            ensure(k.hi <= KB, 'kappa at zeta')
            steps = [('push', ['K'], lambda c: [k]), ('push', ['g'], lambda c: [[Val(t6(c, win), 0) for win in wins]])]

            def final(c, _):
                zw = [c['z']] * (len(wins) % 2)
                gN = self.prod([half(g, 0) for g in c['g']] + zw + ([c['b'][0]] if c['b'] else []))
                gD = self.prod([half(g, 1) for g in c['g']] + zw + ([c['b'][1]] if c['b'] else []))
                gN, gD = (v if v.hi <= KB else fp.normalize(v) for v in (gN, gD))
                ensure(gN.hi <= KB and gD.hi <= KB, 'window factor bound')
                return fp.pack([gN, gD])

            return chain(fp, c, steps, final)

        return fp.scope(vals, body)

    def loop(self, state0: Any, leaves: Any) -> Any:
        """The state after the 88 steps.  Sym: each step reads its leaf from a witness node of its own
        (LEAF_NAMES), so the leaves are not carried along: step k runs on (state, leaf k)."""
        be = self.be
        if not is_sym(be):
            for k, leaf in enumerate(leaves):
                state0 = self.step_value(k, state0, leaf)
            return state0
        shape = self.state_shape()
        state_w = sum(e.w for e in flat(shape))
        e = state0
        bodies: dict[tuple[str, bool], E] = {}
        for k, kind in enumerate(STEPS):
            w = 256 * leaf_words(COMMIT[k])
            leaf = be.witness(LEAF_NAMES[k], leaf_type(COMMIT[k]), w)
            if k in self.prover.plan:  # a step with windows: its own code
                be._push_env(state_w + w)
                try:
                    body = self.step_value(k, be._unpack('O', shape), be.proj('IH', w))
                finally:
                    be._pop_env()
                e = be.comp(be.pair(e, leaf), body)
            else:  # the code of all steps of a kind, on ((state, leaf), the step's line constants)
                key = (kind, COMMIT[k])
                if key not in bodies:
                    be._push_env(state_w + w + 1024)
                    try:
                        bodies[key] = be.share(
                            self.step_value(k, be._unpack('OO', shape), be.proj('OIH', w), be.proj('IH', 1024))
                        )
                    finally:
                        be._pop_env()
                e = be.comp(be.pair(be.pair(e, leaf), be.words_const(self.data[k])), bodies[key])
            e = be.share(e)  # one line of the program text per step
        return e

    # before the loop
    def setup(self, inputs: dict[str, Any], pts: Any, ac: Any, rz: Any) -> Term:
        """(((N, D, se, x, y), so), h, run) and the END values.  Checks A, B, C on their curves and the words of
        a_c, computes the run values, starts u = E(c^-1) as N / D = (a_c(z) - z) / (a_c(z) + z), and starts
        h with the public inputs, the points and a_c."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, lc = self.rd, self.one, fp.lin_const
        z = lambda k: 'z' if k == 1 else f'z{k}'
        raw = lambda w: Val(w, WORD_MAX)
        ctx = {
            'raw': [raw(rz[1]), raw(rz[0]), [raw(w) for w in flat(pts)]],
            'ac': [[Val(w, F_HI) for w in g] for g in ac],
        }
        if inputs['x']:
            ctx['in'] = [raw(x.e if isinstance(x, Val) else x) for x in inputs['x']]

        def tau(c):
            """The end's constant, selected by the digit of the window merged with it."""
            top = self.prover.top
            if top is None:
                return be.consts(256, self.tau_table[0]) if is_sym(be) else self.tau_table[0]
            return self.cv.select_const(c['in'][top[0]], top[1], top[2], self.tau_table)

        def at_zeta_conj(c, a0, a1, g):
            """conj(a) g at zeta: a0 (g0 + g1 zeta) + a1 (g1 - g0 zeta)"""
            return rd([(a0, lc([(one(), g.c0), (c['zeta'], g.c1)])), (a1, lc([(one(), g.c1), (c['zeta'], -g.c0)]))])

        t_at = lambda n, c: lc([(c[z(k)], g) for k, g in poly.FROB_W[n]])  # t_n(z)
        sq = lambda a: lambda c: rd([(c[a], c[a])])
        mu = lambda a, b: lambda c: rd([(c[a], c[b])])
        layer = lambda fs: lambda c: [f(c) for _, f in fs]  # the values of one layer
        layers = [
            [('z2', sq('z'))],
            [('z3', mu('z2', 'z')), ('z4', sq('z2'))],
            [('z6', sq('z3')), ('z7', mu('z4', 'z3')), ('z8', sq('z4'))],
            [('z10', mu('z4', 'z6')), ('z12', sq('z6')), ('z14', mu('z6', 'z8')), ('z16', sq('z8'))],
        ]
        # The first layer normalises the inputs into a fresh environment, which the on-curve checks then read;
        # every later layer pushes its values in front of it, so a_c and the points are not copied along.
        norm = lambda c: [fp.normalize(c['raw'][0]), fp.normalize(c['raw'][1]), [fp.normalize(v) for v in c['raw'][2]]]
        on_curve = lambda c: [
            Val(e, 0)
            for e in (
                cv.g1_on_curve_check(c['p'][0], c['p'][1]),
                cv.g2_on_curve_check((c['p'][2], c['p'][3]), (c['p'][4], c['p'][5])),
                cv.g1_on_curve_check(c['p'][6], c['p'][7]),
            )
        ]
        steps = (
            [('let', ['z', 'r', 'p'], norm, ['raw']), ('check', on_curve)]
            + [('push', [n for n, _ in L], layer(L)) for L in layers]
            + [
                (
                    'push',
                    ['zeta', 'nz', 't1', 't2'],
                    lambda c: [lc([(c['z6'], 1), (one(), -9)]), fp.mul_const(c['z'], -1), t_at(1, c), t_at(2, c)],
                ),
                (
                    'push',
                    ['acz', 'r2', 't3', 't1s', 't2s'],
                    lambda c: [
                        self.eval_at(c['ac'], c['z2']),
                        rd([(c['r'], c['r'])]),
                        fp.mul_const(c['t1'], poly.FROB_W[2][0][1]),  # t3 = g t1
                        rd([(c['t1'], c['t1'])]),
                        rd([(c['t2'], c['t2'])]),
                    ],
                ),
                (
                    'push',
                    ['xcz', 'XB', 'YB', 'r4', 'zr', 'z3zeta', 't3s', 'A1', 'A2'],
                    lambda c: [
                        rd([(c['p'][6], c['z'])]),
                        rd([(c['p'][2], one()), (c['p'][3], c['zeta'])]),
                        rd([(c['p'][4], one()), (c['p'][5], c['zeta'])]),
                        rd([(c['r2'], c['r2'])]),
                        rd([(c['z'], c['r'])]),
                        rd([(c['z3'], c['zeta'])]),
                        rd([(c['t3'], c['t3'])]),
                        self.eval_at(c['ac'], c['t1s']),
                        self.eval_at(c['ac'], c['t2s']),
                    ],
                ),
            ]
        )
        end_hi: list[int] = []

        def final(c, checks):
            g1 = bn254.FROB1
            vals = {nm: c[z(int(nm[1:]))] for nm in self.run if nm[0] == 'z' and nm[1:].isdigit()}  # the powers of z
            vals.update({nm: c[nm] for nm in ('zeta', 'z3zeta', 'xcz', 'r2', 'XB', 'YB')})
            vals.update({f'in{i}': c['in'][i] for i in self.ins})
            vals.update(
                nxpz=rd([(c['p'][0], c['nz'])]),
                yp=c['p'][1],
                xczz=rd([(c['xcz'], c['zeta'])]),
                yc=c['p'][7],
                X1=at_zeta_conj(c, c['p'][2], c['p'][3], g1[2]),
                Y1=at_zeta_conj(c, c['p'][4], c['p'][5], g1[3]),
                cp=fp.add(c['acz'], c['z']),
                cm=fp.sub(c['acz'], c['z']),
            )  # E(c) = cp / cm at z
            run = []
            for nm in self.run:
                v = (
                    vals[nm] if vals[nm].hi <= KB or nm.startswith('in') else fp.normalize(vals[nm])
                )  # inputs stay words
                ensure(v.hi <= KB or nm.startswith('in'), f'run value bound: {nm}')
                run.append(v)
            rv = dict(zip(self.run, run))
            start = [rv['cm'], rv['cp'], fp.const(0), rv['XB'], rv['YB'], fp.const(0)]  # u = E(c^-1) = cm / cp
            for nm, v in zip(STATE, start, strict=True):
                ensure(v.hi <= self.b[nm], f'initial bound: {nm}')
            start = [start[:-1], start[-1]]
            # the last relation N pn - D pd: pi(c'^-1) pi^2(c') pi^3(c'^-1) / tau, numerator and denominator
            A3, At = self.eval_at(c['ac'], c['t3s']), self.eval_at(tau(c), c['z2'])
            prod = lambda vs: rd([(rd([(rd([(vs[0], vs[1])]), vs[2])]), vs[3])])
            pn = prod([fp.sub(c['A1'], c['t1']), fp.add(c['A2'], c['t2']), fp.sub(A3, c['t3']), fp.sub(At, c['z'])])
            pd = prod([fp.add(c['A1'], c['t1']), fp.sub(c['A2'], c['t2']), fp.add(A3, c['t3']), fp.add(At, c['z'])])
            ev = {nm: c[nm] if c[nm].hi <= KB else fp.normalize(c[nm]) for nm in END[2:]}
            for nm, v in ev.items():
                ensure(v.hi <= KB, f'end value bound: {nm}')
            end = [pn, fp.mul_const(pd, -1)] + list(ev.values())
            end_hi.extend(v.hi for v in end)
            n_any, n_step = len(RUN_ANY), len(RUN_STEP)
            run = [[run[:n_any], run[n_any:n_step]], run[n_step:]]
            return be.seq(be.checks([ch.e for ch in checks]), be.pack([fp.pack([start, run]), fp.pack(end)]))

        out = chain(fp, ctx, steps, final)
        self.end_hi = end_hi
        h = self.sha_add(self.sha_init(), list(inputs['words']) + [pts])
        h = self.sha_add(h, [ac[0], ac[1]])
        return be.seq(self.top2_6(ac), self._with_h(out, h))

    def _with_h(self, out: Any, h: Any) -> Any:
        """((start, run), end) and h -> ((start, h, run), end)"""
        be = self.be
        if not is_sym(be):
            (start, run), end = out
            return [[[start, h], run], end]
        shape = [
            [[self.core_shape(), [self.run_shape(), words(len(self.run_rest))]], words(len(END))],
            E('', SHA_CTX_W, 0),
        ]
        return be.with_env(
            be.pair(out, h),
            shape,
            lambda a: be.pack([[[be.subtree(a[0][0][0]), a[1]], be.subtree(a[0][0][1])], be.subtree(a[0][1])]),
        )

    # after the loop
    def final(self, state: Any, end: Any, q: Any, rz: Any) -> Term:
        """The last three relations, S(z) = z Q'(z^2) M(z), and r, z against the two hashes."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one = self.rd, self.one
        (st, h), run = state
        run = {nm: Val(w, KB) for nm, w in zip(self.run, flat(run))}
        run.update({nm: Val(w, KB) for nm, w in zip(END, end) if nm in ('z12', 'z14', 'z16')})
        b = self.b
        chunks = [half for blk in q for half in ([blk] if len(blk) == 8 else [blk[:8], blk[8:]])]
        ensure(
            len(blocks(self.prover.n_q)) == len(q) and all(len(ch) == 8 for ch in chunks),
            'Q is read in chunks of 8 words',
        )
        qz = be.word(0)
        for ch in reversed(chunks):
            zs = [run[f'z{k}'].e for k in range(2, 16, 2)]
            qz = be.call(self.QCHUNK, [[[qz, run['z16'].e], zs], be.subtree(ch) if is_sym(be) else ch])
        c = {nm: Val(w, b[nm]) for nm, w in zip(STATE, flat(st), strict=True)}
        c['qz'] = Val(qz, b['qz'])
        c.update({nm: Val(w, hi) for nm, w, hi in zip(END, end, self.end_hi, strict=True)})
        c.update({nm: run[nm] for nm in ('r2', 'z1', 'z6', 'X1', 'Y1')})

        def s_at_z(c):
            # -psi^3(B) = psi^2(psi(B)) negated, and psi^2 (x, y) = (omega x, -y): its point at zeta is (omega X1, Y1)
            X3 = fp.mul_const(c['X1'], bn254.FROB2[2].c0)
            # the even sum with the two relations of the G2 check, the odd one with the last relation
            se = rd(
                [
                    (c['se'], c['r4']),
                    (c['x'], c['r2']),
                    (X3, fp.mul_const(c['r2'], -1)),
                    (c['y'], one()),
                    (c['Y1'], self.m1()),
                ]
            )
            return rd([(c['so'], c['r2']), (c['N'], c['pn']), (c['D'], c['npd']), (se, c['zr'])])

        def minus_zm(c):  # -z M(z)
            return rd([(c['z1'], fp.lin_const([(c['z12'], -1), (c['z6'], 18), (one(), -82)]))])

        steps = [
            ('let', ['s', 'nzm'], lambda c: [s_at_z(c), minus_zm(c)], [*STATE, 'r2', 'z1', 'z6', 'X1', 'Y1', *END])
        ]

        def check(c, _):
            return cv.zero_check(rd([(c['s'], one()), (c['qz'], c['nzm'])])).e

        identity = chain(fp, c, steps, check)
        r_hash = self.sha_final(h)
        z_hash = self.sha_final(self.sha_add(self.sha_add(self.sha_init(), [rz[0]]), list(q)))
        if not is_sym(be):
            ensure(r_hash == rz[0] and z_hash == rz[1], 'challenge')
            return 0
        return be.checks([identity, be.verify(be.eq256(r_hash, rz[0])), be.verify(be.eq256(z_hash, rz[1]))])

    def program(self, inputs: dict[str, Any], pts: Any, ac: Any, rz: Any, leaves: Any = None, q: Any = None) -> Term:
        """The whole check.  inputs: {'x': the public inputs (accessors or Vals), 'words': their words for the
        transcript}; pts, ac, rz as in witness_shape().  Sym: a unit-typed E over the environment, which
        reads the leaves and Q from witness nodes of their own (witness_nodes); Num: runs the checks, on
        the leaves and Q given."""
        be = self.be
        s0 = self.setup(inputs, pts, ac, rz)
        if not is_sym(be):
            st0, end = s0
            return self.final(self.loop(st0, leaves), end, q, rz)
        n_q = self.prover.n_q
        qshape = [words(k) for k in blocks(n_q)]
        parts: dict[str, int] = {}

        def body(a):
            (st0, end), rza = a
            st = self.loop(be.subtree(st0), None)
            qa = be.witness(Q_NAME, q_type(n_q), 256 * n_q)
            out = be.with_env(
                be.pack([st, be.subtree(end), qa, be.subtree(rza)]),
                [self.state_shape(), words(len(END)), qshape, words(2)],
                lambda a: self.final(*a),
            )
            parts.update(loop=st.c, final=out.c - st.c)
            return out

        out = be.with_env(be.pack([s0, be.subtree(rz)]), [[self.state_shape(), words(len(END))], words(2)], body)
        self.parts = {'setup': s0.c, **parts}
        return out


_BOUNDS: dict[str, int] | None = None


def bounds() -> dict[str, int]:
    """The bounds of the loop state (they depend on the structure only), computed once."""
    global _BOUNDS
    if _BOUNDS is None:
        G = bn254.G2_GEN
        # any constant outside F_p6, and no public inputs: the step functions' arguments are bounded alike
        _BOUNDS = PairingCheck(Fp(Num()), G, bn254.Fp12(bn254.Fp6(1), bn254.Fp6(1)), [bn254.Fp12.one()]).b
    return _BOUNDS


# ---------------------------------------------------------------------------------------------------
# The witness of the check: ((points, a_c), (r, z)) in the program's witness, and witness nodes of their
# own for each step's leaf (lambda, or lambda and a) and for Q, in hashing blocks.  a_c and a committed
# value: 4 + 2 words.  The numeric backend takes all of it as one value (witness_num).
LEAF_NAMES = [f'wl{k}' for k in range(N_STEPS)]
Q_NAME = 'wq'


def leaf_shape(commit: bool) -> Shape:
    """(lambda, a): a (4 + 2 words) if committed."""
    return [words(2)] + ([[words(4), words(2)]] if commit else [])


def _T(n: int) -> str:
    return Tbalanced(['2^256'] * n)


def leaf_type(commit: bool) -> str:
    return Tbalanced([_T(2)] + ([f'({_T(4)} * {_T(2)})'] if commit else []))


def q_type(n_q: int) -> str:
    return Tbalanced([_T(k) for k in blocks(n_q)])


def witness_shape() -> Shape:
    """The check's part of w_in: ((points, a_c), (r, z)), for any number of public inputs."""
    return [[words(8), [words(4), words(2)]], words(2)]


def witness_type() -> str:
    return f'(({_T(8)} * ({_T(4)} * {_T(2)})) * {_T(2)})'


def witness_bits() -> int:
    return 256 * (8 + 6 + 2)


def _split(w: dict[str, Any]) -> tuple[Any, Any, Any, Any]:
    def leaf(k, lf):
        return [lf[:2]] + ([[lf[2:6], lf[6:8]]] if COMMIT[k] else [])

    qs, i = [], 0
    for k in blocks(len(w['q'])):
        qs.append(w['q'][i : i + k])
        i += k
    return w['points'], [w['ac'][:4], w['ac'][4:]], [leaf(k, lf) for k, lf in enumerate(w['leaves'])], qs


def witness_num(w: dict[str, Any]) -> list[Any]:
    """The witness as the nested value the numeric backend takes: ((points, a_c), ((r, z), (leaves, Q)))."""
    pts, ac, leaves, qs = _split(w)
    return [[pts, ac], [[w['r'], w['z']], [leaves, qs]]]


def witness_value(w: dict[str, Any]) -> WSpec:
    """The part of the program's witness as a harness value spec (tools/harness)."""
    pts, ac, _, _ = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    return wpair(wpair(W(pts), wpair(W(ac[0]), W(ac[1]))), W([w['r'], w['z']]))


def witness_nodes(w: dict[str, Any]) -> dict[str, WSpec]:
    """The values of the witness nodes of their own, by name."""
    _, _, leaves, qs = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    leaf = lambda lf: balanced([W(lf[0])] + [wpair(W(x[0]), W(x[1])) for x in lf[1:]], wpair)
    out = {nm: leaf(lf) for nm, lf in zip(LEAF_NAMES, leaves)}
    out[Q_NAME] = wbalanced([W(x) for x in qs])
    return out
