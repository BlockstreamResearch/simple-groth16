"""F_p12 as one extension of degree 12: F_p[w] / (w^12 - 18 w^6 + 82).

The tower of bn254.py has u^2 = -1, v^3 = 9 + u, w^2 = v.  So w^6 = 9 + u, and u = w^6 - 9 satisfies
u^2 + 1 = 0, which is M(w) = w^12 - 18 w^6 + 82 = 0.  An element is a polynomial of degree at most 11 in w
with F_p coefficients; a product is the polynomial product reduced modulo M.  F_p2 sits inside as the
polynomials a0 + a1 (w^6 - 9) (`phi`).

Polynomials are lists of ints mod p, lowest degree first.  This module is plain Python: the prover uses it,
and the generator uses it for constants.
"""
from . import bn254

P = bn254.P
M = [82] + [0] * 5 + [P - 18] + [0] * 5 + [1] # w^12 - 18 w^6 + 82


def trim(a):
    a = [x % P for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])


def neg(a):
    return trim([-x for x in a])


def sub(a, b):
    return add(a, neg(b))


def scale(a, k):
    return trim([x * k for x in a])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return trim(out)


def divmod_m(a):
    """(q, r) with a = q M + r, deg r < 12."""
    a = [x % P for x in a] + [0] * max(0, 12 - len(a))
    q = [0] * max(1, len(a) - 12)
    for k in range(len(a) - 1, 11, -1):
        c = a[k]
        if c:
            q[k - 12] = c
            a[k] = 0
            a[k - 6] = (a[k - 6] + 18 * c) % P
            a[k - 12] = (a[k - 12] - 82 * c) % P
    return trim(q), a[:12]


def reduce(a):
    return divmod_m(a)[1]


def evaluate(a, z):
    acc = 0
    for x in reversed(a):
        acc = (acc * z + x) % P
    return acc


def const(c):
    return [c % P]


X = [0, 1]


def phi(a):
    """The F_p2 element a = a0 + a1 u as the polynomial a0 + a1 (w^6 - 9)."""
    a = bn254._fp2(a)
    return trim([a.c0 - 9 * a.c1, 0, 0, 0, 0, 0, a.c1])


def from_tower(f):
    """A bn254.Fp12 as its 12 coefficients in w.  The tower basis element u^a v^b w^c is
    (w^6 - 9)^a w^(2b + c)."""
    out = [0] * 12
    for c, c6 in enumerate((f.c0, f.c1)):
        for b, c2 in enumerate((c6.c0, c6.c1, c6.c2)):
            k = 2 * b + c
            out[k] += c2.c0 - 9 * c2.c1
            out[k + 6] += c2.c1
    return [x % P for x in out]


def to_tower(d):
    d = list(d) + [0] * (12 - len(d))
    c2s = [bn254.Fp2(d[k] + 9 * d[k + 6], d[k + 6]) for k in range(6)]
    # index k = 2b + c
    c0 = bn254.Fp6(c2s[0], c2s[2], c2s[4])
    c1 = bn254.Fp6(c2s[1], c2s[3], c2s[5])
    return bn254.Fp12(c0, c1)


def frobenius_matrix(n):
    """F[j] = pi^n(w^j) as a reduced polynomial (12 coefficients)."""
    out = []
    for j in range(12):
        e = [0] * 12
        e[j] = 1
        out.append(from_tower(to_tower(e).frobenius(n)))
    return out


FROB = {n: frobenius_matrix(n) for n in (1, 2, 3)}
# pi^n(w) = t_n, the (power, coefficient) of its terms: t_1 = a w + b w^7, t_2 = omega' w, t_3 = omega' t_1
FROB_W = {n: [(k, g) for k, g in enumerate(FROB[n][1]) if g] for n in (1, 2, 3)}
