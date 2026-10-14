"""Plain-Python BN254: the tower Fp < Fp2 < Fp6 < Fp12, G1 and G2, the optimal ate pairing, the residue
witness, Groth16 verification.  This is the reference the generators are tested against; it is itself
checked against py_ecc (tests/test_bn254_ref.py).

    x  = 4965661367192848881
    p  = 36x^4 + 36x^3 + 24x^2 + 6x + 1         base field
    r  = 36x^4 + 36x^3 + 18x^2 + 6x + 1         group order
    E  : y^2 = x^3 + 3                 over Fp       (G1 = E(Fp), cofactor 1)
    E' : y^2 = x^3 + 3/(9+u)           over Fp2      (G2 = E'[r], D-type twist, cofactor h = 2p - r)
    Fp2 = Fp[u]/(u^2 + 1), Fp6 = Fp2[v]/(v^3 - (9+u)), Fp12 = Fp6[w]/(w^2 - v)

h = 10069 * 5864401 * 1875725156269 * q (q a 177-bit prime), so E'(Fp2) has points of small order that
are not in G2.
"""

X = 4965661367192848881
P = 36 * X**4 + 36 * X**3 + 24 * X**2 + 6 * X + 1
R = 36 * X**4 + 36 * X**3 + 18 * X**2 + 6 * X + 1
assert P == 21888242871839275222246405745257275088696311157297823662689037894645226208583
assert R == 21888242871839275222246405745257275088548364400416034343698204186575808495617
ATE_LOOP = 6 * X + 2 # 29793968203157093288


def naf(n):
    """Non-adjacent form, least significant digit first."""
    out = []
    while n:
        if n & 1:
            d = 2 - (n & 3) # 1 or -1
            n -= d
        else:
            d = 0
        out.append(d)
        n >>= 1
    return out


ATE_NAF = naf(ATE_LOOP) # digits, LSB first


# Fp2
class Fp2:
    __slots__ = ('c0', 'c1')

    def __init__(self, c0, c1=0):
        self.c0 = c0 % P
        self.c1 = c1 % P

    def __eq__(self, o):
        o = _fp2(o)
        return self.c0 == o.c0 and self.c1 == o.c1

    def __hash__(self): return hash((self.c0, self.c1))
    def __repr__(self): return f'Fp2({self.c0}, {self.c1})'

    def __add__(self, o): o = _fp2(o); return Fp2(self.c0 + o.c0, self.c1 + o.c1)
    def __sub__(self, o): o = _fp2(o); return Fp2(self.c0 - o.c0, self.c1 - o.c1)
    def __neg__(self): return Fp2(-self.c0, -self.c1)
    __radd__ = __add__

    def __mul__(self, o):
        if isinstance(o, int):
            return Fp2(self.c0 * o, self.c1 * o)
        o = _fp2(o)
        return Fp2(self.c0 * o.c0 - self.c1 * o.c1, self.c0 * o.c1 + self.c1 * o.c0)
    __rmul__ = __mul__

    def square(self):
        return Fp2((self.c0 + self.c1) * (self.c0 - self.c1), 2 * self.c0 * self.c1)

    def conj(self): return Fp2(self.c0, -self.c1)

    def mul_by_xi(self):
        """Multiply by xi = 9 + u."""
        return Fp2(9 * self.c0 - self.c1, self.c0 + 9 * self.c1)

    def inv(self):
        t = pow(self.c0 * self.c0 + self.c1 * self.c1, P - 2, P)
        return Fp2(self.c0 * t, -self.c1 * t)

    def __pow__(self, e):
        r, b = Fp2(1), self
        while e:
            if e & 1: r = r * b
            b = b.square()
            e >>= 1
        return r

    def is_zero(self): return self.c0 == 0 and self.c1 == 0

    def sqrt(self):
        """A square root, or None (p = 3 mod 4: Adj and Rodriguez-Henriquez, algorithm 9)."""
        a1 = self ** ((P - 3) // 4)
        alpha = a1 * a1 * self
        if (alpha ** P) * alpha == Fp2(-1):
            return None
        x0 = a1 * self
        x = Fp2(0, 1) * x0 if alpha == Fp2(-1) else (Fp2(1) + alpha) ** ((P - 1) // 2) * x0
        return x if x.square() == self else None


def _fp2(o):
    return o if isinstance(o, Fp2) else Fp2(o)


XI = Fp2(9, 1)
TWIST_B = XI.inv() * 3 # b' = 3 / xi


# Fp6 = Fp2[v]/(v^3 - xi)
class Fp6:
    __slots__ = ('c0', 'c1', 'c2')

    def __init__(self, c0, c1=None, c2=None):
        self.c0 = _fp2(c0)
        self.c1 = Fp2(0) if c1 is None else _fp2(c1)
        self.c2 = Fp2(0) if c2 is None else _fp2(c2)

    def __eq__(self, o): return self.c0 == o.c0 and self.c1 == o.c1 and self.c2 == o.c2
    def __repr__(self): return f'Fp6({self.c0}, {self.c1}, {self.c2})'
    def __add__(self, o): return Fp6(self.c0 + o.c0, self.c1 + o.c1, self.c2 + o.c2)
    def __sub__(self, o): return Fp6(self.c0 - o.c0, self.c1 - o.c1, self.c2 - o.c2)
    def __neg__(self): return Fp6(-self.c0, -self.c1, -self.c2)

    def __mul__(self, o):
        if isinstance(o, Fp2):
            return Fp6(self.c0 * o, self.c1 * o, self.c2 * o)
        a0, a1, a2 = self.c0, self.c1, self.c2
        b0, b1, b2 = o.c0, o.c1, o.c2
        t0, t1, t2 = a0 * b0, a1 * b1, a2 * b2
        c0 = ((a1 + a2) * (b1 + b2) - t1 - t2).mul_by_xi() + t0
        c1 = (a0 + a1) * (b0 + b1) - t0 - t1 + t2.mul_by_xi()
        c2 = (a0 + a2) * (b0 + b2) - t0 - t2 + t1
        return Fp6(c0, c1, c2)

    def square(self):
        a0, a1, a2 = self.c0, self.c1, self.c2
        s0 = a0.square()
        ab = a0 * a1
        s1 = ab + ab
        s2 = (a0 - a1 + a2).square()
        bc = a1 * a2
        s3 = bc + bc
        s4 = a2.square()
        return Fp6(s0 + s3.mul_by_xi(), s1 + s4.mul_by_xi(), s1 + s2 + s3 - s0 - s4)

    def mul_by_v(self):
        """Multiply by v: (c0, c1, c2) -> (xi c2, c0, c1)."""
        return Fp6(self.c2.mul_by_xi(), self.c0, self.c1)

    def inv(self):
        a0, a1, a2 = self.c0, self.c1, self.c2
        t0 = a0.square() - (a1 * a2).mul_by_xi()
        t1 = a2.square().mul_by_xi() - a0 * a1
        t2 = a1.square() - a0 * a2
        d = (a0 * t0 + (a2 * t1 + a1 * t2).mul_by_xi()).inv()
        return Fp6(t0 * d, t1 * d, t2 * d)

    def is_zero(self): return self.c0.is_zero() and self.c1.is_zero() and self.c2.is_zero()


# Fp12 = Fp6[w]/(w^2 - v)
# Frobenius constants gamma_{1,i} = xi^{i (p-1)/6}
FROB1 = [XI ** (i * (P - 1) // 6) for i in range(6)]
FROB2 = [FROB1[i] * FROB1[i].conj() for i in range(6)] # xi^{i (p^2-1)/6} = gamma1_i * conj(gamma1_i)
FROB3 = [FROB2[i] * FROB1[i] for i in range(6)] # xi^{i (p^3-1)/6}
for i in range(6):
    assert FROB2[i].c1 == 0


class Fp12:
    __slots__ = ('c0', 'c1')

    def __init__(self, c0, c1=None):
        self.c0 = c0 if isinstance(c0, Fp6) else Fp6(c0)
        self.c1 = Fp6(0) if c1 is None else c1

    @staticmethod
    def one(): return Fp12(Fp6(1))

    def __eq__(self, o): return self.c0 == o.c0 and self.c1 == o.c1
    def __repr__(self): return f'Fp12({self.c0}, {self.c1})'
    def __add__(self, o): return Fp12(self.c0 + o.c0, self.c1 + o.c1)
    def __sub__(self, o): return Fp12(self.c0 - o.c0, self.c1 - o.c1)

    def __mul__(self, o):
        a0, a1, b0, b1 = self.c0, self.c1, o.c0, o.c1
        t0, t1 = a0 * b0, a1 * b1
        return Fp12(t0 + t1.mul_by_v(), (a0 + a1) * (b0 + b1) - t0 - t1)

    def square(self):
        a0, a1 = self.c0, self.c1
        t0 = a0 * a1
        c0 = (a0 + a1) * (a0 + a1.mul_by_v()) - t0 - t0.mul_by_v()
        return Fp12(c0, t0 + t0)

    def conj(self): return Fp12(self.c0, -self.c1)

    def inv(self):
        t = (self.c0.square() - self.c1.square().mul_by_v()).inv()
        return Fp12(self.c0 * t, -(self.c1 * t))

    def frobenius(self, n=1):
        """x -> x^(p^n), n in {1, 2, 3}"""
        g = {1: FROB1, 2: FROB2, 3: FROB3}[n]
        cj = (lambda a: a.conj()) if n % 2 else (lambda a: a)
        c0 = Fp6(cj(self.c0.c0), cj(self.c0.c1) * g[2], cj(self.c0.c2) * g[4])
        c1 = Fp6(cj(self.c1.c0) * g[1], cj(self.c1.c1) * g[3], cj(self.c1.c2) * g[5])
        return Fp12(c0, c1)

    def __pow__(self, e):
        r, b = Fp12.one(), self
        while e:
            if e & 1: r = r * b
            b = b.square()
            e >>= 1
        return r

    def mul_by_034(self, c0, c3, c4):
        """Multiply by the sparse element c0 + (c3 + c4 v) w (c0, c3, c4 in Fp2), the shape of a line."""
        a0, a1 = self.c0, self.c1
        t0 = a0 * c0
        t1 = a1 * Fp6(c3, c4)
        t2 = (a0 + a1) * Fp6(c0 + c3, c4)
        return Fp12(t0 + t1.mul_by_v(), t2 - t0 - t1)

    def is_one(self): return self == Fp12.one()


# G1 over Fp
def g1_on_curve(x, y):
    return (y * y - x * x * x - 3) % P == 0


def g1_neg(pt):
    return None if pt is None else (pt[0], (-pt[1]) % P)


def g1_add(a, b):
    """Affine addition; points are (x, y), None is the point at infinity."""
    if a is None: return b
    if b is None: return a
    x1, y1 = a
    x2, y2 = b
    if x1 == x2:
        if (y1 + y2) % P == 0: return None
        l = 3 * x1 * x1 * pow(2 * y1, P - 2, P) % P
    else:
        l = (y2 - y1) * pow(x2 - x1, P - 2, P) % P
    x3 = (l * l - x1 - x2) % P
    return (x3, (l * (x1 - x3) - y1) % P)


def g1_mul(pt, k):
    r = None
    for bit in bin(k % R)[2:]:
        r = g1_add(r, r)
        if bit == '1': r = g1_add(r, pt)
    return r


G1_GEN = (1, 2)


# G2 over Fp2 (affine)
def g2_on_curve(x, y):
    return y.square() == x.square() * x + TWIST_B


def g2_neg(pt):
    return None if pt is None else (pt[0], -pt[1])


def g2_add(a, b):
    if a is None: return b
    if b is None: return a
    x1, y1 = a
    x2, y2 = b
    if x1 == x2:
        if (y1 + y2).is_zero(): return None
        l = x1.square() * 3 * (y1 + y1).inv()
    else:
        l = (y2 - y1) * (x2 - x1).inv()
    x3 = l.square() - x1 - x2
    return (x3, l * (x1 - x3) - y1)


def g2_mul(pt, k):
    """[k] pt for pt in G2 (k is reduced mod r, so not for points outside G2)"""
    return g2_mul_unreduced(pt, k % R)


def g2_mul_unreduced(pt, k):
    """[k] pt for any point of the twist."""
    r = None
    for bit in bin(k)[2:]:
        r = g2_add(r, r)
        if bit == '1': r = g2_add(r, pt)
    return r


def g2_random_point(rng):
    """A random point of E'(Fp2); almost surely not in G2."""
    while True:
        x = Fp2(rng.randrange(P), rng.randrange(P))
        y = (x.square() * x + TWIST_B).sqrt()
        if y is not None:
            return (x, y)


def g2_in_subgroup(pt):
    """pt is in G2, the order-r subgroup of E'(Fp2)."""
    return pt is not None and g2_mul_unreduced(pt, R) is None


G2_GEN = (Fp2(10857046999023057135944570762232829481370756359578518086990519993285655852781,
              11559732032986387107991004021392285783925812861821192530917403151452391805634),
          Fp2(8495653923123431417604973247489272438418190587263600148770280649306958101930,
              4082367875863433681332203403145435568316851327593401208105741076214120093531))


def g2_frobenius(pt):
    """The p-power Frobenius through the twist (psi): (x, y) -> (conj(x) gamma_{1,2}, conj(y) gamma_{1,3})."""
    x, y = pt
    return (x.conj() * FROB1[2], y.conj() * FROB1[3])


# Miller loop (homogeneous projective T = (X, Y, Z), D-type twist)
def line_double(T):
    """Doubling step: (2T, line coefficients (c0, c3, c4) before evaluation at P)."""
    x, y, z = T
    a = (x * y) * pow(2, P - 2, P) # x y / 2
    b = y.square()
    c = z.square()
    e = TWIST_B * (c + c + c) # 3 b' z^2
    f = e + e + e
    g = (b + f) * pow(2, P - 2, P)
    h = (y + z).square() - (b + c) # 2 y z
    i = e - b
    j = x.square()
    e2 = e.square()
    T2 = (a * (b - f), g.square() - (e2 + e2 + e2), b * h)
    return T2, (-h, j + j + j, i)


def line_add(T, Q):
    """Mixed addition step with affine Q: (T + Q, line coefficients (c0, c3, c4))."""
    x, y, z = T
    qx, qy = Q
    theta = y - qy * z
    lam = x - qx * z
    c = theta.square()
    d = lam.square()
    e = lam * d
    f = z * c
    g = x * d
    h = e + f - (g + g)
    T2 = (lam * h, theta * (g - h) - e * y, z * e)
    j = theta * qx - lam * qy
    return T2, (lam, -theta, j)


def eval_line(coeffs, Pt):
    """The line evaluated at P = (xP, yP): the sparse element (c0 yP, c3 xP, c4)."""
    c0, c3, c4 = coeffs
    xP, yP = Pt
    return (c0 * yP, c3 * xP, c4)


# Affine Miller loop, the one the program computes.  The slope lambda of each step is a prover hint, and
# the line through T with slope lambda, evaluated at P, is
#     yP + (-lambda xP) w + (lambda xT - yT) v w
# It differs from the projective line by a factor in Fp2*, which the final exponentiation kills.
def affine_double_slope(T):
    x, y = T
    return x.square() * 3 * (y + y).inv()


def affine_add_slope(T, Q):
    return (Q[1] - T[1]) * (Q[0] - T[0]).inv()


def affine_step(T, lam, Q=None):
    """Doubling (Q None) or addition with slope lam: (T', (c3, c4)) with c3 = -lam (the factor of xP)
    and c4 = lam xT - yT."""
    x, y = T
    if Q is None:
        assert lam * (y + y) == x.square() * 3
        x2 = lam.square() - x - x
    else:
        assert Q[0] != x
        assert lam * (Q[0] - x) == Q[1] - y
        x2 = lam.square() - x - Q[0]
    y2 = lam * (x - x2) - y
    return (x2, y2), (-lam, lam * x - y)


def affine_line(coeffs, Pt):
    c3, c4 = coeffs
    xP, yP = Pt
    return (Fp2(yP, 0), c3 * xP, c4)


def multi_miller_loop_affine(pairs, hints=None):
    """multi_miller_loop with affine steps.  If `hints` is a list, it receives the slopes of every step
    of each pair, in loop order: what the program gets as witness."""
    f = Fp12.one()
    Ts = [Q for _, Q in pairs]
    negQs = [g2_neg(Q) for _, Q in pairs]
    per_pair = [[] for _ in pairs]
    digits = ATE_NAF
    for idx in range(len(digits) - 2, -1, -1):
        f = f.square()
        d = digits[idx]
        for k, (Pt, Q) in enumerate(pairs):
            lam = affine_double_slope(Ts[k])
            per_pair[k].append(lam)
            Ts[k], l = affine_step(Ts[k], lam)
            f = f.mul_by_034(*affine_line(l, Pt))
            if d:
                Qk = Q if d > 0 else negQs[k]
                lam = affine_add_slope(Ts[k], Qk)
                per_pair[k].append(lam)
                Ts[k], l = affine_step(Ts[k], lam, Qk)
                f = f.mul_by_034(*affine_line(l, Pt))
    for k, (Pt, Q) in enumerate(pairs):
        Q1 = g2_frobenius(Q)
        Q2 = g2_neg(g2_frobenius(Q1))
        for Qk in (Q1, Q2):
            lam = affine_add_slope(Ts[k], Qk)
            per_pair[k].append(lam)
            Ts[k], l = affine_step(Ts[k], lam, Qk)
            f = f.mul_by_034(*affine_line(l, Pt))
    if hints is not None:
        hints.extend(per_pair)
    return f


def multi_miller_loop(pairs):
    """prod_i f_{6x+2,Q_i}(P_i) times the two Frobenius lines of each pair; the pairs run in lockstep,
    one squaring per iteration."""
    f = Fp12.one()
    Ts = [(Q[0], Q[1], Fp2(1)) for _, Q in pairs]
    negQs = [g2_neg(Q) for _, Q in pairs]
    digits = ATE_NAF
    for idx in range(len(digits) - 2, -1, -1):
        f = f.square()
        d = digits[idx]
        for k, (Pt, Q) in enumerate(pairs):
            Ts[k], l = line_double(Ts[k])
            f = f.mul_by_034(*eval_line(l, Pt))
            if d:
                Ts[k], l = line_add(Ts[k], Q if d > 0 else negQs[k])
                f = f.mul_by_034(*eval_line(l, Pt))
    for k, (Pt, Q) in enumerate(pairs):
        Q1 = g2_frobenius(Q)
        Q2 = g2_neg(g2_frobenius(Q1))
        Ts[k], l = line_add(Ts[k], Q1)
        f = f.mul_by_034(*eval_line(l, Pt))
        Ts[k], l = line_add(Ts[k], Q2)
        f = f.mul_by_034(*eval_line(l, Pt))
    return f


def miller_loop(Pt, Q):
    return multi_miller_loop([(Pt, Q)])


def final_exponentiation(f):
    # easy part: f^((p^6 - 1)(p^2 + 1))
    f = f.conj() * f.inv()
    f = f.frobenius(2) * f
    # hard part: f^((p^4 - p^2 + 1) / r), a plain exponentiation (the program uses the residue witness)
    return f ** ((P**4 - P**2 + 1) // R)


def pairing(Pt, Q):
    return final_exponentiation(miller_loop(Pt, Q))


# Residue witness (Novakovic and Eagen, "On Proving Pairings", 2024).  Let lambda = 6x + 2 + p - p^2 + p^3
# and h = (p^12 - 1) / r.  The Miller value f has f^h = 1 iff f w = c^lambda for some c in Fp12 and some
# 27th root of unity w.  The image of c -> c^lambda is the subgroup of order h / 3, so f w must have
# order dividing h / 3; w = W27^s, s in {0, 1, 2}, fixes the cube-root-of-unity class of f.  The affine
# Miller value works as well: it differs from the projective one by an element of Fp2*, whose order
# divides h.
LAMBDA = 6 * X + 2 + P - P**2 + P**3
H = (P**12 - 1) // R
assert LAMBDA % R == 0 and H % 27 == 0 and (H // 3) % 9 == 0
W27 = Fp12(Fp6(Fp2(0), Fp2(15836853091350922279986891577810600172284355046962111325588466915565967022071,
                        7058631431986672612198325957254478126651525007192415024767579040330467842072)))
assert W27 ** 27 == Fp12.one() and W27 ** 9 != Fp12.one()


def residue_witness(f):
    """(c, s) with f W27^s = c^LAMBDA, s in {0, 1, 2}; None if f^H != 1 (the pairing product is not 1).
    c is a cube root of u = (f W27^s)^((LAMBDA/3)^-1 mod H/3), taken separately on the mu_27 part of u
    (a table lookup) and on the rest (an exponentiation)."""
    one = Fp12.one()
    for s in range(3):
        y = f * W27 ** s
        if y ** (H // 3) == one:
            break
    else:
        return None
    u = y ** pow(LAMBDA // 3, -1, H // 3)
    n = P**12 - 1
    a = pow(27, -1, n // 27)
    u3, u27 = u ** ((1 - 27 * a) % n), u ** (27 * a % n) # u = u3 u27, u3 in mu_27, u27 of order prime to 3
    c = u27 ** pow(3, -1, n // 27)
    for k in range(27):
        if W27 ** (3 * k) == u3:
            return c * W27 ** k, s
    raise AssertionError('no cube root')


def residue_check(f, c, s):
    """The program's form of f W27^s = c^LAMBDA: f c^-(6x+2) pi(c^-1) pi^2(c) pi^3(c^-1) = W27^-s."""
    ci = c.inv()
    return f * ci ** ATE_LOOP * ci.frobenius(1) * c.frobenius(2) * ci.frobenius(3) == (W27 ** s).inv()


def multi_pairing(pairs):
    """prod e(P_i, Q_i) with one final exponentiation."""
    return final_exponentiation(multi_miller_loop(pairs))


# Groth16
def groth16_verify(vk, proof, public_inputs):
    """Groth16 verification: e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta), L = ic[0] + sum a_i ic[i].
    vk = dict(alpha, beta, gamma, delta, ic); proof = (A, B, C).  Also checks that A, C are on the curve,
    that B is in G2 and that the inputs are below r."""
    A, B, C = proof
    if A is None or C is None or not (g1_on_curve(*A) and g1_on_curve(*C)):
        return False
    if not (g2_on_curve(*B) and g2_in_subgroup(B)):
        return False
    if len(public_inputs) != len(vk['ic']) - 1 or not all(0 <= a < R for a in public_inputs):
        return False
    L = vk['ic'][0]
    for a, pt in zip(public_inputs, vk['ic'][1:]):
        L = g1_add(L, g1_mul(pt, a))
    lhs = multi_pairing([(g1_neg(A), B), (vk['alpha'], vk['beta']), (L, vk['gamma']), (C, vk['delta'])])
    return lhs.is_one()


def groth16_instance(n_inputs=2, seed=7, inputs=None):
    """A synthetic key and proof for tests: random toxic waste, and A, B, C chosen to satisfy the
    verification equation.  A verifier cannot tell it from a real proof.  Random inputs unless given."""
    import random
    r = random.Random(seed)
    alpha, beta, gamma, delta = (r.randrange(1, R) for _ in range(4))
    ic_scalars = [r.randrange(1, R) for _ in range(n_inputs + 1)]
    inputs = [r.randrange(R) for _ in range(n_inputs)] if inputs is None else list(inputs)
    assert len(inputs) == n_inputs
    # choose a, b for the proof; then c solves ab = alpha beta + L gamma + c delta (as exponents)
    a, b = r.randrange(1, R), r.randrange(1, R)
    L = (ic_scalars[0] + sum(s * x for s, x in zip(ic_scalars[1:], inputs))) % R
    c = (a * b - alpha * beta - L * gamma) * pow(delta, -1, R) % R
    vk = dict(alpha=g1_mul(G1_GEN, alpha), beta=g2_mul(G2_GEN, beta), gamma=g2_mul(G2_GEN, gamma),
              delta=g2_mul(G2_GEN, delta), ic=[g1_mul(G1_GEN, s) for s in ic_scalars])
    proof = (g1_mul(G1_GEN, a), g2_mul(G2_GEN, b), g1_mul(G1_GEN, c))
    return vk, proof, inputs
