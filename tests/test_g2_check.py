#!/usr/bin/env python3
"""The G2 membership check (groth/core/pairing.py): after the loop, its point T = [6x+2]B + psi(B) -
psi^2(B) must equal -psi^3(B), as polynomials at z.
For B on the twist, every other relation is made to hold: the Miller values are B's, the residue
witness c is a fixed element, and the constant of the check is chosen so that the residue check holds:
c^lambda times the inverse of the Miller value.
So a point outside G2 can only fail on the two G2 relations.  B in G2 must pass; B plus a point of order
10069, and a random point of the twist, must be rejected.

It also checks that no addition of the loop can meet T = Q, for any point B of the twist, which is why
the slope relations need no inverse of xQ - x.

    python3 tests/test_g2_check.py
"""

import math
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness
from test_pairing import program, witness

from groth.core import bn254 as B
from groth.core import pairing as PC
from groth.core import poly

COFACTOR_PRIMES = list(PC.COFACTOR_PRIMES)


def check_kernel(rng):
    """phi = [6x+2] + psi - psi^2 + psi^3 kills G2 and no other point: E'(Fp2) is cyclic of squarefree
    order r h, so it suffices that phi is nonzero on a point of each prime order dividing h."""
    psi, mul = B.g2_frobenius, B.g2_mul_unreduced

    def phi(Q):
        Q1 = psi(Q)
        Q2 = psi(Q1)
        Q3 = psi(Q2)
        return B.g2_add(B.g2_add(B.g2_add(mul(Q, 6 * B.X + 2), Q1), B.g2_neg(Q2)), Q3)

    h = 2 * B.P - B.R
    assert h == math.prod(COFACTOR_PRIMES)
    assert phi(B.G2_GEN) is None
    for l in COFACTOR_PRIMES:
        T = mul(B.g2_random_point(rng), B.R * h // l)
        assert T is not None and mul(T, l) is None and phi(T) is not None, l
    print('phi has kernel G2')


def sqrt_mod(a, q):
    """A square root of a modulo the odd prime q (Tonelli-Shanks)."""
    if a % q == 0:
        return 0
    assert pow(a, (q - 1) // 2, q) == 1
    s, e = q - 1, 0
    while s % 2 == 0:
        s, e = s // 2, e + 1
    n = next(n for n in range(2, q) if pow(n, (q - 1) // 2, q) == q - 1)
    x, b, g = pow(a, (s + 1) // 2, q), pow(a, s, q), pow(n, s, q)
    while b != 1:
        m, t = 0, b
        while t != 1:
            t, m = t * t % q, m + 1
        gs = pow(g, 1 << (e - m - 1), q)
        x, g, b, e = x * gs % q, gs * gs % q, b * gs * gs % q, m
    return x


def eigenvalue(rng, l):
    """psi on the points of prime order l of the twist, a cyclic group, is multiplication by a root mu of
    mu^2 - t mu + p, t = p + 1 - r the trace of Frobenius; the root is the one that matches on a point."""
    mul, n = B.g2_mul_unreduced, B.R * (2 * B.P - B.R)
    T = None
    while T is None:
        T = mul(B.g2_random_point(rng), n // l)
    t = B.P + 1 - B.R
    d, half = sqrt_mod((t * t - 4 * B.P) % l, l), pow(2, -1, l)
    mu = next(m for m in ((t + d) * half % l, (t - d) * half % l) if mul(T, m) == B.g2_frobenius(T))
    return mu


def check_additions(rng):
    """No addition of the loop meets T = Q, whatever the point B of the twist.  The group is cyclic, so on
    its part of prime order l, T = [k] B and Q = [q] B with q = 1, -1 (B, -B), or mu, -mu^2 for the
    Frobenius additions (psi(B), -psi^2(B)); T = Q needs l | k - q for some prime l of the group order,
    which happens for none.  (T = -Q fails the slope relation: 0 = 2 yQ.)  The generator checks this with
    pairing.additions_avoid_q and the eigenvalues pairing.PSI_EIGEN, which are derived here."""
    assert B.g2_frobenius(B.G2_GEN) == B.g2_mul(B.G2_GEN, B.P % B.R)
    mus = {l: eigenvalue(rng, l) for l in COFACTOR_PRIMES}
    mus[B.R] = B.P % B.R
    assert mus == PC.PSI_EIGEN, 'the eigenvalues of psi'
    k = 1
    for kind in PC.STEPS:
        if kind == 'D':
            k *= 2
        elif kind in ('A+', 'A-'):
            q = 1 if kind == 'A+' else -1
            assert all((k - q) % l for l in mus), (kind, k)
            k += q
    assert k == 6 * B.X + 2
    for l, mu in mus.items():
        assert (k - mu) % l and (k + mu + mu * mu) % l, l
    assert PC.additions_avoid_q(PC.STEPS)
    # and the generator's check refuses loops that break it: an addition at T = B, a loop that does not
    # reach 6x + 2, a Frobenius addition in the middle
    assert not PC.additions_avoid_q(['A+', 'F1', 'F2'])
    assert not PC.additions_avoid_q(PC.STEPS[1:])
    assert not PC.additions_avoid_q(['F1'] + PC.STEPS[:-1])
    print('no addition meets T = Q')


def main():
    rng = random.Random(6)
    check_kernel(rng)
    check_additions(rng)
    key = random.Random(11)
    gamma, delta = B.g2_mul(B.G2_GEN, key.randrange(1, B.R)), B.g2_mul(B.G2_GEN, key.randrange(1, B.R))
    A, C = (B.g1_mul(B.G1_GEN, rng.randrange(1, B.R)) for _ in range(2))
    # no public inputs (gamma pairs with IC_0 alone), so that the program has no tables: B's relations do
    # not depend on them
    gt = PC.gt_constants([B.g1_mul(B.G1_GEN, rng.randrange(1, B.R))], gamma)
    unit = PC.Prover(delta, B.Fp12.one(), gt)
    h = 2 * B.P - B.R
    good = B.g2_mul(B.G2_GEN, rng.randrange(1, B.R))
    small = B.g2_mul_unreduced(B.g2_random_point(rng), B.R * h // 10069)  # order 10069
    cases = [
        ('B in G2', good, True),
        ('B + order-10069 point', B.g2_add(good, small), False),
        ('random twist point', B.g2_random_point(rng), False),
    ]
    b = PC.bounds()
    c = B.Fp12(B.Fp6(B.Fp2(3, 1)), B.Fp6(B.Fp2(5, 2)))  # any element outside F_p6
    c_lam = c**B.LAMBDA
    for label, Bq, in_g2 in cases:
        assert B.g2_on_curve(*Bq) and B.g2_in_subgroup(Bq) == in_g2
        pairs = [(A, Bq), (C, delta)]
        prover = PC.Prover(delta, c_lam * unit.product(pairs, []).inv(), gt)
        w = prover.witness(pairs, [], residue=(c, 0), check=False)
        rels = PC.relations(PC.PolyRing, w['values'], prover.lines)
        failing = [k for k, rel in enumerate(rels) if any(poly.reduce(rel))]
        assert failing == ([] if in_g2 else [PC.N_RELS - 3, PC.N_RELS - 2]), (label, failing)
        text, estimate, _ = program(delta, prover.const, gt, b)
        r = harness.run('g2_check', text, witness([], w))
        if in_g2:
            harness.expect_ok(r, label)
            assert r['cost'] == estimate, (r['cost'], estimate)
            print(f'{label:24} accepted')
        else:
            harness.expect_rejected(r, label)
            print(f'{label:24} rejected: only its two G2 relations fail')
    print('all ok')


if __name__ == '__main__':
    main()
