#!/usr/bin/env python3
"""The G2 membership check (groth/pairing.py): after the loop, B's point at z must equal -psi^3(B) at z.
For B on the twist, every other relation is made to hold: the Miller values are B's, the residue
witness is c = 1, s = 0, and the constant of the check is chosen as the inverse of the Miller value
(pairing.miller_values).
So a point outside G2 can only fail on the two G2 relations.  B in G2 must pass; B plus a point of order
10069, and a random point of the twist, must be rejected.

    python3 tests/test_g2_check.py
"""
import math, os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import bn254 as B, poly, pairing as PC
from test_pairing import program, witness, INPUT
import harness


COFACTOR_PRIMES = [10069, 5864401, 1875725156269, 197620364512881247228717050342013327560683201906968909]


def check_kernel(rng):
    """phi = [6x+2] + psi - psi^2 + psi^3 kills G2 and no other point: E'(Fp2) is cyclic of squarefree
    order r h, so it suffices that phi is nonzero on a point of each prime order dividing h."""
    psi, mul = B.g2_frobenius, B.g2_mul_unreduced

    def phi(Q):
        Q1 = psi(Q); Q2 = psi(Q1); Q3 = psi(Q2)
        return B.g2_add(B.g2_add(B.g2_add(mul(Q, 6 * B.X + 2), Q1), B.g2_neg(Q2)), Q3)
    h = 2 * B.P - B.R
    assert h == math.prod(COFACTOR_PRIMES)
    assert phi(B.G2_GEN) is None
    for l in COFACTOR_PRIMES:
        T = mul(B.g2_random_point(rng), B.R * h // l)
        assert T is not None and mul(T, l) is None and phi(T) is not None, l
    print('phi has kernel G2')


def main():
    rng = random.Random(6)
    check_kernel(rng)
    key = random.Random(11)
    gamma, delta = B.g2_mul(B.G2_GEN, key.randrange(1, B.R)), B.g2_mul(B.G2_GEN, key.randrange(1, B.R))
    A, C, L = (B.g1_mul(B.G1_GEN, rng.randrange(1, B.R)) for _ in range(3))
    h = 2 * B.P - B.R
    good = B.g2_mul(B.G2_GEN, rng.randrange(1, B.R))
    small = B.g2_mul_unreduced(B.g2_random_point(rng), B.R * h // 10069) # order 10069
    cases = [('B in G2', good, True), ('B + order-10069 point', B.g2_add(good, small), False),
             ('random twist point', B.g2_random_point(rng), False)]
    b = PC.bounds()
    for label, Bq, in_g2 in cases:
        assert B.g2_on_curve(*Bq) and B.g2_in_subgroup(Bq) == in_g2
        pairs = [(A, Bq), (L, gamma), (C, delta)]
        prover = PC.Prover(gamma, delta, PC.miller_values(pairs)[-1].inv())
        w = prover.witness(pairs, [INPUT], residue=(B.Fp12.one(), 0), check=False)
        rels = PC.relations(PC.PolyRing, w['values'], prover.lines, prover.table)
        failing = [k for k, rel in enumerate(rels) if any(poly.reduce(rel))]
        assert failing == ([] if in_g2 else [PC.N_RELS - 3, PC.N_RELS - 2]), (label, failing)
        text, estimate, _ = program(gamma, delta, prover.const, b)
        r = harness.run('g2_check', text, witness(L, w))
        if in_g2:
            harness.expect_ok(r, label)
            assert r['cost'] == estimate, (r['cost'], estimate)
            print(f'{label:24} accepted')
        else:
            assert not r.get('ok') and r.get('stage') in ('exec', 'finalize'), (label, r)
            print(f'{label:24} rejected: only its two G2 relations fail')
    print('all ok')


if __name__ == '__main__':
    main()
