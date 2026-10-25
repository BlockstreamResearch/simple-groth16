#!/usr/bin/env python3
"""groth/core/bn254.py against py_ecc's bn128 (pip install py_ecc): the tower, G1 and G2, the pairing, the
residue witness, Groth16 verification, and points of the twist outside G2.

    python3 tests/test_bn254_ref.py
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from py_ecc import bn128 as E

from groth.core import bn254 as B
from groth.core import poly

rng = random.Random(1)


def to_pyecc_g1(pt):
    return None if pt is None else (E.FQ(pt[0]), E.FQ(pt[1]))


def to_pyecc_g2(pt):
    return None if pt is None else (E.FQ2([pt[0].c0, pt[0].c1]), E.FQ2([pt[1].c0, pt[1].c1]))


def to_pyecc_fq12(f):
    # py_ecc's FQ12 is F_p[w] / (w^12 - 18 w^6 + 82), the direct extension of groth/core/poly.py
    return E.FQ12(poly.from_tower(f))


def test_tower():
    for _ in range(50):
        a = B.Fp2(rng.randrange(B.P), rng.randrange(B.P))
        b = B.Fp2(rng.randrange(B.P), rng.randrange(B.P))
        assert a * b == b * a and a.square() == a * a
        assert (a * a.inv()) == B.Fp2(1)
        A = B.Fp6(a, b, a + b)
        Bb = B.Fp6(b, a.square(), b - a)
        assert A.square() == A * A
        assert (A * A.inv()) == B.Fp6(1)
        assert (A * Bb) * B.Fp6(0, 1, 0) == A * Bb.mul_by_v() == A.mul_by_v() * Bb
        F = B.Fp12(A, Bb)
        G = B.Fp12(Bb, A * Bb)
        assert F.square() == F * F
        assert (F * F.inv()).is_one()
        assert F * G == G * F
        for n in (1, 2, 3):
            assert F.frobenius(n) == F ** (B.P**n), n
        c0, c3, c4 = a, b, a * b
        sparse = B.Fp12(B.Fp6(c0), B.Fp6(c3, c4))
        assert F.mul_by_034(c0, c3, c4) == F * sparse
        # py_ecc agreement of the multiplication
        assert to_pyecc_fq12(F * G) == to_pyecc_fq12(F) * to_pyecc_fq12(G)
    print('tower ok')


def test_groups():
    assert B.g1_on_curve(*B.G1_GEN) and B.g2_on_curve(*B.G2_GEN)
    assert B.g1_mul(B.G1_GEN, B.R - 1) == B.g1_neg(B.G1_GEN)
    assert B.g2_in_subgroup(B.G2_GEN) and B.g2_in_subgroup(B.g2_mul(B.G2_GEN, rng.randrange(1, B.R)))
    for _ in range(5):
        k = rng.randrange(B.R)
        assert to_pyecc_g1(B.g1_mul(B.G1_GEN, k)) == E.multiply(E.G1, k)
        assert to_pyecc_g2(B.g2_mul(B.G2_GEN, k)) == E.multiply(E.G2, k)
    # the twist has points outside G2, of every order dividing the cofactor 2p - r
    h = 2 * B.P - B.R
    assert h == 10069 * 5864401 * 1875725156269 * 197620364512881247228717050342013327560683201906968909
    Q = B.g2_random_point(rng)
    assert B.g2_on_curve(*Q) and not B.g2_in_subgroup(Q)
    assert B.g2_mul_unreduced(Q, B.R * h) is None
    T = B.g2_mul_unreduced(Q, B.R * h // 10069)  # a point of order 10069
    assert T is not None and B.g2_mul_unreduced(T, 10069) is None and not B.g2_in_subgroup(T)
    print('groups ok')


def test_pairing():
    for _ in range(3):
        a, b = rng.randrange(1, B.R), rng.randrange(1, B.R)
        Pa = B.g1_mul(B.G1_GEN, a)
        Qb = B.g2_mul(B.G2_GEN, b)
        e1 = B.pairing(Pa, Qb)
        e2 = B.pairing(B.G1_GEN, B.G2_GEN) ** (a * b % B.R)
        assert e1 == e2, 'bilinearity'
        ref = E.pairing(to_pyecc_g2(Qb), to_pyecc_g1(Pa))
        assert to_pyecc_fq12(e1) == ref, 'py_ecc disagreement'
        # multi-pairing: e(P, Q) e(-P, Q) = 1
        assert B.multi_pairing([(Pa, Qb), (B.g1_neg(Pa), Qb)]).is_one()
        # the affine Miller loop gives the same pairing (its Miller value differs by an F_p2* factor)
        hints = []
        fa = B.multi_miller_loop_affine([(Pa, Qb), (B.G1_GEN, B.G2_GEN)], hints)
        assert B.final_exponentiation(fa) == B.final_exponentiation(
            B.multi_miller_loop([(Pa, Qb), (B.G1_GEN, B.G2_GEN)])
        )
        assert len(hints) == 2 and len(hints[0]) == len(B.ATE_NAF) - 1 + sum(1 for d in B.ATE_NAF[:-1] if d) + 2
    print('pairing ok')


def test_residue_witness():
    a, b = rng.randrange(1, B.R), rng.randrange(1, B.R)
    pairs = [(B.g1_mul(B.G1_GEN, a), B.g2_mul(B.G2_GEN, b)), (B.g1_mul(B.G1_GEN, (-a) % B.R), B.g2_mul(B.G2_GEN, b))]
    f = B.multi_miller_loop_affine(pairs)
    c, s = B.residue_witness(f)
    assert B.residue_check(f, c, s)
    assert B.residue_witness(B.multi_miller_loop_affine(pairs[:1])) is None, 'a product that is not 1 has no witness'
    print('residue witness ok')


def test_groth16():
    vk, proof, inputs = B.groth16_instance()
    assert B.groth16_verify(vk, proof, inputs)
    bad = list(inputs)
    bad[0] = (bad[0] + 1) % B.R
    assert not B.groth16_verify(vk, proof, bad)
    A, Bp, C = proof
    assert not B.groth16_verify(vk, (A, Bp, B.g1_add(C, B.G1_GEN)), inputs)
    assert not B.groth16_verify(vk, proof, [inputs[0] + B.R] + inputs[1:]), 'an input >= r'
    T = B.g2_mul_unreduced(B.g2_random_point(rng), B.R)  # a point of the cofactor part
    assert not B.groth16_verify(vk, (A, B.g2_add(Bp, T), C), inputs), 'B outside G2'
    print('groth16 ok')


if __name__ == '__main__':
    test_tower()
    test_groups()
    test_pairing()
    test_residue_witness()
    test_groth16()
