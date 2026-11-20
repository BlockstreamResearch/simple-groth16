#!/usr/bin/env python3
"""The pairing check for two fixed points of G2 (groth/core/pairing_fixed.py), on an instance with
e(P1, [1]_2) e(P2, [x]_2) e(K, [1]_2) = 1, the shape of fflonk's check: the Miller value of (K, [1]_2) is
the check's constant.  The line constants must give bn254's Miller loop, the model's S(z) must equal
z Q'(z^2) M(z) for the odd quotient Q = w Q'(w^2), every relation must be odd and of the degree the
generator counts, the program must accept, and it must reject witnesses that are wrong in one place but
sealed consistently (r, Q and z recomputed), so that only the identity can catch them: a wrong Miller
value, a wrong residue witness, another point.  A wrong challenge (r or z) and a word changed to another
encoding of its value without sealing again must be rejected too, and a false instance has no witness.

    python3 tests/test_pairing_fixed.py    # SEED=5: the instance
"""

import os
import random
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import bn254 as B
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core import pairing_fixed as PF
from groth.core import poly
from groth.core.dsl import CheckFailed
from groth.core.sym import Num, Sym

P = F.P


def instance(rng, key):
    """q1 = [1]_2 and q2 = [x]_2 from the key, with the Miller value of (K, [1]_2); P2 random and
    P1 = -(x P2 + K)."""
    x, k = key.randrange(1, B.R), key.randrange(1, B.R)
    q1, q2 = B.G2_GEN, B.g2_mul(B.G2_GEN, x)
    K = B.g1_mul(B.G1_GEN, k)
    p2 = rng.randrange(1, B.R)
    P2 = B.g1_mul(B.G1_GEN, p2)
    P1 = B.g1_mul(B.G1_GEN, -(x * p2 + k) % B.R)
    assert B.multi_pairing([(P1, q1), (P2, q2), (K, q1)]).is_one()
    return q1, q2, B.multi_miller_loop_affine([(K, q1)]), [P1, P2]


def numeric(pc, w):
    (pts, ac), (rz, (leaves, q)) = PF.witness_num(w)
    return pc.program(pts, ac, rz, leaves, q)


def program(q1, q2, const, b):
    """The check alone, on its witness."""
    bits = PF.witness_bits()
    be = Sym(bits)
    pc = PF.FixedCheck(F.Fp(be), q1, q2, const, b)
    (pts, ac), rz = be._unpack('', PF.witness_shape())
    body = pc.program(pts, ac, rz)
    be.em.define('w_in', 'witness', f'_ -> {PF.witness_type()}')
    be.em.define('main', f'comp w_in ({body.t})')
    return be.em.text(), 2 * (100 + bits) + body.c, pc


def witness(w):
    return {'w_in': PF.witness_value(w), **PF.witness_nodes(w)}


def tampered(prover, w, how):
    """The honest values with one change, sealed again."""
    v = dict(w['values'])
    v['a'] = [None if a is None else list(a) for a in v['a']]
    v['ac'] = list(v['ac'])
    if how == 'Miller value':
        k = next(i for i in range(40, PC.N_STEPS) if PF.COMMIT[i])
        v['a'][k][3] += 1
    elif how == 'residue witness':
        v['ac'][2] += 1
    elif how == 'point':  # another point of the curve, with the honest values
        v['P'] = [v['P'][0], B.g1_add(v['P'][1], B.G1_GEN)]
    return prover.seal(v, check=False)


def main():
    rng = random.Random(int(os.environ.get('SEED', '5')))
    q1, q2, const, points = instance(rng, random.Random(11))
    n_add = sum(1 for k, kind in enumerate(PC.STEPS) if kind != 'D' and not PF.COMMIT[k])
    print(
        f'{PF.N_RELS} relations ({sum(PF.COMMIT)} committed values, {n_add} additions without one), '
        f'S of degree {PF.DEG_S}, Q of {PF.N_Q} words'
    )
    # the line constants give the Miller loop: the product of the lines at the two points, by step
    prover = PF.Prover(q1, q2, const)
    f = B.Fp12.one()
    for i, kind in enumerate(PC.STEPS):
        f = f.square() if kind == 'D' else f
        for pt, ln in zip(points, prover.lines):
            f = f.mul_by_034(*B.affine_line(ln[i], pt))
    assert f == B.multi_miller_loop_affine(list(zip(points, (q1, q2))))
    assert B.final_exponentiation(prover.product(points)).is_one()
    # prover and model
    t0 = time.time()
    w = prover.witness(points)
    r, z = F.from_mont(w['r']), F.from_mont(w['z'])
    R = PC.NumRing(z)
    S = PF.combine(R, PF.relations(R, w['values'], prover.lines), r)
    # Q = w Q'(w^2), and the witness has the coefficients of Q'
    assert z * poly.evaluate([F.from_mont(q) for q in w['q']], z * z) * poly.evaluate(poly.M, z) % P == S
    # the degrees the generator counts (and sizes Q by) are the relations' degrees, and each relation is
    # odd: that is what makes S odd, and Q with it
    rels = PF.relations(PC.PolyRing, w['values'], prover.lines)
    degs = [len(poly.trim(rel)) - 1 for rel in rels]
    assert degs == PF._degrees(PF.COMMIT) and max(degs) == PF.DEG_S <= PF.DEG_CAP
    assert len(rels) == PF.N_RELS and all(not any(rel[0::2]) for rel in rels)
    assert len(w['leaves']) == sum(PF.COMMIT) == len(PF.LEAF_NAMES) and len(w['q']) == PF.N_Q
    print(f"witness in {time.time() - t0:.1f}s, S(z) = z Q'(z^2) M(z), the relations odd and of the degrees counted")
    bad = [(how, tampered(prover, w, how)) for how in ('Miller value', 'residue witness', 'point')]
    wrong_r = dict(w)
    wrong_r['r'] ^= 1
    bad.append(('challenge', wrong_r))
    wrong_z = dict(w)
    wrong_z['z'] ^= 1
    bad.append(('second challenge', wrong_z))
    # the same point word plus 4p (another encoding of the same value) without sealing again: r covers
    # the raw words, so the challenge must reject it
    reencoded = dict(w)
    reencoded['points'] = [w['points'][0] + 4 * P] + w['points'][1:]
    assert reencoded['points'][0] < 2**256
    bad.append(('re-encoded word', reencoded))
    # a point off the curve, sealed again: the on-curve check must reject it whatever the relations do
    off = dict(w['values'])
    off['P'] = [(points[0][0], (points[0][1] + 1) % P), points[1]]
    bad.append(('point off the curve', prover.seal(off, check=False)))
    # numeric model
    b = PF.bounds()
    pcn = PF.FixedCheck(F.Fp(Num()), q1, q2, const, b)
    numeric(pcn, w)
    for how, wb in bad:
        try:
            numeric(pcn, wb)
            raise AssertionError(f'numeric model accepted a wrong {how}')
        except CheckFailed:
            pass
    print('numeric model ok, rejects the tampered witnesses')
    # false instance: no witness
    assert prover.witness([points[0], B.g1_add(points[1], B.G1_GEN)]) is None
    # the program
    text, estimate, pc = program(q1, q2, const, b)
    t0 = time.time()
    res = harness.run('pairing_fixed', text, witness(w), multi=[witness(wb) for _, wb in bad])
    ok = harness.expect_ok(res[0], 'pairing check, fixed G2')
    assert ok['cost'] == estimate, (ok['cost'], estimate)
    for (how, _), rb in zip(bad, res[1:]):
        harness.expect_rejected(rb, how)
        print(f'wrong {how:19} rejected')
    print(
        f'pairing check cost {ok["cost"]:,}: setup {pc.parts["setup"]:,}, loop {pc.parts["loop"]:,}, final {pc.parts["final"]:,}'
    )
    print('steps: ' + ', '.join(f'{k} {v:,}' for k, v in pc.costs.items()))
    print(f'program {ok["program_bytes"]:,} B, witness {ok["witness_bytes"]:,} B ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
