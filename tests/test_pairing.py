#!/usr/bin/env python3
"""The pairing check with the residue witness (groth/pairing.py) on an instance with
e(A, B) e(L, gamma) e(C, delta) = 1.  A wrong s, a wrong c, a wrong slope and a false instance must be
rejected.

    python3 tests/test_pairing.py
"""
import os, random, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, miller as M
from groth.pairing import PairingCheck
from groth.sym import Sym, Num
from groth.dsl import wv, wpair, wbalanced, Tbalanced, balanced_paths
import harness

P = F.P


def instance(rng, key):
    """gamma, delta from the key; A, B, L random, C solving a b + l g + c d = 0"""
    g, d = key.randrange(1, B.R), key.randrange(1, B.R)
    a, b, l = (rng.randrange(1, B.R) for _ in range(3))
    c = (-(a * b + l * g)) * pow(d, -1, B.R) % B.R
    gamma, delta = B.g2_mul(B.G2_GEN, g), B.g2_mul(B.G2_GEN, d)
    A, Bq, L, C = B.g1_mul(B.G1_GEN, a), B.g2_mul(B.G2_GEN, b), B.g1_mul(B.G1_GEN, l), B.g1_mul(B.G1_GEN, c)
    return gamma, delta, [(A, Bq), (L, gamma), (C, delta)]


def point_words(pairs):
    (A, Bq), (L, _), (C, _) = pairs
    return [F.to_mont(v) for v in (A[0], A[1], Bq[0].c0, Bq[0].c1, Bq[1].c0, Bq[1].c1, C[0], C[1], L[0], L[1])]


def run_program(pc, pw, c, ci, sel, hints):
    V = lambda w: F.Val(w, F.WORD_MAX)
    return pc.program((V(pw[0]), V(pw[1])), tuple(V(x) for x in pw[2:6]), (V(pw[6]), V(pw[7])), (V(pw[8]), V(pw[9])),
                      [V(x) for x in c], [V(x) for x in ci], sel, hints)


def main():
    rng = random.Random(int(os.environ.get('SEED', '5')))
    gamma, delta, pairs = instance(rng, random.Random(11))
    assert B.multi_pairing(pairs).is_one()
    bnd = M.bounds()
    hints = M.hint_words(pairs[0][1])
    pw = point_words(pairs)
    # prover
    be = Num(); fp = F.Fp(be)
    pc = PairingCheck(fp, gamma, delta, b=bnd)
    t0 = time.time()
    cw, ciw, s = pc.witness(pairs)
    print(f'residue witness: s = {s} ({time.time() - t0:.1f}s)')
    # numeric model
    run_program(pc, pw, cw, ciw, [s >> 1, s & 1], hints)
    print('numeric model ok')
    # symbolic: witness = ((points, (c, c^-1)), ((s1, s0), hints))
    nh = M.N_STEPS
    be = Sym(256 * 34 + 2 + 512 * nh); fp = F.Fp(be)
    pc = PairingCheck(fp, gamma, delta, b=bnd)
    pts = [F.Val(be.proj('OO' + p, 256), F.WORD_MAX) for p in balanced_paths(10)]
    c = [F.Val(be.proj('OIO' + p, 256), F.WORD_MAX) for p in balanced_paths(12)]
    ci = [F.Val(be.proj('OII' + p, 256), F.WORD_MAX) for p in balanced_paths(12)]
    sel, hints_root = be.proj('IOH', 2), be.proj('IIH', 512 * nh)
    body = pc.program((pts[0], pts[1]), tuple(pts[2:6]), (pts[6], pts[7]), (pts[8], pts[9]), c, ci, sel, hints_root)
    w256 = ['2^256']
    ty = (f'(({Tbalanced(w256 * 10)} * ({Tbalanced(w256 * 12)} * {Tbalanced(w256 * 12)})) * '
          f'((2 * 2) * {Tbalanced(["(2^256 * 2^256)"] * nh)}))')
    be.em.define('w_in', 'witness', f'_ -> {ty}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * 34 + 2 + 512 * nh) + body.c
    text = be.em.text()

    def witness(points, cw, ciw, s, hw):
        return {'w_in': {'p': [{'p': [wbalanced([wv(256, w) for w in points]),
                                      {'p': [wbalanced([wv(256, w) for w in cw]), wbalanced([wv(256, w) for w in ciw])]}]},
                               {'p': [{'p': [{'bit': s >> 1}, {'bit': s & 1}]},
                                      wbalanced([wpair(wv(256, lx), wv(256, ly)) for lx, ly in hw])]}]}}
    bad_c = list(cw); bad_c[0] = (bad_c[0] + 1) % (1 << 256)
    bad_hint = [list(h) for h in hints]; bad_hint[40][1] ^= 1
    # a non-satisfying instance: C + G1 with the witness of the satisfying one
    (A, Bq), (L, _), (C, _) = pairs
    bad_pts = point_words([(A, Bq), (L, gamma), (B.g1_add(C, B.G1_GEN), delta)])
    t0 = time.time()
    results = harness.run('pairing', text, witness(pw, cw, ciw, s, hints), multi=[
        witness(pw, cw, ciw, (s + 1) % 3, hints), witness(pw, bad_c, ciw, s, hints), witness(pw, cw, ciw, s, bad_hint),
        witness(bad_pts, cw, ciw, s, hints)])
    seconds = time.time() - t0
    r = harness.expect_ok(results[0], 'pairing')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for bad, label in zip(results[1:], ('wrong s', 'wrong c', 'wrong hint', 'bad instance')):
        assert not bad.get('ok') and bad.get('stage') in ('exec', 'finalize'), (label, bad)
        print(f'{label:14} rejected as expected')
    print(f'pairing check cost {r["cost"]:,}  estimate {estimate:,}  ok  prog {r["program_bytes"]} B  '
          f'cells {r.get("cells")}  text {len(text) // 1024} KB  ({seconds:.0f}s for five runs)')
    m = pc.m
    rows = [(name, m.costs[name]) for name in ('SQRN', 'DMULN', 'LM1', 'LM2', 'LMN', 'BSTEP_DBL', 'BSTEP_ADD', 'ITER_D', 'ITER_F', 'ITER_A')]
    rows += [('setup (normalisation, on-curve checks, c c^-1 = 1)', pc.parts['setup']), ('loop (88 steps)', pc.parts['loop']),
             ('final (Frobenius factors, three products, comparison)', pc.parts['final']), ('whole program', r['cost'])]
    for name, cst in rows:
        print(f'{name:42} {cst:>12,}')


if __name__ == '__main__':
    main()
