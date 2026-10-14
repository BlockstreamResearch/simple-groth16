#!/usr/bin/env python3
"""The whole verifier (groth/groth16.py) on a synthetic key.  A wrong public input and a tampered proof
must be rejected, and the budget of the input must cover the cost (with padding if needed).

    python3 tests/test_groth16.py             # one public input
    INPUTS=2 python3 tests/test_groth16.py    # two
"""
import os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, pairing as PC
from groth.groth16 import Groth16
from groth.sym import Num
import harness


def main():
    n = int(os.environ.get('INPUTS', '1'))
    w = int(os.environ.get('W', '8'))
    vk, proof, inputs = B.groth16_instance(n, seed=int(os.environ.get('SEED', '7')))
    assert B.groth16_verify(vk, proof, inputs)
    bnd = PC.bounds()
    # prover
    g = Groth16(F.Fp(Num()), vk, w, b=bnd)
    t0 = time.time()
    wit = g.witness(proof, inputs)
    print(f'witness in {time.time() - t0:.1f}s: {len(wit["msm_hints"])} MSM slopes, {len(wit["leaves"])} leaves, {len(wit["q"])} words of Q')
    assert g.witness((proof[0], proof[1], B.g1_add(proof[2], B.G1_GEN)), inputs) is None, 'a wrong proof has no witness'
    # numeric model
    g.verify(g.num_input(wit))
    print('numeric model ok')
    # the program
    text, g, estimate = Groth16.compile(vk, w, b=bnd)
    text_kb = len(text) // 1024
    # rejections: a wrong public input (with the hints of the right one), a tampered proof (C + G1, same witness)
    bad_input = dict(wit); bad_input['scalars'] = [(inputs[0] + 1) % B.R] + inputs[1:]
    bad_proof = dict(wit)
    C2 = B.g1_add(proof[2], B.G1_GEN)
    bad_proof['points'] = wit['points'][:6] + [F.to_mont(C2[0]), F.to_mont(C2[1])]
    wv = lambda gen, wt: {'w_in': gen.witness_value(wt)}
    t0 = time.time()
    results = harness.run(f'groth16_{n}', text, wv(g, wit), multi=[wv(g, bad_input), wv(g, bad_proof)])
    seconds = time.time() - t0
    r = harness.expect_ok(results[0], 'groth16')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for bad, label in zip(results[1:], ('wrong input', 'tampered proof')):
        assert not bad.get('ok') and bad.get('stage') in ('exec', 'finalize'), (label, bad)
        print(f'{label:15} rejected as expected')
    print(f'groth16 ({n} input{"s" if n > 1 else ""}, w = {w}) cost {r["cost"]:,}  estimate {estimate:,}  ok  '
          f'prog {r["program_bytes"]} B  witness {r["witness_bytes"]} B  cells {r.get("cells"):,}  text {text_kb} KB  ({seconds:.0f}s for three runs)')
    rows = [(f'MSM ({n} input{"s" if n > 1 else ""}, {g.nwin} windows of {w} bits each)', g.parts['msm']),
            ('pairing check: setup', g.parts['setup']), ('pairing check: loop', g.parts['loop']), ('pairing check: final', g.parts['final']),
            ('range checks', g.parts['range checks']), ('whole program', r['cost'])]
    for name, cst in rows:
        print(f'{name:48} {cst:>12,}')
    # the budget of the input (program + witness bytes + 50, times 1000) must cover the cost; pad if not
    pad = Groth16.padding(r['cost'], r['program_bytes'], r['witness_bytes'])
    if pad:
        text, g, estimate = Groth16.compile(vk, w, pad_blocks=pad, b=bnd)
        r = harness.expect_ok(harness.run(f'groth16_{n}_padded', text, wv(g, wit)), 'groth16 padded')
        assert r['cost'] == estimate, (r['cost'], estimate)
    assert Groth16.budget_ok(r['cost'], r['program_bytes'], r['witness_bytes']), 'budget'
    weight = r['program_bytes'] + r['witness_bytes'] + 33 + 9
    print(f'{pad} padding blocks: cost {r["cost"]:,} mWU, program {r["program_bytes"]:,} B + witness {r["witness_bytes"]:,} B: '
          f'the input weighs about {weight:,} WU and its budget covers the cost')

if __name__ == '__main__':
    main()
