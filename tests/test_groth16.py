#!/usr/bin/env python3
"""The whole verifier (groth/groth16/verifier.py) on a synthetic key.  A wrong public input and a tampered proof
must be rejected, with the challenges as they were and sealed again (anyone can recompute r, Q and z),
and so must an input above r that the tables alone cannot tell from the right one.  The budget of the
input must cover the cost.

    python3 tests/test_groth16.py             # one public input
    INPUTS=2 python3 tests/test_groth16.py    # two
"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import bn254 as B
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core.budget import budget_ok
from groth.core.dsl import CheckFailed
from groth.core.sym import Num
from groth.groth16 import Groth16


def values_for(g, proof, xs):
    """The prover's values for the inputs xs, which need not be below r: Prover.witness without its range
    check (pairing.py)."""
    pr = g.pc.prover
    A, Bp, C = proof
    pairs = [(B.g1_neg(A), Bp), (C, g.vk['delta'])]
    c, _ = B.residue_witness(pr.product(pairs, xs))
    millers = PC.miller_values(pairs, c, pr.factors(xs))
    return {
        'P': pairs[0][0],
        'B': Bp,
        'C': C,
        'ac': PC.compress(PC.easy(c)),
        'lam': [lam for lam, _ in PC.slopes(Bp)],
        'a': [PC.compress(PC.easy(f)) if PC.COMMIT[i] else None for i, f in enumerate(millers)],
        'win': {s: [pr.tables[(s, w)][pr.digit(xs, w)] for w in wins] for s, wins in pr.plan.items()},
        'tau': pr.taus[pr.end_digit(xs)],
    }


def sealed(g, values, xs, holds):
    """The witness of the values sealed for the inputs xs; `holds`: whether the relations hold, as the prover
    computes them from the values (with the window factors in the values, not those the inputs select)."""
    pr = g.pc.prover
    try:
        pr.seal(values, xs, check=True)
        assert holds, 'the relations hold'
    except CheckFailed:
        assert not holds, 'the relations do not hold'
    w = pr.seal(values, xs, check=False)
    w['scalars'] = list(xs)
    return w


def main():
    n = int(os.environ.get('INPUTS', '1'))
    vk, proof, inputs = B.groth16_instance(n, seed=int(os.environ.get('SEED', '7')))
    assert B.groth16_verify(vk, proof, inputs)
    bnd = PC.bounds()
    # prover
    gn = Groth16(F.Fp(Num()), vk, b=bnd)
    t0 = time.time()
    wit = gn.witness(proof, inputs)
    print(f'witness in {time.time() - t0:.1f}s: {len(wit["leaves"])} leaves, {len(wit["q"])} words of Q')
    assert gn.witness((proof[0], proof[1], B.g1_add(proof[2], B.G1_GEN)), inputs) is None, (
        'a wrong proof has no witness'
    )
    # numeric model
    gn.verify(gn.num_input(wit))
    print('numeric model ok')
    # the program
    t0 = time.time()
    text, g, estimate = Groth16.compile(vk, b=bnd)
    print(f'program generated in {time.time() - t0:.1f}s')
    text_kb = len(text) // 1024
    # rejections.  Not sealed again (the challenge rejects them): a wrong public input with the hints of the
    # right one, a tampered proof (C + G1).  Sealed again, so that the challenges pass: the wrong input (the
    # program's tables give other factors than the values', so the identity rejects it), the tampered proof
    # (its relations do not hold: the identity), the input plus 2^254 (the tables read bits 0..253, the
    # identity holds: only the range check rejects it) and, when it fits in 254 bits, the input plus r (the
    # same factors; only the range check again).
    vals, x0 = wit['values'], inputs[0]
    wrong = [(x0 + 1) % B.R] + inputs[1:]
    C2 = B.g1_add(proof[2], B.G1_GEN)
    bad_input = dict(wit, scalars=wrong)
    bad_proof = dict(wit, points=wit['points'][:6] + [F.to_mont(C2[0]), F.to_mont(C2[1])])
    bad = [
        ('wrong input', bad_input),
        ('tampered proof', bad_proof),
        ('wrong input, sealed', sealed(gn, vals, wrong, True)),
        ('tampered proof, sealed', sealed(gn, dict(vals, C=C2), inputs, False)),
        ('input + 2^254, sealed', sealed(gn, vals, [x0 + 2**254] + inputs[1:], True)),
    ]
    if x0 + B.R < 2**254:
        alias = [x0 + B.R] + inputs[1:]
        bad.append(('input + r, sealed', sealed(gn, values_for(gn, proof, alias), alias, True)))
    # the numeric model runs the pairing check (the identity, then the challenges) before the range checks,
    # so it reports which check rejects: the identity for the first four, only the range check for the rest
    for label, w in bad:
        expect = 'range check' if label.startswith('input +') else 'verify failed'
        try:
            gn.verify(gn.num_input(w))
            raise AssertionError(f'the numeric model accepted the {label}')
        except CheckFailed as e:
            assert str(e) == expect, (label, str(e), expect)
    t0 = time.time()
    results = harness.run(f'groth16_{n}', text, g.witness_value(wit), multi=[g.witness_value(w) for _, w in bad])
    seconds = time.time() - t0
    r = harness.expect_ok(results[0], 'groth16')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for (label, _), res in zip(bad, results[1:]):
        harness.expect_rejected(res, label)
        print(f'{label:24} rejected as expected')
    print(
        f'groth16 ({n} input{"s" if n > 1 else ""}) cost {r["cost"]:,}  estimate {estimate:,}  ok  '
        f'prog {r["program_bytes"]} B  witness {r["witness_bytes"]} B  cells {r.get("cells"):,}  text {text_kb} KB  ({seconds:.0f}s for {len(results)} runs)'
    )
    rows = [
        ('pairing check: setup', g.parts['setup']),
        ('pairing check: loop', g.parts['loop']),
        ('pairing check: final', g.parts['final']),
        ('range checks', g.parts['range checks']),
        ('whole program', r['cost']),
    ]
    for name, cst in rows:
        print(f'{name:48} {cst:>12,}')
    # the budget of the input (program + witness bytes + 50, times 1000) must cover the cost
    assert budget_ok(r['cost'], r['program_bytes'], r['witness_bytes']), 'budget'
    weight = r['program_bytes'] + r['witness_bytes'] + 33 + 9
    print(
        f'cost {r["cost"]:,} mWU, program {r["program_bytes"]:,} B + witness {r["witness_bytes"]:,} B: '
        f'the input weighs about {weight:,} WU and its budget covers the cost'
    )


if __name__ == '__main__':
    main()
