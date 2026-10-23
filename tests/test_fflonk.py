#!/usr/bin/env python3
"""The fflonk verifier (groth/fflonk.py) on the snarkjs 0.7.6 proofs in examples/fflonk.

    python3 tests/test_fflonk.py [quick] [keccak|sha256]

The plain-Python port (fflonk_ref.py) accepts each proof in its transcript's mode and rejects it in the
other, and a tampered evaluation; the opening the program is generated from agrees with it.  Then, for
each mode (or the one given), the program bound to the transaction runs in hand: the honest witness at
the estimated cost, and tampered witnesses, which must be rejected: an evaluation, a challenge word, a
public input, an inverse hint, a column word, the fixed-base scalar, an MSM hint, the pairing's G1 slot
or its G2 slot, and a valid proof for another sighash.  `quick` skips the programs.

The proofs bind the harness's dummy sighash (DUMMY_SIGHASH): circuits/multiplier_fflonk.circom with
a = 3, b = 7, made by tools/circom_demo.py (the SHA-256 one by tools/snarkjs_sha256.mjs).
"""

import copy
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth import bn254 as B
from groth import fflonk as FF
from groth import fflonk_ref as ref
from groth import pairing as PC
from groth.dsl import CheckFailed
from groth.fp import Fp
from groth.sym import Num

EX = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'examples', 'fflonk')
DUMMY_SIGHASH = bytes.fromhex('9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a')
ARGS = sys.argv[1:]
QUICK = 'quick' in ARGS
MODES = [m for m in ref.MODES if m in ARGS] or list(ref.MODES)


def load(name):
    with open(os.path.join(EX, name)) as f:
        return json.load(f)


VK = ref.load_vk(load('verification_key.json'))
PUB = [int(x) for x in load('public.json')]
PROOFS = {m: ref.load_proof(load(f'proof_{m}.json')) for m in ref.MODES}


def reference():
    for m in ref.MODES:
        assert ref.verify(m, VK, PROOFS[m], PUB)['ok'], m
        other = 'sha256' if m == 'keccak' else 'keccak'
        assert not ref.verify(other, VK, PROOFS[m], PUB)['ok'], m
        bad = dict(PROOFS[m])
        bad['a'] = (bad['a'] + 1) % B.R
        assert not ref.verify(m, VK, bad, PUB)['ok'], m
        assert not ref.verify(m, VK, PROOFS[m], [PUB[0], PUB[1], PUB[2] + 1])['ok'], m
        w = FF.witness(VK, PROOFS[m], PUB, m)  # checks the opening against the port, and the MSM against A1
        assert w is not None and len(w['inv']) == FF.N_INV_FIXED + max(1, VK['nPublic'])
        # no two witness nodes hold the same value: the encoding of a program with its witness must share
        # every repeated node, and deploy encodes the unpruned program, where they would be two
        g = FF.Fflonk(Fp(Num()), VK, m, True, PC.bounds())
        values = [
            json.dumps(v, sort_keys=True) for v in g.witness_value(g.witness(PROOFS[m], PUB, DUMMY_SIGHASH)).values()
        ]
        assert len(values) == len(set(values)), 'two witness nodes with the same value'

    print('reference: each proof verifies in its mode only; the opening and the MSM agree with the port')


def tampered(g, w):
    """(label, witness) pairs, each of which the program must reject."""
    out = []

    def case(label, fn):
        w2 = copy.deepcopy(w)
        fn(w2)
        out.append((label, w2))

    case('an evaluation', lambda w2: w2['ev'].__setitem__(8, (w2['ev'][8] + 1) % B.R))
    case('a challenge word', lambda w2: w2['ch'].__setitem__(0, (w2['ch'][0] + 1) % B.R))
    case('a public input', lambda w2: w2['pub'].__setitem__(2, w2['pub'][2] + 1))
    case('an inverse hint', lambda w2: w2['inv'].__setitem__(3, (w2['inv'][3] + 1) % B.R))
    case('a column word', lambda w2: w2['cols'].__setitem__(1, w2['cols'][1] ^ 4))
    case('the fixed-base scalar', lambda w2: w2.__setitem__('v', (w2['v'] + 1) % B.R))
    case('an MSM hint', lambda w2: w2['var']['steps'][40][1].__setitem__(0, (w2['var']['steps'][40][1][0] + 1) % B.P))
    case('the G1 slot', lambda w2: w2['pairing']['points'].__setitem__(1, w2['pairing']['points'][1] ^ 1))
    g2 = B.g2_mul(B.G2_GEN, 5)
    case(
        'the G2 slot',
        lambda w2: w2['pairing']['points'].__setitem__(
            slice(2, 6), [PC.to_mont(x) for x in (g2[0].c0, g2[0].c1, g2[1].c0, g2[1].c1)]
        ),
    )
    return out


def spec_bytes(spec):
    """The bytes of a witness value spec."""
    if 'w' in spec:
        return len(spec['w']) // 2
    return sum(spec_bytes(x) for x in spec['p'])


def program(mode):
    t0 = time.time()
    text, g, estimate = FF.Fflonk.compile(VK, mode, bind=True)
    w = g.witness(PROOFS[mode], PUB, DUMMY_SIGHASH)
    try:
        g.witness(PROOFS[mode], PUB, bytes(32))
        raise AssertionError('a witness for the wrong sighash')
    except CheckFailed:
        pass
    bad = tampered(g, w)
    if mode == 'keccak':  # a valid proof, for another transaction
        other = ref.load_proof(load('proof_keccak_other_sighash.json'))
        pub2 = [int(x) for x in load('public_other_sighash.json')]
        bad.append(('another sighash', g.witness(other, pub2, bytes(32))))
    # padding as if the pruned program were 50 kB, less than it is: more padding than it needs, so the
    # budget covers the cost
    plain = g.witness_value(w)
    # the witness without padding: the groups not taken are pruned, with their values
    unpadded = sum(spec_bytes(v) for k, v in plain.items() if not k.startswith('wpad'))
    pad = g.pad_for(estimate, 50_000, unpadded)
    results = harness.run(
        f'fflonk_{mode}',
        text,
        plain,
        multi=[g.witness_value(w, pad)] + [g.witness_value(x) for _, x in bad],
        timeout=7200,
    )
    r = harness.expect_ok(results[0], f'fflonk {mode}')
    assert r['cost'] == g.cost(estimate, 0), (r['cost'], g.cost(estimate, 0))
    rp = harness.expect_ok(results[1], f'fflonk {mode}, padded')
    budget = (rp['program_bytes'] + rp['witness_bytes'] + 33 + 9 + 50) * 1000  # as Groth16.budget_ok counts it
    assert rp['cost'] == g.cost(estimate, pad) <= budget, (rp['cost'], g.cost(estimate, pad), budget)
    for (label, _), res in zip(bad, results[2:]):
        harness.expect_rejected(res, f'fflonk {mode}: {label}')
        print(f'  {label:22} rejected as expected')
    parts = ', '.join(f'{k} {v / 1e6:.1f} M' for k, v in g.parts.items() if k != 'padding')
    print(
        f'fflonk {mode}: cost {r["cost"]:,} mWU ({parts}), program {r["program_bytes"]:,} B, '
        f'witness {r["witness_bytes"]:,} B, cells {r["cells"]:,}; with {pad} blocks of padding: cost '
        f'{rp["cost"]:,} mWU, budget {budget:,} mWU ({time.time() - t0:.0f}s)'
    )


def main():
    reference()
    if QUICK:
        return
    for m in MODES:
        program(m)
    print('all ok')


if __name__ == '__main__':
    main()
