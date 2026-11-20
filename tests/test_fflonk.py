#!/usr/bin/env python3
"""The fflonk verifier (groth/fflonk/verifier.py) on the snarkjs 0.7.6 proofs in examples/fflonk.

    python3 tests/test_fflonk.py [quick] [keccak|sha256]

The plain-Python port (groth/fflonk/reference.py) accepts each proof in its transcript's mode and
rejects it in the other, and rejects a tampered evaluation or public input; the opening the program is
generated from agrees with it, and no two witness nodes hold the same value.  Then, for each mode (or the
one given), the program bound to the transaction runs in hand: the honest witness at the estimated cost,
the witness padded for a larger program, whose budget must cover its cost, and tampered witnesses, which
must be rejected: an evaluation, a challenge word, a public input, an inverse hint, a column word, the
fixed-base scalar, an MSM hint, either point of the pairing check, and, in Keccak mode, a valid proof for
another sighash.  `quick` skips the programs.

The padding also runs as a program of its own: blocks of zeros pass at the predicted cost whichever groups
are taken, each block at the same cost, and a taken group with a word that is not 0 is rejected: 1, or
one of secp256k1's two primes, which one of the pair's two zero tests accepts.

The proofs bind the harness's dummy sighash (DUMMY_SIGHASH): circuits/multiplier_fflonk.circom with
a = 3, b = 7, made by tools/demo.py (the SHA-256 one by tools/snarkjs_sha256.mjs).
"""

import copy
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import bn254 as B
from groth.core import pairing_fixed as PF
from groth.core import snarkjs
from groth.core.dsl import CheckFailed
from groth.core.fp import N_SECP, P_SECP, Fp
from groth.core.sym import Num, Sym
from groth.fflonk import reference as ref
from groth.fflonk import verifier as FF

EX = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'examples', 'fflonk')
DUMMY_SIGHASH = bytes.fromhex('9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a')
ARGS = sys.argv[1:]
QUICK = 'quick' in ARGS
MODES = [m for m in ref.MODES if m in ARGS] or list(ref.MODES)


def load(name):
    with open(os.path.join(EX, name)) as f:
        return json.load(f)


VK = snarkjs.fflonk_key(load('verification_key.json'))
PUB = [int(x) for x in load('public.json')]
PROOFS = {m: snarkjs.fflonk_proof(load(f'proof_{m}.json')) for m in ref.MODES}


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
        g = FF.Fflonk(Fp(Num()), VK, m, True, PF.bounds())
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
    flip = lambda i: lambda w2: w2['pairing']['points'].__setitem__(i, w2['pairing']['points'][i] ^ 1)
    case("the pairing's point P1", flip(1))  # -(A1 - C0): no longer the MSM's result
    case("the pairing's point P2", flip(2))  # W2: no longer on the curve
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
        other = snarkjs.fflonk_proof(load('proof_keccak_other_sighash.json'))
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
    budget = (rp['program_bytes'] + rp['witness_bytes'] + 33 + 9 + 50) * 1000  # as budget.budget_ok counts it
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


def padding():
    """The padding alone, as a program whose witness nodes are the selector and the groups."""
    be = Sym(0)
    pad = FF.Padding(be)
    body = pad.program()
    be.em.define('main', body.t)
    cost = lambda blocks: body.c - pad.saved(blocks)
    # a block costs the same in every group: its checks, and its witness node read once (2 mWU per bit)
    per_block = [c / 2**k for k, c in enumerate(pad.group_cost)]
    assert max(per_block) - min(per_block) < 500 and max(per_block) < 32_000, per_block

    def value(blocks, words=(), sel=None):
        """The witness of `blocks` blocks; words: (group, index, value) for each word of a group to change."""
        v = FF.Padding.value(blocks)
        if sel is not None:
            v['wpsel'] = {'w': f'{sel:04x}'}
        for k, i, x in words:
            node = v[f'wpad{k}'] = copy.deepcopy(v[f'wpad{k}'])
            n = 16 << k
            while n > 1:  # the i-th of the node's n words
                n //= 2
                node, i = node['p'][i // n], i % n
            node['w'] = f'{x:064x}'
        return v

    good = [0, 1, 0b101010101, 0b010101010, 2**FF.PAD_GROUPS - 1]
    bad = {
        'a word of 1': value(1, [(0, 0, 1)]),
        'a second word of 1': value(1, [(0, 1, 1)]),
        'a word of p_s': value(1, [(0, 0, P_SECP)]),
        # both words of a pair: equal, and 0 modulo one prime, so only the test modulo the other rejects it
        'a pair of words p_s': value(1, [(0, 2, P_SECP), (0, 3, P_SECP)]),
        'a pair of words n_s': value(1, [(0, 14, N_SECP), (0, 15, N_SECP)]),
        'the last word of a group of 8': value(8, [(3, 127, 1)]),
        'a pair of words p_s in a group of 256': value(256, [(8, 2048, P_SECP), (8, 2049, P_SECP)]),
        'a selector above its 9 bits': value(1, sel=0x0201),
    }
    name = f'padding_{MODES[0]}'  # the two modes may run side by side (make -j): a file name for each
    results = harness.run(name, be.em.text(), value(good[0]), multi=[value(b) for b in good[1:]] + list(bad.values()))
    for blocks, res in zip(good, results):
        r = harness.expect_ok(res, f'padding, {blocks} blocks')
        assert r['cost'] == cost(blocks), (blocks, r['cost'], cost(blocks))
    for label, res in zip(bad, results[len(good) :]):
        harness.expect_rejected(res, f'padding: {label}')
    # a changed word in a group that is not taken is pruned with it
    r = harness.expect_ok(harness.run(name, be.em.text(), value(1, [(3, 5, 1)])), 'padding, a group not taken')
    assert r['cost'] == cost(1)
    print(
        f'padding: {per_block[0]:,.0f} mWU a block in a group of 1, {per_block[-1]:,.0f} in a group of 256; '
        f'{len(bad)} changed witnesses rejected'
    )


def main():
    reference()
    padding()
    if QUICK:
        return
    for m in MODES:
        program(m)
    print('all ok')


if __name__ == '__main__':
    main()
