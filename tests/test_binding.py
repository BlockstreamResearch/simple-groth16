#!/usr/bin/env python3
"""The transaction binding (groth/groth16 with depth > 0, groth/core/binding.py): the public input is the
Merkle root of the sighash and three values.  The harness runs programs in SimplicityHL's dummy
environment, whose sig_all_hash is DUMMY_SIGHASH (`deploy sighash dummy`).  A wrong sibling and a proof
for another sighash must be rejected.

Then a shorter signal (signal_bits): the low 184 bits of a root, the shortest the generator allows.  Its
verifier, with tables for those bits only, must accept the proof at the predicted cost, within its budget
(which is why there is a shortest), and reject a wrong sibling, another sighash, and the input with a bit
above its 184, sealed again: the tables do not read that bit, so the pairing check holds and only the
binding rejects it.  The numeric model checks other widths and the binding by the input.

    python3 tests/test_binding.py
"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import binding
from groth.core import bn254 as B
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core.budget import budget_ok
from groth.core.dsl import CheckFailed
from groth.core.sym import Num
from groth.groth16 import Groth16

DUMMY_SIGHASH = bytes.fromhex('9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a')


def main():
    values = [91, 7, 13]  # the public values of the circuit, committed with the sighash
    leaves = [DUMMY_SIGHASH] + values
    depth = binding.depth_of(len(leaves))
    root = binding.public_signal(binding.root(leaves))
    sibs = binding.siblings(leaves)
    assert len(sibs) == depth == 2 and binding.bound_signal(DUMMY_SIGHASH, sibs) == root
    vk, proof, inputs = B.groth16_instance(1, seed=11, inputs=[root])
    assert B.groth16_verify(vk, proof, inputs)
    bnd = PC.bounds()
    g = Groth16(F.Fp(Num()), vk, b=bnd, depth=depth)
    wit = g.witness(proof, inputs, DUMMY_SIGHASH, sibs)
    assert wit is not None and g.witness(proof, inputs, bytes(32), sibs) is None, 'the siblings must give the input'
    g.verify(g.num_input(wit))
    print('numeric model ok')
    text, g, estimate = Groth16.compile(vk, depth=depth, b=bnd)
    # a wrong sibling; the witness of the same tree with another sighash (the root the program computes differs)
    bad_sib = dict(wit)
    bad_sib['siblings'] = [wit['siblings'][0] ^ 1, wit['siblings'][1]]
    other = [bytes(32)] + values
    other_root = binding.public_signal(binding.root(other))
    vk2, proof2, inputs2 = B.groth16_instance(1, seed=11, inputs=[other_root])
    bad_tx = Groth16(F.Fp(Num()), vk2, b=bnd, depth=depth).witness(proof2, inputs2, bytes(32), binding.siblings(other))
    assert bad_tx is not None
    t0 = time.time()
    results = harness.run(
        'binding', text, g.witness_value(wit), multi=[g.witness_value(bad_sib), g.witness_value(bad_tx)]
    )
    r = harness.expect_ok(results[0], 'binding')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for bad, label in zip(results[1:], ('wrong sibling', 'other sighash')):
        harness.expect_rejected(bad, label)
        print(f'{label:15} rejected as expected')
    print(
        f'bound verifier (depth {depth}) cost {r["cost"]:,} mWU, binding {g.parts["binding"]:,} mWU, '
        f'program {r["program_bytes"]} B, witness {r["witness_bytes"]} B ({time.time() - t0:.0f}s)'
    )

    short_signal(bnd, r['cost'])


def refused(f, expect):
    try:
        f()
    except CheckFailed as e:
        assert expect in str(e), (expect, str(e))
        return
    raise AssertionError(f'not refused: {expect}')


def short_instance(bits, bnd, sighash_input=False):
    """(generator, witness, the witness with a bit above the signal's bits set and sealed again) for a
    signal of `bits` bits: the low bits of the root of the sighash and one value, or of the sighash."""
    sibs = [] if sighash_input else binding.siblings([DUMMY_SIGHASH, 21])
    x = binding.bound_signal(DUMMY_SIGHASH, sibs, bits)
    assert x < 2**bits and x == binding.bound_signal(DUMMY_SIGHASH, sibs) % 2**bits
    vk, proof, inputs = B.groth16_instance(1, seed=12, inputs=[x])
    g = Groth16(F.Fp(Num()), vk, b=bnd, depth=len(sibs), sighash_input=sighash_input, signal_bits=bits)
    wit = g.witness(proof, inputs, DUMMY_SIGHASH, sibs)
    assert wit is not None and g.witness(proof, inputs, bytes(32), sibs) is None
    g.verify(g.num_input(wit))
    # a verifier of another width expects another signal
    other = 253 if bits != 253 else 200
    assert (
        Groth16(F.Fp(Num()), vk, b=bnd, depth=len(sibs), sighash_input=sighash_input, signal_bits=other).witness(
            proof, inputs, DUMMY_SIGHASH, sibs
        )
        is None
    )
    high = g.pc.prover.seal(wit['values'], [x + (1 << bits)])
    high.update(scalars=[x + (1 << bits)], sighash=wit['sighash'], siblings=wit.get('siblings'))
    refused(lambda: g.verify(g.num_input(high)), 'transaction binding failed')
    return vk, g, wit, high


def short_signal(bnd, full_cost):
    for bits in (200, 248):
        short_instance(bits, bnd)
    short_instance(binding.MIN_BITS, bnd, sighash_input=True)
    for bad in (0, 128, 160, 176, 190, 252, 254, 256):
        refused(lambda bad=bad: binding.check_bits(bad), 'a signal has')
    print('numeric model ok for signals of 184, 200 and 248 bits; a bit above the signal is rejected')
    bits = binding.MIN_BITS
    vk, g, wit, high = short_instance(bits, bnd)
    text, g, estimate = Groth16.compile(vk, depth=1, b=bnd, signal_bits=bits)
    assert [w for w in PC.windows([bits]) if w[1] + w[2] > bits] == [] and len(PC.windows([bits])) == bits // 8
    bad_sib = dict(wit, siblings=[wit['siblings'][0] ^ 1])
    x2 = binding.bound_signal(bytes(32), binding.siblings([bytes(32), 21]), bits)
    vk2, proof2, inputs2 = B.groth16_instance(1, seed=12, inputs=[x2])
    bad_tx = Groth16(F.Fp(Num()), vk2, b=bnd, depth=1, signal_bits=bits).witness(
        proof2, inputs2, bytes(32), binding.siblings([bytes(32), 21])
    )
    assert bad_tx is not None
    t0 = time.time()
    bad = [bad_sib, bad_tx, high]
    results = harness.run('binding_short', text, g.witness_value(wit), multi=[g.witness_value(w) for w in bad])
    r = harness.expect_ok(results[0], f'a signal of {bits} bits')
    assert r['cost'] == estimate < full_cost, (r['cost'], estimate, full_cost)
    # the shortest signal is the one whose one-input verifier the budget still pays for
    assert budget_ok(r['cost'], r['program_bytes'], r['witness_bytes']), r
    for res, label in zip(results[1:], ('wrong sibling', 'other sighash', 'a bit above the signal')):
        harness.expect_rejected(res, label)
        print(f'{label:22} rejected as expected')
    print(
        f'bound verifier with a signal of {bits} bits (depth 1) cost {r["cost"]:,} mWU, binding '
        f'{g.parts["binding"]:,} mWU, program {r["program_bytes"]} B, witness {r["witness_bytes"]} B '
        f'({time.time() - t0:.0f}s)'
    )


if __name__ == '__main__':
    main()
