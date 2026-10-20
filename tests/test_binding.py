#!/usr/bin/env python3
"""The transaction binding (groth/groth16.py with depth > 0, groth/merkle.py): the public input is the
Merkle root of the sighash and three values.  The harness runs programs in SimplicityHL's dummy
environment, whose sig_all_hash is DUMMY_SIGHASH (`deploy sighash dummy`).  A wrong sibling and a proof
for another sighash must be rejected.

    python3 tests/test_binding.py
"""
import os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, pairing as PC, merkle
from groth.groth16 import Groth16
from groth.sym import Num
import harness

DUMMY_SIGHASH = bytes.fromhex('9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a')


def main():
    values = [91, 7, 13] # the public values of the circuit, committed with the sighash
    leaves = [DUMMY_SIGHASH] + values
    depth = merkle.depth_of(len(leaves))
    root = merkle.public_signal(merkle.root(leaves))
    sibs = merkle.siblings(leaves)
    assert len(sibs) == depth == 2 and Groth16.root(DUMMY_SIGHASH, sibs) == root
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
    bad_sib = dict(wit); bad_sib['siblings'] = [wit['siblings'][0] ^ 1, wit['siblings'][1]]
    other = [bytes(32)] + values
    other_root = merkle.public_signal(merkle.root(other))
    vk2, proof2, inputs2 = B.groth16_instance(1, seed=11, inputs=[other_root])
    bad_tx = Groth16(F.Fp(Num()), vk2, b=bnd, depth=depth).witness(proof2, inputs2, bytes(32), merkle.siblings(other))
    assert bad_tx is not None
    wv = lambda wt: g.witness_value(wt)
    t0 = time.time()
    results = harness.run('binding', text, wv(wit), multi=[wv(bad_sib), wv(bad_tx)])
    r = harness.expect_ok(results[0], 'binding')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for bad, label in zip(results[1:], ('wrong sibling', 'other sighash')):
        assert not bad.get('ok') and bad.get('stage') in ('exec', 'finalize'), (label, bad)
        print(f'{label:15} rejected as expected')
    print(f'bound verifier (depth {depth}) cost {r["cost"]:,} mWU, binding {g.parts["binding"]:,} mWU, '
          f'program {r["program_bytes"]} B, witness {r["witness_bytes"]} B ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
