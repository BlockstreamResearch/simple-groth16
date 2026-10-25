#!/usr/bin/env python3
"""Verifier program from a snarkjs verification key, and witness from a snarkjs proof.

    python3 tools/groth16_snarkjs.py program verification_key.json --values N --out build/x
    python3 tools/groth16_snarkjs.py witness verification_key.json proof.json public.json --leaves leaves.json --out build/x
    python3 tools/groth16_snarkjs.py program|witness ... --sighash-input [--sighash <64 hex digits>] --out build/x

`program` writes x.simpl (then `deploy compile` makes x.uprog and `deploy address` the output to fund).
`witness` writes x.w0.json for `deploy spend`; it verifies the proof first.

--values N (N >= 0): the circuit follows circuits/public_merkle.circom with PublicMerkleRoot(N), so its
one public signal is the Merkle root of the sighash and N values, and the program binds the proof to the
spending transaction.  The witness needs --leaves, a JSON file {"sighash": "<64 hex digits>", "values":
["<decimal>", ...]}, which also gives N.

--sighash-input (in place of --values and --leaves): the circuit's first public signal is the sighash of
the spending transaction with its top three bits cleared (binding.public_signal, as for a root), which the
program compares with the transaction's, and every public signal is a verifier input (about 6.6 M mWU and
14 kB each).  For circuits that cannot compute the Merkle root, such as Noir circuits converted to R1CS
(tools/noir_r1cs.py, circuits/noir/multiplier).  `witness` needs the sighash itself (--sighash), since
the signal lacks its top three bits.

--unbound (in place of the others): every public signal is a verifier input (about 6.6 M mWU
and 14 kB each).  Nothing binds the transaction: anyone who sees a spend can reuse its witness in another
transaction to the same output, and the public inputs are whatever the spender proves.
"""

import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth.core import binding, snarkjs
from groth.core import bn254 as B
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core.dsl import CheckFailed
from groth.core.sym import Num
from groth.groth16 import Groth16


def need(ok, msg):
    """Refuse with msg unless ok.  Not an assert, so python -O keeps the check."""
    if not ok:
        sys.exit(f'groth16_snarkjs.py: {msg}')


def refusing(f, path):
    """f(the JSON at path), with a failed check (groth/core/snarkjs.py) as a refusal."""
    try:
        return f(snarkjs.load(path))
    except CheckFailed as e:
        sys.exit(f'groth16_snarkjs.py: {path}: {e}')


def load_json(path):
    with open(path) as f:
        return json.load(f)


def load_vk(path):
    return refusing(snarkjs.groth16_key, path)


def load_proof(path):
    return refusing(snarkjs.groth16_proof, path)


def load_public(path):
    return refusing(snarkjs.public_signals, path)


def load_leaves(path):
    j = load_json(path)
    sighash = bytes.fromhex(j['sighash'])
    need(len(sighash) == 32, 'the sighash is 32 bytes (64 hex digits)')
    values = [int(v) for v in j['values']]
    need(all(0 <= v < B.R for v in values), 'a value is not below r')
    return sighash, values


def binding_depth(n, n_values, leaf_values, unbound):
    """The depth of the public-signal tree: binding.depth_of(N + 1) for a bound circuit with N values
    (--values N, or the values of --leaves), 0 only with an explicit --unbound."""
    if leaf_values is not None:
        need(
            n_values is None or n_values == len(leaf_values),
            f'--values {n_values} but the leaves have {len(leaf_values)} values',
        )
        n_values = len(leaf_values)
    bound = n_values is not None
    need(bound != unbound, 'give --values N (or --leaves) or --sighash-input for a bound circuit, or --unbound')
    if not bound:
        return 0
    need(n_values >= 0, '--values is at least 0')
    need(n == 1, f'a bound circuit has one public signal, the key has {n}')
    return binding.depth_of(n_values + 1)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['program', 'witness'])
    ap.add_argument('files', nargs='+', help='verification_key.json [proof.json public.json]')
    ap.add_argument('--out', required=True)
    ap.add_argument('--values', type=int, help='N: the circuit uses PublicMerkleRoot(N) (bound to the transaction)')
    ap.add_argument('--leaves', help='leaves.json, the leaves of the proof (witness of a bound circuit)')
    ap.add_argument('--unbound', action='store_true', help='no transaction binding: every public signal is an input')
    ap.add_argument('--sighash-input', action='store_true', help='bound by the first public signal, the sighash')
    ap.add_argument('--sighash', help="witness with --sighash-input: the transaction's sighash, 64 hex digits")
    a = ap.parse_args(argv)
    vk = load_vk(a.files[0])
    n = len(vk['ic']) - 1
    by_input = a.sighash_input
    need(by_input or a.sighash is None, '--sighash goes with --sighash-input')
    if by_input:
        alone = a.values is None and not a.leaves and not a.unbound
        need(alone, '--sighash-input goes alone: no --values, --leaves or --unbound')
        sighash, values, depth = None, None, 0
        if a.command == 'witness':
            need(a.sighash is not None, 'witness with --sighash-input needs --sighash')
            sighash = bytes.fromhex(a.sighash)
            need(len(sighash) == 32, 'the sighash is 32 bytes (64 hex digits)')
    else:
        sighash, values = load_leaves(a.leaves) if a.leaves else (None, None)
        depth = binding_depth(n, a.values, values, a.unbound)
    t0 = time.time()
    os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
    if a.command == 'program':
        text, g, cost = Groth16.compile(vk, depth, sighash_input=by_input)
        with open(a.out + '.simpl', 'w') as f:
            f.write(text)
        if by_input:
            bound = 'bound to the transaction (the first public signal is the sighash)'
        elif depth:
            bound = f'bound to the transaction (tree depth {depth})'
        else:
            bound = 'NOT bound to the transaction (--unbound)'
        print(
            f'wrote {a.out}.simpl: {n} public input{"s" if n > 1 else ""}, {bound}, '
            f'cost bound {cost:,} mWU ({time.time() - t0:.0f}s)'
        )
        return
    need(len(a.files) == 3, 'witness needs verification_key.json proof.json public.json')
    proof, inputs = load_proof(a.files[1]), load_public(a.files[2])
    need(len(inputs) == n, f'public.json has {len(inputs)} signals, the key {n}')
    need(B.groth16_verify(vk, proof, inputs), 'the proof does not verify')
    g = Groth16(F.Fp(Num()), vk, b=PC.bounds(), depth=depth, sighash_input=by_input)
    if by_input:
        need(Groth16.root(sighash, []) == inputs[0], 'the first public signal is not this sighash')
        wit = g.witness(proof, inputs, sighash)
    elif depth:
        need(bool(a.leaves), '--leaves is needed for a bound circuit')
        sibs = binding.siblings([sighash] + values)
        need(Groth16.root(sighash, sibs) == inputs[0], 'the leaves do not give the public signal')
        wit = g.witness(proof, inputs, sighash, sibs)
    else:
        wit = g.witness(proof, inputs)
    need(wit is not None, 'no witness for this proof')
    g.verify(g.num_input(wit))
    with open(a.out + '.w0.json', 'w') as f:
        json.dump(g.witness_value(wit), f)
    print(f'wrote {a.out}.w0.json: the proof verifies ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
