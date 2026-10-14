#!/usr/bin/env python3
"""Verifier program from a snarkjs verification key, and witness from a snarkjs proof.

    python3 tools/groth16_snarkjs.py program verification_key.json --out build/x [--values N] [--w 5] [--pad auto]
    python3 tools/groth16_snarkjs.py witness verification_key.json proof.json public.json --out build/x [--leaves leaves.json]

`program` writes x.simpl (then `deploy compile` makes x.uprog and `deploy address` the output to fund).
`witness` writes x.w0.json for `deploy spend`; it verifies the proof first.

--values N: the circuit follows circuits/public_merkle.circom, so its one public signal is the Merkle
root of the sighash and N values, and the proof is bound to the spending transaction.  The witness then
needs --leaves, a JSON file {"sighash": "<64 hex digits>", "values": ["<decimal>", ...]}.  Without
--values, every public signal is a verifier input (8.7 M mWU each) and nothing binds the transaction.

--pad: the number of 512-byte padding blocks; `auto` sizes it from the program's cost, assuming a pruned
program of PROGRAM_BYTES bytes (`deploy spend` reports whether the budget is covered).
"""
import argparse, json, os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, pairing as PC, merkle
from groth.groth16 import Groth16
from groth.sym import Num

PROGRAM_BYTES = 60000 # a pruned one-input verifier is about 61 kB; a low estimate only adds padding


def g1(pt):
    x, y, z = (int(v) for v in pt)
    assert z != 0, 'point at infinity'
    if z != 1:
        zi = pow(z, -1, B.P)
        x, y = x * zi % B.P, y * zi % B.P
    assert B.g1_on_curve(x, y), 'G1 point not on the curve'
    return (x, y)


def g2(pt):
    x, y, z = (B.Fp2(int(v[0]), int(v[1])) for v in pt)
    assert not z.is_zero(), 'point at infinity'
    if z != B.Fp2(1):
        zi = z.inv()
        x, y = x * zi, y * zi
    assert B.g2_on_curve(x, y), 'G2 point not on the twist'
    assert B.g2_in_subgroup((x, y)), 'G2 point not in the order-r subgroup'
    return (x, y)


def load_vk(path):
    j = json.load(open(path))
    assert j.get('protocol') == 'groth16' and j.get('curve') in ('bn128', 'bn254'), 'a snarkjs groth16/bn128 key'
    vk = dict(alpha=g1(j['vk_alpha_1']), beta=g2(j['vk_beta_2']), gamma=g2(j['vk_gamma_2']), delta=g2(j['vk_delta_2']),
              ic=[g1(p) for p in j['IC']])
    assert len(vk['ic']) == j['nPublic'] + 1
    return vk


def load_proof(path):
    j = json.load(open(path))
    assert j.get('protocol') == 'groth16' and j.get('curve') in ('bn128', 'bn254'), 'a snarkjs groth16/bn128 proof'
    return (g1(j['pi_a']), g2(j['pi_b']), g1(j['pi_c']))


def load_public(path):
    return [int(v) for v in json.load(open(path))]


def load_leaves(path):
    j = json.load(open(path))
    return bytes.fromhex(j['sighash']), [int(v) for v in j['values']]


def auto_pad(vk, w, depth):
    """Padding blocks from the unpadded program's cost and witness size."""
    _, g, cost = Groth16.compile(vk, w, 0, depth)
    return Groth16.padding(cost, PROGRAM_BYTES, (g.witness_bits() + 7) // 8)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['program', 'witness'])
    ap.add_argument('files', nargs='+', help='verification_key.json [proof.json public.json]')
    ap.add_argument('--out', required=True)
    ap.add_argument('--values', type=int, default=0, help='public values of the circuit behind the Merkle root (0: no binding)')
    ap.add_argument('--leaves', help='the leaves of the proof (witness with --values)')
    ap.add_argument('--w', type=int, default=5, help='MSM window width')
    ap.add_argument('--pad', default='auto', help='padding blocks of 512 bytes, or auto')
    a = ap.parse_args()
    vk = load_vk(a.files[0])
    n = len(vk['ic']) - 1
    if a.leaves:
        sighash, values = load_leaves(a.leaves)
        a.values = len(values)
    depth = merkle.depth_of(a.values + 1) if a.values else 0
    if depth:
        assert n == 1, f'a bound circuit has one public signal, the key has {n}'
    t0 = time.time()
    pad = auto_pad(vk, a.w, depth) if a.pad == 'auto' else int(a.pad)
    os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
    if a.command == 'program':
        text, g, cost = Groth16.compile(vk, a.w, pad, depth)
        with open(a.out + '.simpl', 'w') as f:
            f.write(text)
        print(f'wrote {a.out}.simpl: {n} public input{"s" if n > 1 else ""}, '
              f'{"bound to the transaction (tree depth %d)" % depth if depth else "no transaction binding"}, '
              f'{pad} padding blocks, cost bound {cost:,} mWU ({time.time() - t0:.0f}s)')
        return
    assert len(a.files) == 3, 'witness needs verification_key.json proof.json public.json'
    proof, inputs = load_proof(a.files[1]), load_public(a.files[2])
    assert len(inputs) == n, 'public signals'
    assert B.groth16_verify(vk, proof, inputs), 'the proof does not verify'
    g = Groth16(F.Fp(Num()), vk, a.w, b=PC.bounds(), pad_blocks=pad, depth=depth)
    if depth:
        assert a.leaves, '--leaves is needed for a bound circuit'
        sibs = merkle.siblings([sighash] + values)
        assert Groth16.root(sighash, sibs) == inputs[0], 'the leaves do not give the public signal'
        wit = g.witness(proof, inputs, sighash, sibs)
    else:
        wit = g.witness(proof, inputs)
    assert wit is not None
    g.verify(g.num_input(wit))
    with open(a.out + '.w0.json', 'w') as f:
        json.dump({'w_in': g.witness_value(wit)}, f)
    print(f'wrote {a.out}.w0.json: the proof verifies (s = {wit["s"]}), {pad} padding blocks ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
