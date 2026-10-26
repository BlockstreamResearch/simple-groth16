#!/usr/bin/env python3
"""The fflonk verifier program from a snarkjs verification key, and its witness from a snarkjs proof.

    python3 tools/fflonk_snarkjs.py program verification_key.json --transcript keccak|sha256 --bind|--unbound --out build/x
    python3 tools/fflonk_snarkjs.py witness verification_key.json proof.json public.json --transcript keccak|sha256 --bind|--unbound --out build/x

`program` writes x.simpl (then `deploy compile` makes x.uprog and `deploy address` the output to fund).
`witness` writes x.w0.json for `deploy spend`; it verifies the proof first (groth/fflonk/reference.py).

The verifier costs more than its program and witness weigh, so the witness carries padding (zero blocks
of 512 bytes, groth/fflonk/verifier.py) to raise the input's budget.  `witness` runs the program once in hand
(HAND, default tools/harness/target/release/hand) to learn the pruned program's size and pads just
enough; --pad N sets the number of blocks instead.  hand runs programs in a dummy environment, whose
sighash is not the transaction's, so with --bind it measures the program without the binding.  The
program measured is smaller than the one spent (it has no binding, and no padding group taken), so the
budget it predicts is a lower bound.

--transcript keccak checks proofs from snarkjs as it is; sha256, proofs from tools/snarkjs_sha256.mjs.
--bind: the circuit's first two public signals are the sighash of the spending transaction (two 128-bit
limbs, high then low), as in circuits/multiplier_fflonk.circom, and the program compares them with the
transaction's.  --unbound: nothing binds the transaction, so anyone who sees a spend can reuse its witness
in another transaction to the same output.  One of the two is required.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth.core import snarkjs
from groth.core.dsl import CheckFailed
from groth.fflonk import Fflonk
from groth.fflonk import reference as ref

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HAND = os.environ.get('HAND', os.path.join(ROOT, 'tools', 'harness', 'target', 'release', 'hand'))


def refusing(f, path):
    """f(the JSON at path), with a failed check (groth/core/snarkjs.py) as a refusal."""
    try:
        return f(snarkjs.load(path))
    except CheckFailed as e:
        sys.exit(f'fflonk_snarkjs.py: {path}: {e}')


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('command', choices=['program', 'witness'])
    ap.add_argument('files', nargs='+', help='verification_key.json [proof.json public.json]')
    ap.add_argument('--out', required=True)
    ap.add_argument('--transcript', choices=list(ref.MODES), required=True)
    ap.add_argument('--bind', action='store_true', help='the first two public signals are the sighash')
    ap.add_argument('--unbound', action='store_true', help='no transaction binding: anyone can reuse the witness')
    ap.add_argument('--pad', type=int, help='blocks of padding (default: as many as the budget needs)')
    a = ap.parse_args(argv)
    if a.bind == a.unbound:
        sys.exit('give --bind (the first two public signals are the sighash) or --unbound')
    vk = refusing(snarkjs.fflonk_key, a.files[0])
    t0 = time.time()
    os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
    if a.command == 'program':
        text, g, cost = Fflonk.compile(vk, a.transcript, a.bind)
        with open(a.out + '.simpl', 'w') as f:
            f.write(text)
        binding = 'bound to the transaction' if a.bind else 'no transaction binding'
        print(
            f'wrote {a.out}.simpl: fflonk, {a.transcript} transcript, {vk["nPublic"]} public inputs, {binding}, '
            f'cost {g.cost(cost, 0):,} mWU before padding ({time.time() - t0:.0f}s)'
        )
        return
    if len(a.files) != 3:
        sys.exit('witness needs verification_key.json proof.json public.json')
    proof, pub = refusing(snarkjs.fflonk_proof, a.files[1]), refusing(snarkjs.public_signals, a.files[2])
    if not ref.verify(a.transcript, vk, proof, pub)['ok']:
        sys.exit(f'the proof does not verify ({a.transcript} transcript)')
    text, g, estimate = Fflonk.compile(vk, a.transcript, a.bind)
    sighash = ((pub[0] << 128) | pub[1]).to_bytes(32, 'big') if a.bind else None
    w = g.witness(proof, pub, sighash)
    pad = a.pad
    if pad is None:
        if not os.path.exists(HAND):
            sys.exit(f'{HAND} not found: build tools/harness (make harness), set HAND, or give --pad')
        measured = Fflonk.compile(vk, a.transcript, False)[0] if a.bind else text
        with tempfile.TemporaryDirectory() as d:
            prog, wit = os.path.join(d, 'p.simpl'), os.path.join(d, 'p.w0.json')
            with open(prog, 'w') as f:
                f.write(measured)
            with open(wit, 'w') as f:
                json.dump(g.witness_value(w, 0), f)
            out = subprocess.run([HAND, prog, wit], capture_output=True, text=True, check=True).stdout
        r = json.loads(next(line for line in out.splitlines() if line.startswith('{')))
        if not r.get('ok'):
            sys.exit(f'the program rejects the witness: {r}')
        pad = g.pad_for(estimate, r['program_bytes'], r['witness_bytes'])
        print(
            f'pruned program {r["program_bytes"]:,} B, witness {r["witness_bytes"]:,} B without padding: '
            f'{pad} blocks of padding ({pad * 512:,} B)'
        )
    try:
        value = g.witness_value(w, pad)  # before the file is opened, so a bad --pad leaves it as it was
    except CheckFailed as e:
        sys.exit(f'fflonk_snarkjs.py: {e}')
    with open(a.out + '.w0.json', 'w') as f:
        json.dump(value, f)
    print(f'wrote {a.out}.w0.json: the proof verifies; cost {g.cost(estimate, pad):,} mWU ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
