#!/usr/bin/env python3
"""The toy circuit circuits/multiplier.circom end to end (the prover knows a, b with a b = c):

    python3 tools/circom_demo.py setup --out build/multiplier
        circuit, Groth16 key (verification_key.json) and verifier program (verifier.simpl)
    python3 tools/circom_demo.py prove --out build/multiplier --sighash <64 hex digits> [--a 3 --b 7]
        proof.json, public.json, leaves.json and the verifier's witness verifier.w0.json

Needs circom (CIRCOM, default `circom`) and `npm install` in circuits/ (snarkjs and circomlib;
NODE_MODULES to use another directory).  `setup` downloads a powers-of-tau file sized for the circuit
from the perpetual powers of tau (PTAU to use a local file).  tools/regtest.sh runs both on a node.
"""
import argparse, json, math, os, re, shutil, subprocess, sys, time
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from groth import bn254, merkle

CIRCOM = os.environ.get('CIRCOM', 'circom')
NODE_MODULES = os.environ.get('NODE_MODULES', os.path.join(ROOT, 'circuits', 'node_modules'))
SNARKJS = os.path.join(NODE_MODULES, '.bin', 'snarkjs')
CIRCUIT = os.path.join(ROOT, 'circuits', 'multiplier.circom')
NAME = 'multiplier'
VALUES = 1 # the circuit's public values behind the root: c
PTAU_URL = 'https://pse-trusted-setup-ppot.s3.eu-central-1.amazonaws.com/pot28_0080/ppot_0080_{power}.ptau'


def run(cmd, **kw):
    print('+', ' '.join(cmd), flush=True)
    return subprocess.run(cmd, check=True, **kw)


def snarkjs(*args, **kw):
    return run([SNARKJS] + list(args), **kw)


def ptau(out, r1cs):
    """A prepared powers-of-tau file for the circuit (2^power >= constraints + 2)."""
    info = snarkjs('r1cs', 'info', r1cs, capture_output=True, text=True).stdout
    constraints = int(re.search(r'# of Constraints: (\d+)', info).group(1))
    power = max(1, math.ceil(math.log2(constraints + 2)))
    path = os.environ.get('PTAU', os.path.join(out, f'pot{power}_final.ptau'))
    if not os.path.exists(path):
        url = PTAU_URL.format(power=power)
        print(f'{constraints} constraints: downloading the powers of tau for 2^{power} from {url}', flush=True)
        run(['curl', '-sSL', '-o', path + '.part', url])
        os.rename(path + '.part', path)
    return path


def check_tools():
    if not shutil.which(CIRCOM):
        sys.exit('circom not found: install circom 2 (https://github.com/iden3/circom/releases) or set CIRCOM')
    if not os.path.isdir(os.path.join(NODE_MODULES, 'circomlib')) or not os.path.exists(SNARKJS):
        sys.exit(f'snarkjs and circomlib not found in {NODE_MODULES}: run `npm install` in circuits/ (or set NODE_MODULES)')


def setup(a):
    check_tools()
    out = a.out
    os.makedirs(out, exist_ok=True)
    run([CIRCOM, CIRCUIT, '--r1cs', '--wasm', '-o', out, '-l', NODE_MODULES])
    r1cs, zkey0, zkey = (os.path.join(out, f) for f in (f'{NAME}.r1cs', f'{NAME}_0000.zkey', f'{NAME}.zkey'))
    snarkjs('groth16', 'setup', r1cs, ptau(out, r1cs), zkey0)
    snarkjs('zkey', 'contribute', zkey0, zkey, '--name=demo', '-e=simple-groth demo entropy')
    snarkjs('zkey', 'export', 'verificationkey', zkey, os.path.join(out, 'verification_key.json'))
    run([sys.executable, os.path.join(ROOT, 'tools', 'groth16_snarkjs.py'), 'program', os.path.join(out, 'verification_key.json'),
         '--values', str(VALUES), '--out', os.path.join(out, 'verifier')])


def prove(a):
    check_tools()
    out = a.out
    a.a, a.b = a.a % bn254.R, a.b % bn254.R # the circuit's field is the BN254 scalar field
    c = a.a * a.b % bn254.R
    sighash = bytes.fromhex(a.sighash)
    with open(os.path.join(out, 'input.json'), 'w') as f:
        json.dump(dict(a=str(a.a), b=str(a.b), c=str(c), sighash=[str(v) for v in merkle.sighash_limbs(sighash)]), f)
    print(f'a = {a.a}\nb = {a.b}\nc = a b mod r = {c}')
    with open(os.path.join(out, 'leaves.json'), 'w') as f:
        json.dump(dict(sighash=a.sighash, values=[str(c)]), f)
    t0 = time.time()
    run(['node', os.path.join(out, f'{NAME}_js', 'generate_witness.js'), os.path.join(out, f'{NAME}_js', f'{NAME}.wasm'),
         os.path.join(out, 'input.json'), os.path.join(out, f'{NAME}.wtns')])
    snarkjs('groth16', 'prove', os.path.join(out, f'{NAME}.zkey'), os.path.join(out, f'{NAME}.wtns'),
            os.path.join(out, 'proof.json'), os.path.join(out, 'public.json'))
    print(f'proved in {time.time() - t0:.0f}s', flush=True)
    snarkjs('groth16', 'verify', os.path.join(out, 'verification_key.json'), os.path.join(out, 'public.json'), os.path.join(out, 'proof.json'))
    public = json.load(open(os.path.join(out, 'public.json')))
    assert int(public[0]) == merkle.public_signal(merkle.root([sighash, c])), 'the circuit and merkle.py disagree on the root'
    print(f'the public signal is the Merkle root of the sighash and c = {c}, as merkle.py computes it')
    run([sys.executable, os.path.join(ROOT, 'tools', 'groth16_snarkjs.py'), 'witness', os.path.join(out, 'verification_key.json'),
         os.path.join(out, 'proof.json'), os.path.join(out, 'public.json'), '--leaves', os.path.join(out, 'leaves.json'),
         '--out', os.path.join(out, 'verifier')])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['setup', 'prove'])
    ap.add_argument('--out', default='build/multiplier')
    ap.add_argument('--sighash', help='the sig_all_hash of the spending transaction (deploy sighash)')
    ap.add_argument('--a', type=int, default=3, help='a factor (reduced mod r)')
    ap.add_argument('--b', type=int, default=7)
    a = ap.parse_args()
    if a.command == 'setup':
        setup(a)
    else:
        assert a.sighash and len(a.sighash) == 64, '--sighash <64 hex digits>'
        prove(a)


if __name__ == '__main__':
    main()
