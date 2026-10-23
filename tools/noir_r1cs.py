#!/usr/bin/env python3
"""A Noir circuit as R1CS for snarkjs: compile it once, then a witness per proof.

    python3 tools/noir_r1cs.py compile circuits/noir/multiplier inputs.json --out build/x
    python3 tools/noir_r1cs.py witness inputs.json --out build/x

`compile` runs `nargo compile` (NARGO, version 1.0.0-beta.19) and refuses the circuit unless every ACIR
opcode is one the R1CS can hold soundly (below), then converts it with `noir-cli interop` (NOIR_CLI, from
Noir-Groth16 at commit 4b7caac) to x.r1cs, the circuit snarkjs sets up, and keeps the compiled artifact
(x.noir.json).  `witness` converts that artifact again for the inputs and writes x.wtns, the witness
snarkjs proves with, after checking that the R1CS is x.r1cs byte for byte.  inputs.json gives the circuit's parameters by name, as the ABI shapes them:
{"sighash": ["<decimal>", "<decimal>"], "c": "21", ...}.

Why the checks.  The converter lowers some black-box functions with constraints (RANGE, AND, XOR, by bit
decomposition), but writes others, Keccak-f among them, as unconstrained hints: the R1CS would accept any
output, and a proof would prove nothing about it.  For others still it folds the witness's values into
the R1CS as constants.  So `compile` allows only assertions (ASSERT), Brillig calls (unconstrained code,
whose outputs the circuit must constrain, as in any Noir backend; nargo checks for outputs it leaves
unconstrained) and the black boxes RANGE, AND and XOR, and `witness` refuses an R1CS that changed with
the inputs.  --trust NAME[,NAME...] allows more opcode kinds (a black box by its name, MEMORY, CALL), at
the user's risk: review how noir-cli lowers them first.

The circuit's public parameters are snarkjs's public signals, in order.  For a verifier bound to the
transaction, the first two must be the sighash as two 128-bit limbs, high then low (the Groth16 tool's
--sighash-inputs, fflonk's --bind).
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

NARGO = os.environ.get('NARGO', 'nargo')
NOIR_CLI = os.environ.get('NOIR_CLI', 'noir-cli')
NARGO_VERSION = '1.0.0-beta.19'
CONVERTER = 'https://github.com/jamesbachini/Noir-Groth16 at 4b7caac (cargo install --git ... --rev 4b7caac noir-cli)'
ALLOWED = {'ASSERT', 'BRILLIG', 'RANGE', 'AND', 'XOR'}


def fail(msg):
    """Refuse with msg (not an assert, so python -O keeps it)."""
    sys.exit(f'noir_r1cs.py: {msg}')


def opcode_kinds(acir_text):
    """The kinds of the ACIR opcodes in `nargo compile --print-acir` output, with their counts: ASSERT,
    BRILLIG, CALL, MEMORY, or a black box's name (RANGE, KECCAKF1600, ...).  Brillig functions (the
    unconstrained code) are skipped; a line that is not a known opcode is an error."""
    kinds = {}
    section = None
    for line in acir_text.splitlines():
        s = line.strip()
        if not s or s.startswith('Compiled ACIR for'):
            continue
        if re.fullmatch(r'func \d+', s):
            section = 'acir'
            continue
        if re.match(r'unconstrained func \d+', s):
            section = 'brillig'
            continue
        if section != 'acir' or re.match(r'(private parameters|public parameters|return values):', s):
            continue
        m = re.match(r'BLACKBOX::([A-Z0-9_]+)\b', s)
        if m:
            kind = m.group(1)
        elif s.startswith('ASSERT '):
            kind = 'ASSERT'
        elif s.startswith('BRILLIG CALL '):
            kind = 'BRILLIG'
        elif s.startswith('CALL '):
            kind = 'CALL'
        elif re.match(r'(INIT|MEM|READ|WRITE)\b', s):
            kind = 'MEMORY'
        else:
            raise ValueError(f'an ACIR line this tool does not know: {s[:80]}')
        kinds[kind] = kinds.get(kind, 0) + 1
    if not kinds:
        raise ValueError('no ACIR opcodes in the output')
    return kinds


def check_kinds(kinds, trust=()):
    """Refuse opcode kinds outside the allowed set (and the trusted ones)."""
    bad = sorted(set(kinds) - ALLOWED - set(trust))
    if bad:
        fail(
            'the circuit uses ' + ', '.join(f'{k} ({kinds[k]}x)' for k in bad) + ', which this tool does not allow: '
            'noir-cli writes some black boxes as unconstrained hints or folds witness values into the R1CS, and its '
            'lowering of the rest is not checked here.  Rewrite the circuit without them, or give --trust after '
            'reviewing how noir-cli lowers them.'
        )


def run(cmd, **kw):
    try:
        return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw)
    except FileNotFoundError:
        fail(f'{cmd[0]} not found: set NARGO / NOIR_CLI (nargo {NARGO_VERSION}; noir-cli from {CONVERTER})')
    except subprocess.CalledProcessError as e:
        fail(f'{" ".join(cmd)} failed:\n{e.stdout}{e.stderr}')


def nargo_compile(circuit_dir):
    """Compile the circuit (nargo's own checks included, such as for unconstrained outputs); return the
    artifact's path and the opcode kinds."""
    version = run([NARGO, '--version']).stdout
    if f'nargo version = {NARGO_VERSION}' not in version:
        fail(f'nargo {NARGO_VERSION} is needed (the version noir-cli reads), not: {version.splitlines()[:1]}')
    with open(os.path.join(circuit_dir, 'Nargo.toml')) as f:
        name = re.search(r'^name\s*=\s*"([^"]+)"', f.read(), re.M)
    if not name:
        fail(f'no package name in {circuit_dir}/Nargo.toml')
    out = run([NARGO, 'compile', '--force', '--print-acir'], cwd=circuit_dir).stdout
    try:
        kinds = opcode_kinds(out)
    except ValueError as e:
        fail(str(e))
    return os.path.join(circuit_dir, 'target', name.group(1) + '.json'), kinds


def interop(artifact, inputs, out_dir):
    """noir-cli interop: (r1cs path, wtns path) in out_dir."""
    run([NOIR_CLI, 'interop', artifact, inputs, '--out', out_dir])
    return os.path.join(out_dir, 'circuit.r1cs'), os.path.join(out_dir, 'witness.wtns')


def compile_r1cs(circuit_dir, inputs, out, trust=()):
    artifact, kinds = nargo_compile(circuit_dir)
    check_kinds(kinds, trust)
    with tempfile.TemporaryDirectory() as d:
        r1cs, _ = interop(artifact, inputs, d)
        shutil.copyfile(r1cs, out + '.r1cs')
    shutil.copyfile(artifact, out + '.noir.json')
    with open(out + '.opcodes.json', 'w') as f:
        json.dump(kinds, f, sort_keys=True)
    return kinds


def witness(inputs, out, trust=()):
    """x.wtns for the inputs, from the compiled artifact x.noir.json, with the R1CS checked against
    x.r1cs."""
    if not os.path.exists(out + '.r1cs'):
        fail(f'{out}.r1cs not found: run `compile` first')
    with open(out + '.opcodes.json') as f:
        check_kinds(json.load(f), trust)
    with tempfile.TemporaryDirectory() as d:
        r1cs, wtns = interop(out + '.noir.json', inputs, d)
        with open(r1cs, 'rb') as f1, open(out + '.r1cs', 'rb') as f2:
            if f1.read() != f2.read():
                fail('the R1CS for these inputs is not the compiled one: noir-cli folded witness values into it')
        shutil.copyfile(wtns, out + '.wtns')


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['compile', 'witness'])
    ap.add_argument('files', nargs='+', help='compile: CIRCUIT_DIR INPUTS (any satisfying inputs); witness: INPUTS')
    ap.add_argument('--out', required=True)
    ap.add_argument('--trust', default='', help='opcode kinds to allow besides ASSERT, BRILLIG, RANGE, AND, XOR')
    a = ap.parse_args(argv)
    trust = [t for t in a.trust.split(',') if t]
    os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
    if a.command == 'compile':
        if len(a.files) != 2:
            fail('compile needs the circuit directory and inputs.json')
        kinds = compile_r1cs(a.files[0], a.files[1], a.out, trust)
        print(f'wrote {a.out}.r1cs: opcodes ' + ', '.join(f'{k} {v}' for k, v in sorted(kinds.items())))
    else:
        if len(a.files) != 1:
            fail('witness needs inputs.json')
        witness(a.files[0], a.out, trust)
        print(f'wrote {a.out}.wtns: the R1CS is {a.out}.r1cs')


if __name__ == '__main__':
    main()
