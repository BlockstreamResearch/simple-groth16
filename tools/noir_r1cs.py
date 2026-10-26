#!/usr/bin/env python3
"""A Noir circuit as R1CS for snarkjs: compile it once, then a witness per proof.

    python3 tools/noir_r1cs.py compile circuits/noir/multiplier inputs.json --out build/x
    python3 tools/noir_r1cs.py witness inputs.json --out build/x

`compile` runs `nargo compile` (NARGO, version 1.0.0-beta.19) into a fresh directory and refuses the
circuit unless every ACIR opcode is one the R1CS can hold soundly and its public signals are its public
parameters (below), then converts the artifact that run wrote, whose ACIR it checked, with `noir-cli
interop` (NOIR_CLI, from Noir-Groth16 at commit 4b7caace1f21) to x.r1cs, the circuit snarkjs sets up, and
keeps that artifact (x.noir.json).  It never reads the circuit's own target/ directory.  `witness` converts that artifact again for the inputs and writes x.wtns, the witness
snarkjs proves with, after checking that the R1CS is x.r1cs byte for byte.  inputs.json gives the circuit's parameters by name, as the ABI shapes them:
{"sighash": ["<decimal>", "<decimal>"], "c": "21", ...}.

Why the checks.  The converter lowers some black-box functions with constraints (RANGE, AND, XOR, by bit
decomposition), but writes others, Keccak-f among them, as unconstrained hints: the R1CS would accept any
output, and a proof would prove nothing about it.  For others still it folds the witness's values into
the R1CS as constants.  So `compile` allows only assertions (ASSERT), Brillig calls (unconstrained code,
whose outputs the circuit must constrain, as in any Noir backend) and the black boxes RANGE, AND and XOR,
and `witness` refuses an R1CS that changed with the inputs.  --trust NAME[,NAME...] allows more opcode
kinds (a black box by its name, MEMORY, CALL), at the user's risk: review how noir-cli lowers them first.

nargo's warnings are fatal (--deny-warnings), among them its check for Brillig outputs the circuit leaves
unconstrained, which it otherwise only prints.  The check is a heuristic: it misses some
under-constrained hints and flags some constrained ones.  --allow-nargo-warnings prints the warnings
instead, for a circuit reviewed to constrain what nargo flags.

noir-cli makes the circuit's first ACIR witnesses the public signals, whatever their visibility: nargo
numbers the parameters in the order they are declared, and the return values after them.  So `compile`
refuses a circuit unless its public parameters are declared before any private one and it returns
nothing.  The public signals are then the public parameters, in order.  For a verifier bound to the
transaction, the first is the sighash with its top three bits cleared (the Groth16 tool's
--sighash-input); fflonk's --bind takes the sighash as two 128-bit limbs, high then low, as the first two.
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
NOIR_GROTH16 = (
    '4b7caace1f2128e454c8d0fe50cac1ec46b1e272'  # the full commit: an abbreviated rev is a name cargo resolves
)
CONVERTER = f'https://github.com/jamesbachini/Noir-Groth16 at {NOIR_GROTH16} (cargo install --locked --git ... --rev {NOIR_GROTH16} noir-cli)'
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


def public_layout(acir_text):
    """func 0's public parameters and return values (their ACIR witness indices) in `nargo compile
    --print-acir` output."""
    found, section = {}, None
    for line in acir_text.splitlines():
        s = line.strip()
        if re.fullmatch(r'func \d+', s) or re.match(r'unconstrained func \d+', s):
            section = s
            continue
        m = re.fullmatch(r'(public parameters|return values): \[(.*)\]', s)
        if m and section == 'func 0':
            found[m.group(1)] = [int(w) for w in re.findall(r'\bw(\d+)\b', m.group(2))]
    return found.get('public parameters'), found.get('return values')


def check_layout(public, returns):
    """Refuse unless noir-cli's public signals, ACIR witnesses w0..w(n-1) with n the number of public
    parameters and return values, are exactly the public parameters: declared first, with no return
    value.  Otherwise a private parameter would be a public signal, published in the spend, and a declared
    public input would be missing from the statement."""
    if public is None or returns is None:
        fail('no public parameters or return values for func 0 in the nargo output')
    if returns:
        fail(
            f'the circuit returns a value (witnesses {returns}): noir-cli would make other witnesses public in its '
            'place.  Return nothing; make the value a public parameter and assert it.'
        )
    if not public or public != list(range(len(public))):
        fail(
            f'the public parameters are witnesses {public}: noir-cli makes the first witnesses public, whatever '
            'their visibility, so declare every public parameter before any private one, the sighash first.'
        )


def r1cs_publics(path):
    """(nPubOut, nPubIn) from an iden3 .r1cs file's header section."""
    with open(path, 'rb') as f:
        b = f.read()
    if b[:4] != b'r1cs':
        fail(f'{path} is not an R1CS file')
    i, n = 12, int.from_bytes(b[8:12], 'little')
    for _ in range(n):
        kind, size = int.from_bytes(b[i : i + 4], 'little'), int.from_bytes(b[i + 4 : i + 12], 'little')
        if kind == 1:
            j = i + 12
            fs = int.from_bytes(b[j : j + 4], 'little')
            j += 4 + fs + 4  # field size, prime, number of wires
            return int.from_bytes(b[j : j + 4], 'little'), int.from_bytes(b[j + 4 : j + 8], 'little')
        i += 12 + size
    fail(f'{path} has no header section')


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


def run(cmd, check=True, **kw):
    try:
        return subprocess.run(cmd, check=check, capture_output=True, text=True, **kw)
    except FileNotFoundError:
        fail(f'{cmd[0]} not found: set NARGO / NOIR_CLI (nargo {NARGO_VERSION}; noir-cli from {CONVERTER})')
    except subprocess.CalledProcessError as e:
        fail(f'{" ".join(cmd)} failed:\n{e.stdout}{e.stderr}')


DIAGNOSTIC = re.compile(r'^(bug|error|warning)\b', re.M)


def nargo_compile(circuit_dir, target_dir, warnings=False):
    """Compile the circuit into target_dir, an empty directory, and return the artifact this run wrote
    there and the ACIR it printed: the artifact converted is the one whose ACIR is checked.  nargo's
    warnings are fatal, unless `warnings` (then they are printed)."""
    version = run([NARGO, '--version']).stdout
    if f'nargo version = {NARGO_VERSION}' not in version:
        fail(f'nargo {NARGO_VERSION} is needed (the version noir-cli reads), not: {version.splitlines()[:1]}')
    if os.listdir(target_dir):
        fail(f'{target_dir} is not empty')
    cmd = [NARGO, 'compile', '--force', '--print-acir', '--target-dir', os.path.abspath(target_dir)]
    if not warnings:
        cmd.insert(2, '--deny-warnings')
    res = run(cmd, check=False, cwd=circuit_dir)
    why = (
        'nargo reported a problem with the circuit (a Brillig output it leaves unconstrained is a soundness bug; '
        'an unsafe block needs a // Safety: comment).  Fix the circuit, or give --allow-nargo-warnings after reviewing it'
    )
    if res.returncode != 0:
        fail(f'{" ".join(cmd)} failed' + (f'.  {why}' if not warnings else '') + f':\n{res.stdout}{res.stderr}')
    if DIAGNOSTIC.search(res.stderr):
        if not warnings:
            fail(f'{why}:\n{res.stderr}')
        print(res.stderr, file=sys.stderr, end='')
    built = [f for f in os.listdir(target_dir) if f.endswith('.json')]
    if len(built) != 1:
        fail(f'nargo built {len(built)} programs for {circuit_dir}: give the directory of one binary package')
    return os.path.join(target_dir, built[0]), res.stdout


def interop(artifact, inputs, out_dir):
    """noir-cli interop: (r1cs path, wtns path) in out_dir."""
    run([NOIR_CLI, 'interop', artifact, inputs, '--out', out_dir])
    return os.path.join(out_dir, 'circuit.r1cs'), os.path.join(out_dir, 'witness.wtns')


def compile_r1cs(circuit_dir, inputs, out, trust=(), warnings=False):
    with tempfile.TemporaryDirectory() as t, tempfile.TemporaryDirectory() as d:
        artifact, acir = nargo_compile(circuit_dir, t, warnings)
        try:
            kinds = opcode_kinds(acir)
        except ValueError as e:
            fail(str(e))
        check_kinds(kinds, trust)
        public, returns = public_layout(acir)
        check_layout(public, returns)
        r1cs, _ = interop(artifact, inputs, d)
        if r1cs_publics(r1cs) != (0, len(public)):
            fail(f'noir-cli wrote {r1cs_publics(r1cs)} public outputs and inputs, not (0, {len(public)})')
        shutil.copyfile(r1cs, out + '.r1cs')
        shutil.copyfile(artifact, out + '.noir.json')  # the artifact whose ACIR was checked
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
    ap.add_argument('--allow-nargo-warnings', action='store_true', help="print nargo's warnings instead of refusing")
    a = ap.parse_args(argv)
    trust = [t for t in a.trust.split(',') if t]
    os.makedirs(os.path.dirname(a.out) or '.', exist_ok=True)
    if a.command == 'compile':
        if len(a.files) != 2:
            fail('compile needs the circuit directory and inputs.json')
        kinds = compile_r1cs(a.files[0], a.files[1], a.out, trust, a.allow_nargo_warnings)
        print(f'wrote {a.out}.r1cs: opcodes ' + ', '.join(f'{k} {v}' for k, v in sorted(kinds.items())))
    else:
        if len(a.files) != 1:
            fail('witness needs inputs.json')
        witness(a.files[0], a.out, trust)
        print(f'wrote {a.out}.wtns: the R1CS is {a.out}.r1cs')


if __name__ == '__main__':
    main()
