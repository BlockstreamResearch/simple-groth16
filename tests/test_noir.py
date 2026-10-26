#!/usr/bin/env python3
"""Noir circuits through R1CS: tools/noir_r1cs.py's checks, and the Groth16 verifier bound by its first
public input (groth/groth16/verifier.py, sighash_input) on the proofs in examples/noir.

    python3 tests/test_noir.py [quick]

The opcode check reads `nargo compile --print-acir` output (canned here, so no nargo is needed): it
allows assertions, Brillig calls and the RANGE, AND and XOR black boxes, skips the Brillig functions'
code, and refuses the rest (Keccak-f, which noir-cli writes as an unconstrained hint; memory; calls)
unless trusted, and any line it does not know.  The layout check refuses a circuit whose public signals
would not be its public parameters: noir-cli makes the first ACIR witnesses public, so a private
parameter declared before a public one, or a return value, is refused.  nargo runs (stubbed here) into a
fresh directory: the tool converts the artifact that run wrote, never one under the circuit's own
target/, and refuses when nargo reports a problem on stderr, as it does for an unconstrained Brillig
output while exiting 0.

The proofs are of circuits/noir/multiplier (a = 3, b = 7, c = 21), made by `tools/demo.py
--frontend noir` for the harness's dummy sighash and for another one.  The program must accept the
first at the predicted cost, within its budget, and reject the second, and a wrong c.  `quick` skips the
program.
"""

import json
import os
import sys
import tempfile
import time
import types

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import groth16_snarkjs as T
import harness
import noir_r1cs as N

from groth.core import binding
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core.budget import budget_ok
from groth.core.sym import Num
from groth.groth16 import Groth16

EX = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'examples', 'noir')
DUMMY_SIGHASH = bytes.fromhex('9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a')
OTHER_SIGHASH = bytes.fromhex('11' * 32)
QUICK = 'quick' in sys.argv[1:]

MULTIPLIER = """Compiled ACIR for main:
func 0
private parameters: [w2, w3]
public parameters: [w0, w1]
return values: []
ASSERT w1 = w2*w3
"""
HINTED = """Compiled ACIR for main:
func 0
private parameters: [w0, w1]
public parameters: [w2]
return values: []
BLACKBOX::RANGE input: w0, bits: 64
BLACKBOX::KECCAKF1600 inputs: [w0, w1], outputs: [w3, w4]
BRILLIG CALL func: 0, predicate: 1, inputs: [w3], outputs: [w5]
ASSERT w5 = w2

unconstrained func 0: directive_invert
0: @21 = const u32 1
1: BLACKBOX::KECCAKF1600 is only unconstrained code here
"""
MEMORY = """func 0
private parameters: [w0, w1]
public parameters: []
return values: []
INIT b0 = [w0, w1]
READ w2 = b0[w1]
CALL func: 1, predicate: 1, inputs: [w2], outputs: [w3]

func 1
private parameters: [w0]
public parameters: []
return values: [w1]
ASSERT w1 = w0*w0
"""


def refused(f, *args, expect=''):
    try:
        f(*args)
    except SystemExit as e:
        assert expect in str(e), (expect, str(e))
        return
    raise AssertionError(f'not refused: {args}')


def opcodes():
    assert N.opcode_kinds(MULTIPLIER) == {'ASSERT': 1}
    N.check_kinds(N.opcode_kinds(MULTIPLIER))
    hinted = N.opcode_kinds(HINTED)  # the Brillig function's lines are not ACIR opcodes
    assert hinted == {'RANGE': 1, 'KECCAKF1600': 1, 'BRILLIG': 1, 'ASSERT': 1}, hinted
    refused(N.check_kinds, hinted, expect='KECCAKF1600 (1x)')
    N.check_kinds(hinted, ['KECCAKF1600'])
    memory = N.opcode_kinds(MEMORY)
    assert memory == {'MEMORY': 2, 'CALL': 1, 'ASSERT': 1}, memory
    refused(N.check_kinds, memory, expect='CALL (1x), MEMORY (2x)')
    try:
        N.opcode_kinds('func 0\nSOMETHING NEW w0\n')
        raise AssertionError('an unknown opcode line passed')
    except ValueError:
        pass
    print('opcode check: assertions, Brillig calls and RANGE pass; Keccak-f, memory and calls are refused')


def layout():
    N.check_layout(*N.public_layout(MULTIPLIER))  # the toy circuit: public parameters first
    assert N.public_layout(MULTIPLIER) == ([0, 1], [])
    assert N.r1cs_publics(os.path.join(EX, 'multiplier.r1cs')) == (0, 2)
    bad = {
        'a private parameter between two public ones': ('[w1, w3]', '[w0, w2]', '[]'),
        'a public return value': ('[w1, w2]', '[w0]', '[w3]'),
        'a private parameter first': ('[w0, w3]', '[w1, w2]', '[]'),
    }
    for label, (private, public, returns) in bad.items():
        text = MULTIPLIER.replace('[w2, w3]', private, 1).replace('[w0, w1]', public, 1)
        text = text.replace('return values: []', f'return values: {returns}')
        expect = 'returns a value' if returns != '[]' else 'declare every'
        assert N.public_layout(text)[0] == [int(w) for w in public.strip('[]').replace('w', '').split(', ')], label
        refused(N.check_layout, *N.public_layout(text), expect=expect)
    print('layout check: public parameters first pass; a private one before, or a return value, is refused')


def stub_nargo(stderr='', programs=('multiplier',)):
    """N.run as nargo 1.0.0-beta.19 would answer: the version, or a compile that writes `programs` into
    the --target-dir it is given and prints the multiplier's ACIR, with `stderr`, exiting 0."""

    def run(cmd, **kw):
        if '--version' in cmd:
            return types.SimpleNamespace(stdout=f'nargo version = {N.NARGO_VERSION}\n', stderr='')
        target = cmd[cmd.index('--target-dir') + 1]
        for name in programs:
            with open(os.path.join(target, name + '.json'), 'w') as f:
                f.write('{"nargo": "this run"}')
        return types.SimpleNamespace(stdout=MULTIPLIER, stderr=stderr, returncode=0)

    return run


def nargo_run():
    real = N.run
    try:
        with tempfile.TemporaryDirectory() as tmp:
            # a circuit directory with a decoy: a Nargo.toml whose description names another package,
            # and a target/ holding an artifact under that name
            circuit = os.path.join(tmp, 'c')
            os.makedirs(os.path.join(circuit, 'target'))
            with open(os.path.join(circuit, 'Nargo.toml'), 'w') as f:
                f.write('[package]\ndescription = """\nname = "evil"\n"""\nname = "multiplier"\ntype = "bin"\n')
            with open(os.path.join(circuit, 'target', 'evil.json'), 'w') as f:
                f.write('{"nargo": "planted"}')
            bug = "bug: Brillig function call isn't properly covered by a manual constraint\n"
            cases = [
                ({}, None),
                ({'stderr': bug}, 'soundness bug'),
                ({'programs': ()}, 'built 0'),
                ({'programs': ('a', 'b')}, 'built 2'),
            ]
            for i, (case, expect) in enumerate(cases):
                N.run = stub_nargo(**case)
                t = os.path.join(tmp, f't{i}')
                os.makedirs(t)
                if expect is None:
                    artifact, acir = N.nargo_compile(circuit, t)
                    assert artifact == os.path.join(t, 'multiplier.json') and acir == MULTIPLIER, artifact
                    with open(artifact) as f:
                        assert 'this run' in f.read()
                else:
                    refused(N.nargo_compile, circuit, t, expect=expect)
            N.run = stub_nargo(stderr='warning: unused variable\n')
            t = os.path.join(tmp, 'tw')
            os.makedirs(t)
            N.nargo_compile(circuit, t, True)  # --allow-nargo-warnings: printed, not refused
    finally:
        N.run = real
    print("nargo: the artifact is this run's, not the circuit's target/; a diagnostic on stderr is refused")


def load(name):
    with open(os.path.join(EX, name)) as f:
        return json.load(f)


def program():
    vk = T.load_vk(os.path.join(EX, 'verification_key.json'))
    proofs = {}
    for label, sighash, suffix in (('this', DUMMY_SIGHASH, ''), ('other', OTHER_SIGHASH, '_other_sighash')):
        proof = T.load_proof(os.path.join(EX, f'proof{suffix}.json'))
        inputs = T.load_public(os.path.join(EX, f'public{suffix}.json'))
        assert inputs == [binding.public_signal(sighash), 21], inputs
        proofs[label] = (proof, inputs, sighash)
    bnd = PC.bounds()
    g = Groth16(F.Fp(Num()), vk, b=bnd, sighash_input=True)
    proof, inputs, sighash = proofs['this']
    wit = g.witness(proof, inputs, sighash)
    assert wit is not None and g.witness(proof, inputs, OTHER_SIGHASH) is None, 'the input must be the sighash'
    g.verify(g.num_input(wit))
    other = g.witness(*proofs['other'])  # a valid proof, for another transaction
    assert other is not None
    wrong_c = dict(wit, scalars=[inputs[0], 22])
    if QUICK:
        print('numeric model ok')
        return
    t0 = time.time()
    text, g, estimate = Groth16.compile(vk, sighash_input=True, b=bnd)
    results = harness.run(
        'noir', text, g.witness_value(wit), multi=[g.witness_value(other), g.witness_value(wrong_c)], timeout=7200
    )
    r = harness.expect_ok(results[0], 'noir')
    assert r['cost'] == estimate, (r['cost'], estimate)
    assert budget_ok(r['cost'], r['program_bytes'], r['witness_bytes']), r
    for bad, label in zip(results[1:], ('another sighash', 'a wrong c')):
        harness.expect_rejected(bad, label)
        print(f'{label:15} rejected as expected')
    print(
        f'Noir verifier (2 public inputs, bound by the first): cost {r["cost"]:,} mWU, binding '
        f'{g.parts["binding"]:,} mWU, program {r["program_bytes"]:,} B, witness {r["witness_bytes"]:,} B '
        f'({time.time() - t0:.0f}s)'
    )


def main():
    opcodes()
    layout()
    nargo_run()
    program()
    print('all ok')


if __name__ == '__main__':
    main()
