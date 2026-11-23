#!/usr/bin/env python3
"""The command-line tools refuse what they cannot build safely.

tools/groth16_snarkjs.py: a circuit is bound to the transaction unless --unbound is given (--values 0 is
PublicMerkleRoot(0), tree depth 1), the flags must agree, its checks survive python -O, and a witness
whose leaves do not give the public signal is refused, as is one whose sighash is not the first public
signal (--sighash-input).  --fix K=VALUE compiles a public signal into the key: the folded key accepts the
proof with that value and no other, the binding applies to the signals left, and `witness` refuses a
proof whose public.json has another value.  --signal-bits N is a multiple of 8 from 184 to 248, goes with
a binding only, and a witness whose signal has another width is refused.

tools/fflonk_snarkjs.py: --bind or --unbound is required; a key point off the curve is refused, also
under python -O, and so is a proof made with the other transcript.  The proof's evaluations load reduced
mod r, as snarkjs reads them, so no witness holds a word that is not canonical, and a bad --pad leaves an
earlier witness as it was.  The loaders refuse points whose z is not 1 (snarkjs would read them as
Jacobian).

tools/demo.py: a powers-of-tau file is used only if its BLAKE2b-512 digest is the recorded one, whether
it is cached or downloaded; a recorded size larger than needed serves (fflonk's 2^9 takes the recorded
2^16), and a size with no recorded digest is refused.

    python3 tests/test_tools.py
"""

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import types

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
EXAMPLE = os.path.join(ROOT, 'examples', 'multiplier')
FFLONK = os.path.join(ROOT, 'examples', 'fflonk')
NOIR = os.path.join(ROOT, 'examples', 'noir')


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, 'tools', name + '.py'))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def refused(f, *args, expect=''):
    try:
        f(*args)
    except SystemExit as e:
        assert expect in str(e), (expect, str(e))
        return
    raise AssertionError(f'not refused: {args}')


def check_binding_depth(T):
    d = T.binding_depth
    assert d(1, None, None, True) == 0
    assert d(1, 0, None, False) == 1  # PublicMerkleRoot(0): the tree holds only the sighash
    assert d(1, 1, None, False) == 1
    assert d(1, 3, None, False) == 2
    assert d(1, None, [5], False) == 1  # the leaves give N
    assert d(1, None, [], False) == 1
    assert d(1, 2, [5, 6], False) == 2
    refused(d, 1, None, None, False, expect='--unbound')  # neither: no silent default
    refused(d, 1, 0, None, True, expect='--unbound')  # both
    refused(d, 1, None, [], True, expect='--unbound')
    refused(d, 1, -1, None, False, expect='at least 0')
    refused(d, 1, 1, [5, 6], False, expect='leaves have 2')
    refused(d, 2, 1, None, False, expect='one public signal')


def check_optimized(tmp):
    """python -O strips asserts; the tool's checks are not asserts, so an off-curve IC point is refused."""
    with open(os.path.join(EXAMPLE, 'verification_key.json')) as f:
        vk = json.load(f)
    vk['IC'][1][1] = str(int(vk['IC'][1][1]) + 1)
    path = os.path.join(tmp, 'bad_vk.json')
    with open(path, 'w') as f:
        json.dump(vk, f)
    tool = os.path.join(ROOT, 'tools', 'groth16_snarkjs.py')
    out = subprocess.run(
        [sys.executable, '-O', tool, 'program', path, '--unbound', '--out', os.path.join(tmp, 'x')],
        capture_output=True,
        text=True,
    )
    assert out.returncode != 0 and 'not on the curve' in out.stderr, out
    assert not os.path.exists(os.path.join(tmp, 'x.simpl'))


def check_wrong_leaves(T, tmp):
    with open(os.path.join(EXAMPLE, 'leaves.json')) as f:
        leaves = json.load(f)
    leaves['sighash'] = '00' * 32
    path = os.path.join(tmp, 'leaves.json')
    with open(path, 'w') as f:
        json.dump(leaves, f)
    files = [os.path.join(EXAMPLE, f) for f in ('verification_key.json', 'proof.json', 'public.json')]
    argv = ['witness', *files, '--leaves', path, '--out', os.path.join(tmp, 'w')]
    refused(T.main, argv, expect='the leaves do not give the public signal')
    assert not os.path.exists(os.path.join(tmp, 'w.w0.json'))
    refused(T.main, ['witness', *files, '--out', os.path.join(tmp, 'w')], expect='--unbound')


def check_sighash_input(T, tmp):
    vk = os.path.join(NOIR, 'verification_key.json')
    files = [vk, os.path.join(NOIR, 'proof.json'), os.path.join(NOIR, 'public.json')]
    out = os.path.join(tmp, 'si')
    refused(T.main, ['program', vk, '--sighash-input', '--values', '1', '--out', out], expect='goes alone')
    refused(T.main, ['program', vk, '--sighash-input', '--unbound', '--out', out], expect='goes alone')
    refused(T.main, ['program', vk, '--sighash', '00' * 32, '--unbound', '--out', out], expect='--sighash goes with')
    refused(T.main, ['witness', *files, '--sighash-input', '--out', out], expect='needs --sighash')
    argv = ['witness', *files, '--sighash-input', '--sighash', '11' * 32, '--out', out]
    refused(T.main, argv, expect='not this sighash')
    assert not os.path.exists(out + '.w0.json')


def check_fix(T, tmp):
    """--fix on the Noir example's key, whose signals are (sighash, c) with c = 21."""
    sys.path.insert(0, ROOT)
    from groth.core import bn254 as B
    from groth.core.dsl import CheckFailed
    from groth.groth16 import Groth16, fix_inputs

    vk_path = os.path.join(NOIR, 'verification_key.json')
    files = [vk_path, os.path.join(NOIR, 'proof.json'), os.path.join(NOIR, 'public.json')]
    vk, proof, inputs = T.load_vk(vk_path), T.load_proof(files[1]), T.load_public(files[2])
    assert inputs[1] == 21 and B.groth16_verify(vk, proof, inputs)
    # the folded key: one signal left, and it accepts the proof for c = 21 only
    folded = fix_inputs(vk, {1: 21})
    assert len(folded['ic']) == 2 and folded['ic'][1] == vk['ic'][1] and folded['ic'][0] != vk['ic'][0]
    assert B.groth16_verify(folded, proof, inputs[:1])
    assert not B.groth16_verify(fix_inputs(vk, {1: 22}), proof, inputs[:1])
    assert not B.groth16_verify(folded, proof, [inputs[0] ^ 1])
    assert fix_inputs(vk, {}) == vk and fix_inputs(vk, {1: 0})['ic'] == vk['ic'][:2]  # 0 times a point
    # any signal, in any order: fixing both leaves the constant L of the proof's inputs
    both = fix_inputs(vk, {1: 21, 0: inputs[0]})
    assert both['ic'] == [B.g1_add(B.g1_add(vk['ic'][0], B.g1_mul(vk['ic'][1], inputs[0])), B.g1_mul(vk['ic'][2], 21))]
    assert both == fix_inputs(fix_inputs(vk, {0: inputs[0]}), {0: 21})
    for bad in ({2: 1}, {-1: 1}, {1: B.R}, {1: -1}):
        try:
            fix_inputs(vk, bad)
            raise AssertionError(f'not refused: {bad}')
        except CheckFailed:
            pass
    # IC_0 + a IC_1 at infinity: a key built for it is refused, not compiled
    try:
        fix_inputs({**vk, 'ic': [B.g1_neg(vk['ic'][1]), vk['ic'][1], vk['ic'][2]]}, {0: 1})
        raise AssertionError('not refused: IC_0 at infinity')
    except CheckFailed:
        pass
    # the tool
    out = os.path.join(tmp, 'fx')
    program = lambda *flags: ['program', vk_path, *flags, '--out', out]
    for item, expect in (
        ('1', 'give K=VALUE'),
        ('c=21', 'give K=VALUE'),
        ('1=twenty', 'give K=VALUE'),
        ('2=21', 'public signals 0 to 1'),
        ('-1=21', 'public signals 0 to 1'),
        (f'1={B.R}', 'not below r'),
        ('1=-1', 'not below r'),
    ):
        refused(T.main, program('--unbound', f'--fix={item}'), expect=expect)
    refused(T.main, program('--unbound', '--fix', '1=21', '--fix', '1=21'), expect='fixed twice')
    refused(T.main, program('--unbound', '--fix', '0=5', '--fix', '1=21'), expect='at least one public signal')
    refused(T.main, program('--sighash-input', '--fix', '0=5'), expect='signal 0 is the sighash')
    # the binding by the tree wants one signal left: here it is the key's signal 0
    refused(T.main, program('--values', '0'), expect='one public signal')
    assert not os.path.exists(out + '.simpl')
    T.main(program('--sighash-input', '--fix', '1=0x15'))  # 21
    with open(out + '.simpl') as f:
        assert f.read() == Groth16.compile(folded, sighash_input=True)[0]
    # the witness: the same --fix, and a public.json with another value there is refused
    sighash = '9ef140b9bd336a9c5f00476986ac6a42cbadba9edd3de4b7fe36b5490fd0754a'  # the harness's dummy
    witness = lambda *flags: ['witness', *files, '--sighash-input', '--sighash', sighash, *flags, '--out', out]
    refused(T.main, witness('--fix', '1=22'), expect='the program fixes it to 22')
    assert not os.path.exists(out + '.w0.json')
    T.main(witness('--fix', '1=21'))  # checks the witness in the numeric model of the folded key's verifier
    assert os.path.exists(out + '.w0.json')


def check_signal_bits(T, tmp):
    """--signal-bits on the example key, whose signal is a root of 253 bits."""
    vk = os.path.join(EXAMPLE, 'verification_key.json')
    files = [vk, os.path.join(EXAMPLE, 'proof.json'), os.path.join(EXAMPLE, 'public.json')]
    out = os.path.join(tmp, 'sb')
    for n in ('190', '176', '128', '252', '256', '0'):  # 176 and below: the budget would not cover the cost
        refused(T.main, ['program', vk, '--values', '1', '--signal-bits', n, '--out', out], expect='multiple of 8')
    refused(T.main, ['program', vk, '--unbound', '--signal-bits', '200', '--out', out], expect='not with --unbound')
    assert not os.path.exists(out + '.simpl')
    T.main(['program', vk, '--values', '1', '--signal-bits', '200', '--out', out])
    T.main(['program', vk, '--values', '1', '--out', out + '_full'])
    assert os.path.getsize(out + '.simpl') < os.path.getsize(out + '_full.simpl')  # tables for 200 bits only
    # the example's proof is for a signal of 253 bits: a verifier of 200 has no witness for it
    argv = ['witness', *files, '--leaves', os.path.join(EXAMPLE, 'leaves.json'), '--signal-bits', '200', '--out', out]
    refused(T.main, argv, expect='cut to 200 bits')
    assert not os.path.exists(out + '.w0.json')


def check_ptau(tmp):
    D = load('demo')
    info = '# of Constraints: 5\n# of Public Inputs: 0\n# of Outputs: 1\n'  # 2^3 > 5 + 1
    D.snarkjs = lambda *a, **kw: types.SimpleNamespace(stdout=info)
    good, bad = b'the recorded powers of tau', b'another powers of tau'
    D.PTAU_BLAKE2B = {3: hashlib.blake2b(good, digest_size=64).hexdigest()}
    os.environ.pop('PTAU', None)
    os.environ.pop('PTAU_BLAKE2B', None)
    out = os.path.join(tmp, 'out')
    os.makedirs(out)
    cached = os.path.join(out, 'pot3_final.ptau')
    served = []

    def curl(cmd, **kw):  # stands in for the download: writes the served bytes to the -o path
        assert cmd[0] == 'curl' and '--fail' in cmd and '=https' in cmd
        with open(cmd[cmd.index('-o') + 1], 'wb') as f:
            f.write(served[-1])

    D.run = curl
    # a cached file is checked, not trusted
    with open(cached, 'wb') as f:
        f.write(bad)
    refused(D.ptau, out, 'r1cs', expect='not the expected powers of tau')
    with open(cached, 'wb') as f:
        f.write(good)
    assert D.ptau(out, 'r1cs') == cached
    os.remove(cached)
    # a download is checked before it is kept, and nothing of a refused one stays
    served.append(bad)
    refused(D.ptau, out, 'r1cs', expect='not used')
    assert os.listdir(out) == []
    served.append(good)
    assert D.ptau(out, 'r1cs') == cached and os.listdir(out) == ['pot3_final.ptau']
    # a size with no recorded digest
    D.PTAU_BLAKE2B = {}
    refused(D.ptau, out, 'r1cs', expect='no recorded digest')


def check_fflonk(tmp):
    F = load('fflonk_snarkjs')
    vk = os.path.join(FFLONK, 'verification_key.json')
    out = os.path.join(tmp, 'ff')
    refused(F.main, ['program', vk, '--transcript', 'keccak', '--out', out], expect='--unbound')
    refused(F.main, ['program', vk, '--transcript', 'keccak', '--bind', '--unbound', '--out', out], expect='--unbound')
    files = [vk, os.path.join(FFLONK, 'proof_sha256.json'), os.path.join(FFLONK, 'public.json')]
    argv = ['witness', *files, '--transcript', 'keccak', '--bind', '--pad', '0', '--out', out]
    refused(F.main, argv, expect='does not verify')
    assert not os.path.exists(out + '.w0.json')
    # python -O keeps the key's checks: C0 off the curve
    with open(vk) as f:
        j = json.load(f)
    j['C0'][1] = str(int(j['C0'][1]) + 1)
    path = os.path.join(tmp, 'bad_fflonk_vk.json')
    with open(path, 'w') as f:
        json.dump(j, f)
    tool = os.path.join(ROOT, 'tools', 'fflonk_snarkjs.py')
    res = subprocess.run(
        [sys.executable, '-O', tool, 'program', path, '--transcript', 'sha256', '--bind', '--out', out],
        capture_output=True,
        text=True,
    )
    assert res.returncode != 0 and 'not on the curve' in res.stderr, res
    assert not os.path.exists(out + '.simpl')


def check_loaders(tmp):
    """The fflonk proof's evaluations as snarkjs reads them; witness words in range; affine points only."""
    sys.path.insert(0, ROOT)
    from groth.core import bn254 as B
    from groth.core import snarkjs as S
    from groth.core.dsl import CheckFailed, wv

    def fails(f, *args):
        try:
            f(*args)
        except CheckFailed:
            return
        raise AssertionError(f'not refused: {args}')

    with open(os.path.join(FFLONK, 'proof_keccak.json')) as f:
        j = json.load(f)
    a = int(j['evaluations']['a'])
    good = S.fflonk_proof(j)
    for k in (1, 4):  # snarkjs reads a + k r below 2^256 as a
        j2 = json.loads(json.dumps(j))
        j2['evaluations']['a'] = str(a + k * B.R)
        assert S.fflonk_proof(j2) == good
    for bad in (str(a - B.R), str(a + 6 * B.R), hex(a), ' 1', '1_2', 7, True):
        j2 = json.loads(json.dumps(j))
        j2['evaluations']['a'] = bad
        fails(S.fflonk_proof, j2)
    j2 = dict(j, curve='bls12381')
    fails(S.fflonk_proof, j2)
    for v in (-1, 1 << 256):
        fails(wv, 256, v)
    assert wv(256, (1 << 256) - 1) == {'w': 'f' * 64}
    # z must be 1: (x z^2, y z^3, z) is the same point to snarkjs, another one (or none) to (X/Z, Y/Z)
    x, y = S.g1(j['polynomials']['C1'][:2] + ['1'])
    fails(S.g1, [str(x * 4 % B.P), str(y * 8 % B.P), '2'])
    with open(os.path.join(EXAMPLE, 'verification_key.json')) as f:
        vk = json.load(f)
    vk['vk_beta_2'][2] = ['2', '0']
    fails(S.groth16_key, vk)
    # a bad --pad leaves an earlier witness file as it was
    F = load('fflonk_snarkjs')
    out = os.path.join(tmp, 'pad')
    with open(out + '.w0.json', 'w') as f:
        f.write('earlier')
    files = [os.path.join(FFLONK, n) for n in ('verification_key.json', 'proof_keccak.json', 'public.json')]
    refused(F.main, ['witness', *files, '--transcript', 'keccak', '--bind', '--pad', '512', '--out', out], expect='511')
    with open(out + '.w0.json') as f:
        assert f.read() == 'earlier'


def check_ptau_fflonk(tmp):
    """fflonk needs 9 times its domain; a larger recorded size serves, and is taken."""
    D = load('demo')
    info = '# of Constraints: 2\n# of Public Inputs: 3\n# of Outputs: 0\n'  # needs 2^9
    D.snarkjs = lambda *a, **kw: types.SimpleNamespace(stdout=info)
    good = b'the recorded powers of tau of size 2^16'
    D.PTAU_BLAKE2B = {16: hashlib.blake2b(good, digest_size=64).hexdigest()}
    os.environ.pop('PTAU', None)
    os.environ.pop('PTAU_BLAKE2B', None)
    out = os.path.join(tmp, 'out_fflonk')
    os.makedirs(out)
    with open(os.path.join(out, 'pot16_final.ptau'), 'wb') as f:
        f.write(good)
    assert D.ptau(out, 'r1cs', 'fflonk') == os.path.join(out, 'pot16_final.ptau')
    D.PTAU_BLAKE2B = {8: D.PTAU_BLAKE2B[16]}  # too small: no recorded size serves
    refused(D.ptau, out, 'r1cs', 'fflonk', expect='no recorded digest for the powers of tau of size 2^9')


def main():
    T = load('groth16_snarkjs')
    with tempfile.TemporaryDirectory() as tmp:
        check_binding_depth(T)
        check_optimized(tmp)
        check_wrong_leaves(T, tmp)
        check_sighash_input(T, tmp)
        check_fix(T, tmp)
        check_signal_bits(T, tmp)
        check_ptau(tmp)
        check_fflonk(tmp)
        check_loaders(tmp)
        check_ptau_fflonk(tmp)
    print('all ok')


if __name__ == '__main__':
    main()
