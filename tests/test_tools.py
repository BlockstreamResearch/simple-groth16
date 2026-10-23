#!/usr/bin/env python3
"""The command-line tools refuse what they cannot build safely.

tools/groth16_snarkjs.py: a circuit is bound to the transaction unless --unbound is given (--values 0 is
PublicMerkleRoot(0), tree depth 1), the flags must agree, its checks survive python -O, and a witness
whose leaves do not give the public signal is refused.  tools/fflonk_snarkjs.py: --bind or --unbound is
required, a key point off the curve is refused under python -O, and so is a proof for the other
transcript.  tools/circom_demo.py: a powers-of-tau file is used only if its BLAKE2b-512 digest is the
recorded one, whether it is cached or downloaded, and fflonk takes the smallest recorded size that is
large enough.

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


def check_ptau(tmp):
    D = load('circom_demo')
    D.snarkjs = lambda *a, **kw: types.SimpleNamespace(stdout='# of Constraints: 5\n')  # 2^3 >= 5 + 2
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


def check_ptau_fflonk(tmp):
    """fflonk needs 9 times its domain; a larger recorded size serves, and is taken."""
    D = load('circom_demo')
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
        check_ptau(tmp)
        check_fflonk(tmp)
        check_ptau_fflonk(tmp)
    print('all ok')


if __name__ == '__main__':
    main()
