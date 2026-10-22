#!/usr/bin/env python3
"""The command-line tools refuse what they cannot build safely.

tools/groth16_snarkjs.py: a circuit is bound to the transaction unless --unbound is given (--values 0 is
PublicMerkleRoot(0), tree depth 1), the flags must agree, its checks survive python -O, and a witness
whose leaves do not give the public signal is refused.

    python3 tests/test_tools.py
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
EXAMPLE = os.path.join(ROOT, 'examples', 'multiplier')


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


def main():
    T = load('groth16_snarkjs')
    with tempfile.TemporaryDirectory() as tmp:
        check_binding_depth(T)
        check_optimized(tmp)
        check_wrong_leaves(T, tmp)
    print('all ok')


if __name__ == '__main__':
    main()
