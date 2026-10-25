#!/usr/bin/env python3
"""Keccak-f[1600] and Keccak-256 in Simplicity (groth/core/keccak.py).

The reference permutation is checked against hashlib's SHA3-256 (the same permutation), and Keccak-256
against known digests.  The programs run in hand: the permutation of a random state, and Keccak-256 of
messages of 1 to 9 words (every way a message can end in its last block), each checked lane by lane or
word by word against the reference, at the estimated cost.  A wrong expected digest must be rejected.

    python3 tests/test_keccak.py
"""

import hashlib
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import keccak as K
from groth.core.dsl import Tbalanced, wbalanced, wv
from groth.core.sym import E, Num, Sym


def reference():
    rng = random.Random(1)
    for n in (0, 1, 31, 32, 100, 135, 136, 137, 271, 272, 300):
        msg = bytes(rng.randrange(256) for _ in range(n))
        assert K.sha3_256(msg) == hashlib.sha3_256(msg).digest(), n
    # Keccak-256 test vectors (Ethereum)
    assert K.keccak256(b'').hex() == 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'
    assert K.keccak256(b'abc').hex() == '4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45'
    fox = b'The quick brown fox jumps over the lazy dog'
    assert K.keccak256(fox).hex() == '4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15'
    # the word helpers agree with the byte functions
    w = rng.getrandbits(256)
    assert b''.join(x.to_bytes(8, 'little') for x in K.word_lanes(w)) == w.to_bytes(32, 'big')
    assert K.lanes_word(K.word_lanes(w)) == w
    # Num agrees with the reference
    ws = [rng.getrandbits(256) for _ in range(5)]
    assert K.Keccak(Num()).hash_words(ws) == int.from_bytes(
        K.keccak256(b''.join(x.to_bytes(32, 'big') for x in ws)), 'big'
    )
    print('reference: SHA3-256 matches hashlib, Keccak-256 its test vectors')


def run(name, n_words, bits, build, values, expected, out_bits, out_n, ok=True):
    """A program: w_in (n_words words of `bits`) -> build(be, accessors) -> out_n words of out_bits,
    each checked against expected."""
    be = Sym(bits * n_words)
    accs = be._unpack('', [E('', bits, 0) for _ in range(n_words)])
    e = build(be, accs)

    def checks(outs):
        ws = be.split(outs[0], [E('', out_bits, 0) for _ in range(out_n)]) if out_n > 1 else [outs[0]]
        eq = 'eq_64' if out_bits == 64 else 'eq_256'
        return be.checks([be.verify(be.jet(eq, be.pair(w, be.const(out_bits, x)), 1)) for w, x in zip(ws, expected)])

    body = be.scope([e], checks)
    be.em.define('w_in', 'witness', f'_ -> {Tbalanced([f"2^{bits}"] * n_words)}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + bits * n_words) + body.c
    r = harness.run(name, be.em.text(), {'w_in': wbalanced([wv(bits, v) for v in values])})
    if not ok:
        harness.expect_rejected(r, name)
        print(f'{name:28} rejected as expected ({r.get("error", "")[:40]})')
        return
    harness.expect_ok(r, name)
    assert r['cost'] == estimate, (name, r['cost'], estimate)
    print(f'{name:28} cost {r["cost"]:>10,}  (block {e.c:>10,})  prog {r["program_bytes"]:>5} B  ok')


def main():
    reference()
    rng = random.Random(2)
    st = [rng.getrandbits(64) for _ in range(25)]
    run('keccak_f', 25, 64, lambda be, a: K.Keccak(be).permute(be.subtree(a)), st, K.keccak_f(st), 64, 25)
    for n in range(1, 10):
        ws = [rng.getrandbits(256) for _ in range(n)]
        digest = int.from_bytes(K.keccak256(b''.join(x.to_bytes(32, 'big') for x in ws)), 'big')
        run(f'keccak256_{n}w', n, 256, lambda be, a: K.Keccak(be).hash_words(a), ws, [digest], 256, 1)
    ws = [rng.getrandbits(256) for _ in range(3)]
    digest = int.from_bytes(K.keccak256(b''.join(x.to_bytes(32, 'big') for x in ws)), 'big')
    run('keccak256_wrong', 3, 256, lambda be, a: K.Keccak(be).hash_words(a), ws, [digest ^ 1], 256, 1, ok=False)
    print('all ok')


if __name__ == '__main__':
    main()
