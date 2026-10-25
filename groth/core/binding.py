"""Transaction binding: how a circuit's public inputs name the transaction that spends the output, so that
a proof cannot be replayed or redirected.  Three conventions, each with its plain-Python side and the
program's check (Sym):

    the tree (Groth16, circuits/public_merkle.circom): one public signal, the SHA-256 Merkle root of the
        public values with the sighash as leaf 0; the witness carries the siblings of leaf 0 and the
        program recomputes the root from the sig_all_hash jet (`root_check`)
    the input (Groth16 with sighash_input, Noir circuits): the first public input is the sighash itself,
        masked like a root; a tree with no siblings (`root_check` with none)
    the limbs (fflonk): the first two public inputs are the sighash as two 128-bit limbs, high then low
        (`limbs_check`)

The tree:

    leaves:  32 bytes each; leaf 0 is the sighash, leaf i the i-th public value, big-endian
    tree:    2^depth leaves, depth = max(1, ceil(log2(number of leaves))), missing leaves are zero
    node:    SHA-256(left || right)
    signal:  the root with its top three bits cleared, so that it is below r
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from typing import Any

from .dsl import ensure

MASK = 2**253 - 1
SHA_PAD64 = (0x80 << 504) | 512  # the second SHA-256 block of a 64-byte message: 0x80, zeros, the bit length


def leaf(v: int | bytes) -> bytes:
    """A 32-byte leaf from an int (big-endian) or bytes."""
    if isinstance(v, bytes):
        ensure(len(v) == 32, 'a leaf is 32 bytes')
        return v
    return v.to_bytes(32, 'big')


def node(left: bytes, right: bytes) -> bytes:
    return hashlib.sha256(left + right).digest()


def depth_of(n_leaves: int) -> int:
    d = 0
    while 2**d < n_leaves:
        d += 1
    return max(d, 1)


def levels(leaves: Sequence[int | bytes], depth: int | None = None) -> list[list[bytes]]:
    """The levels of the tree, bottom-up: the padded leaves first, the root (a one-item list) last."""
    items = [leaf(v) for v in leaves]
    depth = depth_of(len(items)) if depth is None else depth
    ensure(len(items) <= 2**depth, 'more leaves than the tree holds')
    level = items + [bytes(32)] * (2**depth - len(items))
    out = [level]
    while len(level) > 1:
        level = [node(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        out.append(level)
    return out


def root(leaves: Sequence[int | bytes], depth: int | None = None) -> bytes:
    return levels(leaves, depth)[-1][0]


def siblings(leaves: Sequence[int | bytes], index: int = 0, depth: int | None = None) -> list[bytes]:
    """The siblings of leaf `index` along its path, bottom-up."""
    out = []
    for level in levels(leaves, depth)[:-1]:
        out.append(level[index ^ 1])
        index >>= 1
    return out


def public_signal(root_bytes: bytes) -> int:
    """The root as the circuit's public signal: top three bits cleared."""
    return int.from_bytes(root_bytes, 'big') & MASK


def sighash_limbs(sighash: int | bytes) -> list[int]:
    """The circuit's encoding of the sighash: two 128-bit limbs, high then low."""
    v = int.from_bytes(leaf(sighash), 'big')
    return [v >> 128, v & (2**128 - 1)]


def bound_signal(sighash: bytes | int, siblings: Sequence[bytes | int]) -> int:
    """The public input that the siblings of leaf 0 bind to the sighash (none: the masked sighash)."""
    h = leaf(sighash)
    for s in siblings:
        h = node(h, leaf(s))
    return public_signal(h)


# ---------------------------------------------------------------------------------------------------
# The program's checks (Sym)
def sha256_64(be: Any, a: Any, b: Any) -> Any:
    """SHA-256 of the 64-byte message a || b: two compressions."""
    iv = be.jet('sha_256_iv', be.unit(), 256)
    m = be.jet('sha_256_block', be.pair(iv, be.pair(a, b)), 256)
    return be.jet('sha_256_block', be.pair(m, be.const(512, SHA_PAD64)), 256)


def root_check(be: Any, a1: Any, siblings: Sequence[Any]) -> Any:
    """A unit-typed E: the word a1 is the masked root of the path from the sig_all_hash jet through the
    siblings (words), or, with none, the masked sighash."""
    h = be.jet('sig_all_hash', be.unit(), 256)
    for s in siblings:
        h = sha256_64(be, h, s)

    def masked(accs):
        hv, a = accs
        top = be.jet('and_8', be.pair(be.sub(hv, 'OOOOO', 8), be.const(8, 0x1F)), 8)
        m = be.pair(
            be.pair(
                be.pair(be.pair(be.pair(top, be.sub(hv, 'OOOOI', 8)), be.sub(hv, 'OOOI', 16)), be.sub(hv, 'OOI', 32)),
                be.sub(hv, 'OI', 64),
            ),
            be.sub(hv, 'I', 128),
        )
        return be.verify(be.eq256(a, m))

    return be.scope([h, a1], masked)


def limbs_check(be: Any, hi: Any, lo: Any) -> Any:
    """A unit-typed E: the words hi and lo (projections) are the high and low 128-bit halves of the
    sig_all_hash jet's sighash: the top half of each is 0, its low half the sighash's."""
    h = be.jet('sig_all_hash', be.unit(), 256)
    pub = [hi, lo]

    def body(acc, lift):
        hv = acc[0]
        out = []
        for k, half in enumerate(('O', 'I')):
            x = lift(pub[k])
            for pth in ('OO', 'OI'):  # the top half of the input is 0
                out.append(be.verify(be.jet('eq_64', be.pair(be.sub(x, pth, 64), be.const(64, 0)), 1)))
            for pth in ('O', 'I'):  # its low half is the sighash's half
                out.append(be.verify(be.jet('eq_64', be.pair(be.sub(x, 'I' + pth, 64), be.sub(hv, half + pth, 64)), 1)))
        return be.checks(out)

    return be.let([h], body)
