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

A shorter signal.  The verifier pays for every 8 bits of a public input, so the signal may be cut to its
low `bits` bits, a multiple of 8 from MIN_BITS to 248 (`check_bits`), in the circuit and in the program
alike.  Another transaction, or other siblings, with the same signal is then a second preimage of a
`bits`-bit hash, 2^bits work; two transactions with the same signal are a collision, 2^(bits / 2) work,
which matters wherever someone other than the prover has a say in the transaction or in the values.

The lower bound is not about that margin.  A shorter signal takes bytes off the program faster than cost,
and below 184 bits the Groth16 verifier of one input costs more than its bytes pay for: every spend of
such a program would be refused, and the coins of its output lost.  tests/test_binding.py checks that the
budget covers the cost at MIN_BITS.
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from typing import Any

from .dsl import ensure

SIGNAL_BITS = 253  # the bits of the signal: a root, or a sighash, without its top three bits
MIN_BITS = 184  # the shortest signal whose verifier the input's budget still pays for
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


def check_bits(bits: int) -> int:
    """The bits of a signal: 253, or a multiple of 8 from MIN_BITS to 248."""
    ok = bits == SIGNAL_BITS or (MIN_BITS <= bits <= 248 and bits % 8 == 0)
    ensure(ok, f'a signal has 253 bits, or a multiple of 8 from {MIN_BITS} to 248')
    return bits


def public_signal(root_bytes: bytes, bits: int = SIGNAL_BITS) -> int:
    """The root as the circuit's public signal: its low `bits` bits (253: the top three bits cleared)."""
    return int.from_bytes(root_bytes, 'big') & (2 ** check_bits(bits) - 1)


def sighash_limbs(sighash: int | bytes) -> list[int]:
    """The circuit's encoding of the sighash: two 128-bit limbs, high then low."""
    v = int.from_bytes(leaf(sighash), 'big')
    return [v >> 128, v & (2**128 - 1)]


def bound_signal(sighash: bytes | int, siblings: Sequence[bytes | int], bits: int = SIGNAL_BITS) -> int:
    """The public input that the siblings of leaf 0 bind to the sighash (none: the masked sighash)."""
    h = leaf(sighash)
    for s in siblings:
        h = node(h, leaf(s))
    return public_signal(h, bits)


# ---------------------------------------------------------------------------------------------------
# The program's checks (Sym)
def sha256_64(be: Any, a: Any, b: Any) -> Any:
    """SHA-256 of the 64-byte message a || b: two compressions."""
    iv = be.jet('sha_256_iv', be.unit(), 256)
    m = be.jet('sha_256_block', be.pair(iv, be.pair(a, b)), 256)
    return be.jet('sha_256_block', be.pair(m, be.const(512, SHA_PAD64)), 256)


def root_check(be: Any, a1: Any, siblings: Sequence[Any], bits: int = SIGNAL_BITS) -> Any:
    """A unit-typed E: the word a1 is the masked root of the path from the sig_all_hash jet through the
    siblings (words), or, with none, the masked sighash.  The whole word is compared, so a1 is below
    2^bits."""
    check_bits(bits)
    h = be.jet('sig_all_hash', be.unit(), 256)
    for s in siblings:
        h = sha256_64(be, h, s)

    def low(hv, path='', lo=0, width=256):
        """The chunk of hv at `path`, bits lo .. lo + width - 1, with the bits from `bits` up cleared: the
        chunk itself, a zero constant, or the pair of its two halves."""
        if lo + width <= bits:
            return be.sub(hv, path, width)
        if lo >= bits:
            return be.const(width, 0)
        return be.pair(low(hv, path + 'O', lo + width // 2, width // 2), low(hv, path + 'I', lo, width // 2))

    def masked(accs):
        hv, a = accs
        if bits != SIGNAL_BITS:  # a multiple of 8
            return be.verify(be.eq256(a, low(hv)))
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
