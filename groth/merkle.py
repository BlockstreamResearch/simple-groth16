"""The public-signal convention (the Python side of circuits/public_merkle.circom).

A circuit for this verifier has one public signal: the SHA-256 Merkle root of its public values, with
the sighash of the spending transaction as leaf 0.

    leaves:  32 bytes each; leaf 0 is the sighash, leaf i the i-th public value, big-endian
    tree:    2^depth leaves, depth = max(1, ceil(log2(number of leaves))), missing leaves are zero
    node:    SHA-256(left || right)
    signal:  the root with its top three bits cleared, so that it is below r

The program gets the siblings of leaf 0 in its witness and recomputes the root from its sig_all_hash
jet (groth16.py, `binding`).
"""
import hashlib

MASK = 2**253 - 1


def leaf(v):
    """A 32-byte leaf from an int (big-endian) or bytes."""
    if isinstance(v, bytes):
        assert len(v) == 32, 'a leaf is 32 bytes'
        return v
    return v.to_bytes(32, 'big')


def node(left, right):
    return hashlib.sha256(left + right).digest()


def depth_of(n_leaves):
    d = 0
    while 2**d < n_leaves:
        d += 1
    return max(d, 1)


def levels(leaves, depth=None):
    """The levels of the tree, bottom-up: the padded leaves first, the root (a one-item list) last."""
    leaves = [leaf(v) for v in leaves]
    depth = depth_of(len(leaves)) if depth is None else depth
    assert len(leaves) <= 2**depth
    level = leaves + [bytes(32)] * (2**depth - len(leaves))
    out = [level]
    while len(level) > 1:
        level = [node(level[i], level[i + 1]) for i in range(0, len(level), 2)]
        out.append(level)
    return out


def root(leaves, depth=None):
    return levels(leaves, depth)[-1][0]


def siblings(leaves, index=0, depth=None):
    """The siblings of leaf `index` along its path, bottom-up."""
    out = []
    for level in levels(leaves, depth)[:-1]:
        out.append(level[index ^ 1])
        index >>= 1
    return out


def public_signal(root_bytes):
    """The root as the circuit's public signal: top three bits cleared."""
    return int.from_bytes(root_bytes, 'big') & MASK


def sighash_limbs(sighash):
    """The circuit's encoding of the sighash: two 128-bit limbs, high then low."""
    v = int.from_bytes(leaf(sighash), 'big')
    return [v >> 128, v & (2**128 - 1)]
