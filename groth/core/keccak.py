"""Keccak-f[1600] and Keccak-256 in Simplicity, from the 64-bit jets.

Simplicity has no Keccak jet.  The permutation is built from xor_xor_64 (theta's column parities),
xor_64, left_rotate_64 (rho) and ch_64 (chi: b0 ^ (~b1 & b2) = ch(b1, b0, b0 ^ b2)), about 120 jets per
round.  A round is one function, ROUND: (round constant, 25 lanes) -> 25 lanes, and the permutation
KECCAKF calls it 24 times; both are defined once per program.  The state is a balanced tree of the 25
lanes, lane x + 5 y at position x + 5 y, each lane a 64-bit word holding the lane's 8 bytes little-endian
(Keccak's convention).

Keccak-256 (the original padding, 0x01 ... 0x80, as Ethereum and snarkjs use; SHA3-256 pads with 0x06) of
a message made of 32-byte big-endian words, the form snarkjs's transcript hashes: each word is 4 lanes,
whose bytes are the word's bytes in order, so building a lane only re-pairs byte projections of the word
(no jet).  The 136-byte rate is 17 lanes: block boundaries cut words, which does not matter lane by lane.
The digest is the first 4 lanes, re-paired into a big-endian word.

The reference functions (keccak_f, keccak256, sha3_256) are plain Python; the tests check them against
hashlib's SHA3-256, which uses the same permutation.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from .dsl import ensure
from .sym import JET_COST, E, is_sym

# rust-simplicity 0.9, src/jet/init/elements.rs (fn cost)
JET_COST.update({'xor_64': 95, 'xor_xor_64': 93, 'ch_64': 91, 'left_rotate_64': 98})

M64 = (1 << 64) - 1
RATE_LANES = 17  # 136 bytes


def _round_constants() -> list[int]:
    out, r = [], 1
    for _ in range(24):
        c = 0
        for j in range(7):
            r = ((r << 1) ^ ((r >> 7) * 0x71)) % 256
            if r & 2:
                c |= 1 << ((1 << j) - 1)
        out.append(c)
    return out


def _rotations() -> list[list[int]]:
    rot = [[0] * 5 for _ in range(5)]  # rot[x][y]
    x, y = 1, 0
    for t in range(24):
        rot[x][y] = ((t + 1) * (t + 2) // 2) % 64
        x, y = y, (2 * x + 3 * y) % 5
    return rot


RC = _round_constants()
ROT = _rotations()


# ---------------------------------------------------------------------------------------------------
# The reference
def rol(v: int, n: int) -> int:
    return ((v << n) | (v >> (64 - n))) & M64 if n else v


def keccak_round(a: Sequence[int], rc: int) -> list[int]:
    """One round on the lanes a[x + 5 y]."""
    c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
    d = [c[(x - 1) % 5] ^ rol(c[(x + 1) % 5], 1) for x in range(5)]
    b = [0] * 25
    for x in range(5):
        for y in range(5):
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rol(a[x + 5 * y] ^ d[x], ROT[x][y])
    out = [b[x + 5 * y] ^ (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]) for y in range(5) for x in range(5)]
    out[0] ^= rc
    return out


def keccak_f(a: Sequence[int]) -> list[int]:
    a = list(a)
    for rc in RC:
        a = keccak_round(a, rc)
    return a


def _sponge(msg: bytes, pad: int) -> bytes:
    m = bytearray(msg) + bytes([pad]) + bytes((-len(msg) - 1) % 136)
    m[-1] |= 0x80
    st = [0] * 25
    for off in range(0, len(m), 136):
        for i in range(RATE_LANES):
            st[i] ^= int.from_bytes(m[off + 8 * i : off + 8 * i + 8], 'little')
        st = keccak_f(st)
    return b''.join(st[i].to_bytes(8, 'little') for i in range(4))


def keccak256(msg: bytes) -> bytes:
    """Keccak-256, the original padding (Ethereum's)."""
    return _sponge(msg, 0x01)


def sha3_256(msg: bytes) -> bytes:
    """SHA3-256 (FIPS 202): the same sponge with 0x06."""
    return _sponge(msg, 0x06)


def word_lanes(w: int) -> list[int]:
    """The 4 lanes of a 32-byte big-endian word."""
    b = w.to_bytes(32, 'big')
    return [int.from_bytes(b[8 * j : 8 * j + 8], 'little') for j in range(4)]


def lanes_word(lanes: Sequence[int]) -> int:
    """The big-endian word of 4 lanes (the digest)."""
    return int.from_bytes(b''.join(x.to_bytes(8, 'little') for x in lanes), 'big')


def message_lanes(n_words: int) -> list[Any]:
    """The lanes of a message of n_words words with Keccak-256's padding, by block: each lane is ('w', i, j)
    (lane j of word i), ('k', value) (padding) or None (zero)."""
    lanes: list[Any] = [('w', i, j) for i in range(n_words) for j in range(4)]
    n = len(lanes)
    total = -(-(n + 1) // RATE_LANES) * RATE_LANES
    lanes += [None] * (total - n)
    first, last = 0x01, 0x80 << 56
    lanes[n] = ('k', first | (last if n == total - 1 else 0))
    if n != total - 1:
        lanes[-1] = ('k', last)
    return [lanes[i : i + RATE_LANES] for i in range(0, total, RATE_LANES)]


# ---------------------------------------------------------------------------------------------------
# The program
def lanes_shape() -> list[E]:
    return [E('', 64, 0) for _ in range(25)]


class Keccak:
    """Keccak-f and Keccak-256 over a backend (Sym: expressions; Num: numbers)."""

    def __init__(self, be: Any) -> None:
        self.be = be

    def round_fn(self) -> E:
        """ROUND: (rc, 25 lanes) -> 25 lanes.  theta's column parities are bound once (let), then D;
        rho and pi give B, bound in a scope of its own (with rc), and chi reads B."""
        be = self.be
        if 'ROUND' in be.fns:
            return be.fns['ROUND']

        def body(accs):
            rc, a = accs
            xx = lambda p, q, r: be.jet('xor_xor_64', be.pair(p, be.pair(q, r)), 64)
            xor = lambda p, q: be.jet('xor_64', be.pair(p, q), 64)

            def rot(e, n):
                return be.jet('left_rotate_64', be.pair(be.const(8, n), e), 64) if n else e

            def c_body(c, lift):
                def d_body(d, lift2):
                    al = [lift2(lift(e)) for e in a]
                    bl: list[Any] = [None] * 25
                    for x in range(5):
                        for y in range(5):
                            bl[y + 5 * ((2 * x + 3 * y) % 5)] = rot(xor(al[x + 5 * y], d[x]), ROT[x][y])

                    def chi(bs):
                        rcb, b = bs[0], bs[1:]
                        out = []
                        for y in range(5):
                            for x in range(5):
                                b0, b1, b2 = b[x + 5 * y], b[(x + 1) % 5 + 5 * y], b[(x + 2) % 5 + 5 * y]
                                t = be.jet('ch_64', be.pair(b1, be.pair(b0, xor(b0, b2))), 64)
                                out.append(xor(t, rcb) if x == 0 and y == 0 else t)
                        return be.pack(out)

                    return be.scope([lift2(lift(rc))] + bl, chi)

                d = [xor(c[(x - 1) % 5], rot(c[(x + 1) % 5], 1)) for x in range(5)]
                return be.let(d, d_body)

            cols = [xx(xx(a[x], a[x + 5], a[x + 10]), a[x + 15], a[x + 20]) for x in range(5)]
            return be.let(cols, c_body)

        be.fns['ROUND'] = be.function('ROUND', [E('', 64, 0), lanes_shape()], body)
        return be.fns['ROUND']

    def keccakf_fn(self) -> E:
        """KECCAKF: 25 lanes -> 25 lanes, the 24 rounds."""
        be = self.be
        if 'KECCAKF' in be.fns:
            return be.fns['KECCAKF']
        rnd = self.round_fn()

        def body(accs):
            st = be.subtree(accs)
            for rc in RC:
                st = be.comp(be.pair(be.const(64, rc), st), rnd)
            return st

        be.fns['KECCAKF'] = be.function('KECCAKF', lanes_shape(), body)
        return be.fns['KECCAKF']

    def permute(self, state: Any) -> Any:
        """Keccak-f of a state: Sym, an E of the 25-lane tree; Num, a list of 25 ints."""
        if not is_sym(self.be):
            return keccak_f(state)
        return self.be.comp(state, self.keccakf_fn())

    def word_lanes(self, w: Any) -> list[Any]:
        """The 4 lanes of a projected 256-bit big-endian word: byte k of lane j is byte 8 j + k of the word,
        and a lane holds its bytes little-endian, so each lane re-pairs 8 byte projections."""
        be = self.be
        if not is_sym(be):
            return word_lanes(w)
        ensure(w.path is not None and w.w == 256, 'a projected 256-bit word')
        byte = lambda i: be.sub(w, ''.join('O' if (i >> (4 - b)) & 1 == 0 else 'I' for b in range(5)), 8)
        return [be.pack([byte(8 * j + k) for k in range(7, -1, -1)]) for j in range(4)]

    def digest_word(self, state: Any) -> Any:
        """The digest, lanes 0 .. 3 of a state, as a big-endian word.  Sym: state is a projected 25-lane tree."""
        be = self.be
        if not is_sym(be):
            return lanes_word(state[:4])
        lanes = be.split(state, lanes_shape())
        byte = lambda lane, k: be.sub(lane, ''.join('O' if (k >> (2 - b)) & 1 == 0 else 'I' for b in range(3)), 8)
        # byte 8 j + k of the digest is byte k of lane j, its (7 - k)-th byte from the top
        return be.pack([byte(lanes[j], 7 - k) for j in range(4) for k in range(8)])

    def hash_words(self, words: Sequence[Any]) -> Any:
        """Keccak-256 of the 32-byte big-endian words (projections, or ints for constant words), as a
        big-endian word."""
        be = self.be
        n = len(words)
        if not is_sym(be):
            return int.from_bytes(keccak256(b''.join(w.to_bytes(32, 'big') for w in words)), 'big')
        # a constant word (an int) gives constant lanes, made where they are used
        lanes = [word_lanes(w) if isinstance(w, int) else self.word_lanes(w) for w in words]

        def lane(spec):
            if spec is None:
                return be.const(64, 0)
            if spec[0] == 'k':
                return be.const(64, spec[1])
            x = lanes[spec[1]][spec[2]]
            return be.const(64, x) if isinstance(x, int) else x

        blocks = message_lanes(n)
        state = self.permute(be.pack([lane(s) for s in blocks[0]] + [be.const(64, 0)] * (25 - RATE_LANES)))
        for blk in blocks[1:]:
            state = self._absorb(state, blk, lane)
        return be.with_env(state, lanes_shape(), lambda st: self.digest_word(be.subtree(st)))

    def _absorb(self, state: E, blk: Sequence[Any], lane: Any) -> E:
        """Xor a block into a computed state, then permute.  The block's lanes are read from the outer
        environment, lifted into the state's."""
        be = self.be

        def body(st, lift):
            out = []
            for i in range(25):
                spec = blk[i] if i < RATE_LANES else None
                if spec is None:
                    out.append(st[i])
                else:
                    if spec[0] == 'k':
                        m = be.const(64, spec[1])
                    else:
                        x = lane(spec)
                        m = x if x.t.startswith('k') else lift(x)  # constants are made in this environment
                    out.append(be.jet('xor_64', be.pair(st[i], m), 64))
            return self.permute(be.pack(out))

        return be.let(_one(state), lambda accs, lift: body(be.split(accs[0], lanes_shape()), lift))


def _one(e: E) -> list[E]:
    return [e]


def hash_words_cost_terms(n_words: int) -> dict[str, int]:
    """How many permutations and absorbed blocks hash_words of n_words words takes."""
    blocks = message_lanes(n_words)
    return {'permutations': len(blocks), 'xored blocks': len(blocks) - 1}
