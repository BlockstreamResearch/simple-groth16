"""The Groth16 verifier: e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta), L = IC_0 + sum a_i IC_i.

The program checks e(-A, B) e(L, gamma) e(C, delta) e(alpha, beta) = 1 as one polynomial identity
(pairing.py).  The verifying key is compiled in: the IC points become the MSM tables (curve.py), gamma
and delta the line constants of the loop, and the Miller value of (alpha, beta) the constant of the
final relation.

The witness, all field words in Montgomery form (x R mod p, R = 2^256 - 2^32 - 977):

    ((public inputs, MSM slopes), the check's witness (pairing.witness_shape))

-A is given instead of A, so the program negates nothing.  `witness` computes everything from a proof.
The public inputs are range-checked (a_i < r).

Transaction binding (depth > 0): the circuit's only public input is the SHA-256 Merkle root of its
public values, with the sighash of the spending transaction as leaf 0 (merkle.py).  The witness carries
the siblings of leaf 0, and the program recomputes the root from its sig_all_hash jet, so the proof is
valid for this transaction only.

Padding: a program's cost in mWU must not exceed 1000 times the size of its input's witness stack in
bytes (plus 50).  The verifier's bytes earn more than it costs, so it needs no padding.  For programs
that do, the witness can carry blocks of 512 zero bytes (Elements does not relay an annex, where
rust-simplicity would put padding).  Each block must be read by a jet to get a type (an unused witness
gets the unit type), so it is hashed into a fresh SHA-256 context that is then dropped: about 25.5 k mWU
per block, 5% of the 512 WU it earns.

The witness is the balanced pair of its parts: main, siblings, padding (those present).
"""
from . import bn254, merkle
from .fp import Fp, Val, to_mont
from .sym import Sym, E, words, is_sym, SHA_CTX_W
from .curve import Curve, MSM_X_HI, MSM_Y_HI
from . import pairing
from .pairing import PairingCheck
from .dsl import ensure, wv, wpair, wbalanced, Tbalanced, balanced_paths

PAD_BLOCK = Tbalanced(['2^512'] * 8) # 2^4096: 512 bytes
PAD_BLOCK_COST = 25500 # mWU per block: its share of the witness node and of main's comp, init, read, add_512, drop
SHA_PAD64 = (0x80 << 504) | 512 # the second SHA-256 block of a 64-byte message: 0x80, zeros, the bit length

R = bn254.R


class Groth16:
    """Generator of the verifier of vk = dict(alpha, beta, gamma, delta, ic) (bn254 points).  w: MSM
    window width in bits; b: pairing.bounds(); depth: depth of the public-signal Merkle tree (0: no
    transaction binding)."""

    def __init__(self, fp, vk, w=5, nbits=254, b=None, pad_blocks=0, depth=0):
        self.fp, self.be = fp, fp.be
        self.cv = Curve(fp)
        self.vk, self.w, self.nbits, self.pad_blocks, self.depth = vk, w, nbits, pad_blocks, depth
        self.n = len(vk['ic']) - 1
        self.nwin = (nbits + w - 1) // w
        self.tables, offset = Curve.msm_tables(vk['ic'][1:], w, nbits)
        self.start = bn254.g1_add(vk['ic'][0], offset)
        self.pc = PairingCheck(fp, vk['gamma'], vk['delta'], bn254.multi_miller_loop_affine([(vk['alpha'], vk['beta'])]), b)

    # prover side
    def witness(self, proof, inputs, sighash=None, siblings=None):
        """The witness of the proof (A, B, C) for the public inputs, as a dict; None if the proof does not
        verify.  With a binding, also the sighash (leaf 0) and its siblings (merkle.siblings), which must
        give the first input."""
        A, B, C = proof
        ensure(len(inputs) == self.n and all(0 <= a < R for a in inputs), 'public inputs')
        msm_hints, L = Curve.msm_hints(self.start, inputs, self.tables, self.w, self.nbits)
        nA = bn254.g1_neg(A)
        wit = self.pc.prover.witness([(nA, B), (L, self.vk['gamma']), (C, self.vk['delta'])], inputs)
        if wit is None:
            return None
        wit.update(scalars=list(inputs), msm_hints=[to_mont(h) for hi in msm_hints for h in hi])
        if self.depth:
            ensure(len(siblings) == self.depth, 'number of siblings')
            wit['sighash'] = int.from_bytes(merkle.leaf(sighash), 'big')
            wit['siblings'] = [int.from_bytes(merkle.leaf(x), 'big') for x in siblings]
            if self.root(wit['sighash'], wit['siblings']) != inputs[0]:
                return None
        return wit

    @staticmethod
    def root(sighash, siblings):
        """The public input that the siblings of leaf 0 bind to the sighash."""
        h = merkle.leaf(sighash)
        for s in siblings:
            h = merkle.node(h, merkle.leaf(s))
        return merkle.public_signal(h)

    def _parts(self):
        return ['main'] + (['siblings'] if self.depth else []) + (['pad'] if self.pad_blocks else [])

    def witness_type(self):
        """The witness type, in the human-readable encoding."""
        T = lambda k: Tbalanced(['2^256'] * k)
        main = f'(({T(self.n)} * {T(self.n * self.nwin)}) * {pairing.witness_type()})'
        parts = dict(main=lambda: main, siblings=lambda: T(self.depth), pad=lambda: Tbalanced([PAD_BLOCK] * self.pad_blocks))
        return Tbalanced([parts[p]() for p in self._parts()])

    def witness_bits(self):
        return 256 * (self.n + self.n * self.nwin + self.depth) + pairing.witness_bits() + 4096 * self.pad_blocks

    def witness_value(self, wit):
        """The witness dict as a harness value spec (tools/harness)."""
        W = lambda ws: wbalanced([wv(256, x) for x in ws])
        main = wpair(wpair(W(wit['scalars']), W(wit['msm_hints'])), pairing.witness_value(wit))
        parts = dict(main=lambda: main, siblings=lambda: W(wit['siblings']),
                     pad=lambda: wbalanced([wbalanced([wv(512, 0)] * 8) for _ in range(self.pad_blocks)]))
        return wbalanced([parts[p]() for p in self._parts()])

    def witness_shape(self, pad=True):
        main = [[words(self.n), words(self.n * self.nwin)], pairing.witness_shape()]
        parts = dict(main=main, siblings=words(self.depth), pad=[E('', 4096, 0) for _ in range(self.pad_blocks)])
        return [parts[p] for p in self._parts() if pad or p != 'pad']

    # the verifier
    def verify(self, acc):
        """All checks on the witness accessors `acc` (nested like witness_shape).  Sym: a unit-typed E
        over the witness environment; Num: runs the checks on the values."""
        be, cv = self.be, self.cv
        parts = dict(zip(self._parts(), acc))
        main = parts['main']
        (scalars, msm_hints), rest = main
        sc = [Val(a, R - 1) for a in scalars]
        if is_sym(be):
            state = cv.msm_sym(sc, be.subtree(msm_hints), self.tables, self.start, self.w, self.nbits)
            self.parts = {'msm': state.c} # cost attribution
            shape = [[E('', 256, 0), E('', 256, 0), words(self.n)], self.witness_shape(pad=False)[0]]
            main_bits = self.witness_bits() - 256 * self.depth - 4096 * self.pad_blocks
            out = be.with_env(be.pair(state, be.proj(balanced_paths(len(self._parts()))[0], main_bits)), shape, self.checks)
            extra = []
            if self.depth:
                extra.append(self.binding(scalars[0], parts['siblings']))
            if self.pad_blocks:
                extra += self.consume_padding(parts['pad'])
            return be.checks([out] + extra) if extra else out
        hints = [[Val(msm_hints[i * self.nwin + j], 0) for j in range(self.nwin)] for i in range(self.n)]
        (x, y), checks = cv.msm(sc, hints, self.tables, self.start, self.w, self.nbits)
        if self.depth:
            self.binding(scalars[0], parts['siblings'])
        return self.checks([[x.e, y.e, scalars], main])

    def checks(self, accs):
        """The pairing check on (-A, B, C) and L from the MSM state, and the range checks of the inputs."""
        be, cv = self.be, self.cv
        (x, y, scalars), (_, ((pts, (c, ci)), ((sel, rz), (leaves, q)))) = accs
        L = (Val(x, MSM_X_HI), Val(y, MSM_Y_HI))
        chk = self.pc.program({'L': L, 'words': scalars}, pts, c, ci, sel, rz, leaves, q)
        ranges = [cv.lt_const_check(Val(a, 0), R) for a in scalars]
        if not is_sym(be):
            return 0
        self.parts.update(self.pc.parts)
        self.parts['range checks'] = sum(v.e.c for v in ranges)
        return be.checks([chk] + [v.e for v in ranges])

    def binding(self, a1, siblings):
        """The first public input equals the masked root of the path from the sig_all_hash jet through
        the siblings.  Num: siblings is (sighash, siblings)."""
        be = self.be
        if not is_sym(be):
            sighash, sibs = siblings
            ensure(self.root(sighash, sibs) == a1, 'transaction binding failed')
            return 0
        h = be.jet('sig_all_hash', be.unit(), 256)
        for s in siblings:
            h = self.sha256_64(h, s)

        def masked(accs):
            hv, a = accs
            top = be.jet('and_8', be.pair(be.sub(hv, 'OOOOO', 8), be.const(8, 0x1f)), 8)
            m = be.pair(be.pair(be.pair(be.pair(be.pair(top, be.sub(hv, 'OOOOI', 8)), be.sub(hv, 'OOOI', 16)),
                                        be.sub(hv, 'OOI', 32)), be.sub(hv, 'OI', 64)), be.sub(hv, 'I', 128))
            return be.verify(be.eq256(a, m))
        out = be.scope([h, a1], masked)
        self.parts['binding'] = out.c
        return out

    def sha256_64(self, a, b):
        """SHA-256 of the 64-byte message a || b: two compressions."""
        be = self.be
        iv = be.jet('sha_256_iv', be.unit(), 256)
        m = be.jet('sha_256_block', be.pair(iv, be.pair(a, b)), 256)
        return be.jet('sha_256_block', be.pair(m, be.const(512, SHA_PAD64)), 256)

    def program(self):
        """Sym: the unit-typed E of the whole verifier over the witness environment."""
        self.be.env[0] = self.witness_bits()
        return self.verify(self.be._unpack('', self.witness_shape()))

    def num_input(self, wit):
        """The witness dict as the nested value `verify` takes on the numeric backend."""
        main = [[wit['scalars'], wit['msm_hints']], pairing.witness_num(wit)]
        parts = dict(main=main, siblings=[wit.get('sighash'), wit.get('siblings')], pad=[0] * self.pad_blocks)
        return [parts[p] for p in self._parts()]

    def consume_padding(self, blocks):
        """One unit-typed E per padding block: the block is hashed into a fresh context, then dropped."""
        be = self.be
        out = []
        for blk in blocks:
            init = be.jet('sha_256_ctx_8_init', be.unit(), SHA_CTX_W)
            ctx = be.jet('sha_256_ctx_8_add_512', be.pair(init, blk), SHA_CTX_W)
            out.append(be.comp(ctx, be.unit()))
        return out

    @classmethod
    def compile(cls, vk, w=5, pad_blocks=0, depth=0, b=None):
        """The verifier of a key: (program text, its generator, cost bound in mWU)."""
        be = Sym(0)
        g = cls(Fp(be), vk, w, b=b or pairing.bounds(), pad_blocks=pad_blocks, depth=depth)
        body = g.program()
        be.em.define('w_in', 'witness', f'_ -> {g.witness_type()}')
        be.em.define('main', f'comp w_in ({body.t})')
        return be.em.text(), g, 2 * (100 + g.witness_bits()) + body.c

    @staticmethod
    def padding(cost, program_bytes, witness_bytes, margin=512):
        """Number of 512-byte padding blocks that make the input's budget cover the cost.  The budget is
        1000 mWU per byte of the witness stack (program, witness, control block, length prefixes) plus
        50; each block also adds PAD_BLOCK_COST.  The margin covers the CMR and small size changes."""
        need = (cost + 999) // 1000 - 50 - (program_bytes + witness_bytes + 33 + 9) + margin
        k = max(0, (need + 511) // 512)
        return k + (k * PAD_BLOCK_COST + 511999) // 512000 # the blocks' own cost

    @staticmethod
    def budget_ok(cost, program_bytes, witness_bytes):
        return cost <= 1000 * (program_bytes + witness_bytes + 33 + 9 + 50)
