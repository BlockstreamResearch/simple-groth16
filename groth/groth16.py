"""The Groth16 verifier: e(A, B) = e(alpha, beta) e(L, gamma) e(C, delta), L = IC_0 + sum a_i IC_i.

The program checks e(-A, B) e(C, delta) e(alpha, beta) e(L, gamma) = 1 as one polynomial identity
(pairing.py).  The verifying key is compiled in: delta gives the line constants of the loop, the Miller
value of (alpha, beta) the constant of the final relation, and the IC points with gamma the tables of the
public inputs' term: e(L, gamma) = e(IC_0, gamma) prod e(IC_i, gamma)^(a_i), so L is never computed.

The witness, the field words in Montgomery form (x R mod p, R = 2^256 - 2^32 - 977): the program's
witness node w_in holds

    (public inputs, the check's witness (pairing.witness_shape))

and the pairing check reads each step's leaf and Q from witness nodes of their own (pairing.witness_nodes).

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
from .fp import Fp, Val
from .sym import Sym, E, words, is_sym, SHA_CTX_W
from .curve import Curve
from . import pairing
from .pairing import PairingCheck
from .dsl import ensure, wv, wpair, wbalanced, Tbalanced, balanced_paths

PAD_BLOCK = Tbalanced(['2^512'] * 8) # 2^4096: 512 bytes
PAD_BLOCK_COST = 25500 # mWU per block: its share of the witness node and of main's comp, init, read, add_512, drop
SHA_PAD64 = (0x80 << 504) | 512 # the second SHA-256 block of a 64-byte message: 0x80, zeros, the bit length

R = bn254.R


class Groth16:
    """Generator of the verifier of vk = dict(alpha, beta, gamma, delta, ic) (bn254 points).  b:
    pairing.bounds(); depth: depth of the public-signal Merkle tree (0: no transaction binding)."""

    def __init__(self, fp, vk, b=None, pad_blocks=0, depth=0):
        self.fp, self.be = fp, fp.be
        self.cv = Curve(fp)
        self.vk, self.pad_blocks, self.depth = vk, pad_blocks, depth
        self.n = len(vk['ic']) - 1
        self.pc = PairingCheck(fp, vk['delta'], bn254.multi_miller_loop_affine([(vk['alpha'], vk['beta'])]),
                               pairing.gt_constants(vk['ic'], vk['gamma']), b)

    # prover side
    def witness(self, proof, inputs, sighash=None, siblings=None):
        """The witness of the proof (A, B, C) for the public inputs, as a dict; None if the proof does not
        verify.  With a binding, also the sighash (leaf 0) and its siblings (merkle.siblings), which must
        give the first input."""
        A, B, C = proof
        ensure(len(inputs) == self.n and all(0 <= a < R for a in inputs), 'public inputs')
        wit = self.pc.prover.witness([(bn254.g1_neg(A), B), (C, self.vk['delta'])], inputs)
        if wit is None:
            return None
        wit.update(scalars=list(inputs))
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
        main = f'({T(self.n)} * {pairing.witness_type(self.n)})'
        parts = dict(main=lambda: main, siblings=lambda: T(self.depth), pad=lambda: Tbalanced([PAD_BLOCK] * self.pad_blocks))
        return Tbalanced([parts[p]() for p in self._parts()])

    def witness_bits(self):
        """The bits of the program's witness node, w_in."""
        return 256 * (self.n + self.depth) + pairing.witness_bits(self.n) + 4096 * self.pad_blocks

    def all_witness_bits(self):
        """With the witness nodes of their own (the pairing check's leaves and Q)."""
        return self.witness_bits() + pairing.witness_node_bits(self.n)

    def witness_value(self, wit):
        """The witness dict as harness value specs (tools/harness), by witness node: w_in, the leaves and Q."""
        W = lambda ws: wbalanced([wv(256, x) for x in ws])
        main = wpair(W(wit['scalars']), pairing.witness_value(wit))
        parts = dict(main=lambda: main, siblings=lambda: W(wit['siblings']),
                     pad=lambda: wbalanced([wbalanced([wv(512, 0)] * 8) for _ in range(self.pad_blocks)]))
        return {'w_in': wbalanced([parts[p]() for p in self._parts()]), **pairing.witness_nodes(wit)}

    def witness_shape(self, pad=True):
        main = [words(self.n), pairing.witness_shape(self.n)]
        parts = dict(main=main, siblings=words(self.depth), pad=[E('', 4096, 0) for _ in range(self.pad_blocks)])
        return [parts[p] for p in self._parts() if pad or p != 'pad']

    # the verifier
    def verify(self, acc):
        """All checks on the witness accessors `acc` (nested like witness_shape).  Sym: a unit-typed E
        over the witness environment; Num: runs the checks on the values."""
        be = self.be
        parts = dict(zip(self._parts(), acc))
        if is_sym(be): # in an environment of main alone
            main_bits = self.witness_bits() - 256 * self.depth - 4096 * self.pad_blocks
            out = be.with_env(be.proj(balanced_paths(len(self._parts()))[0], main_bits), self.witness_shape(pad=False)[0], self.checks)
        else:
            out = self.checks(parts['main'])
        extra = []
        if self.depth:
            extra.append(self.binding(parts['main'][0][0], parts['siblings']))
        if self.pad_blocks:
            extra += self.consume_padding(parts['pad'])
        if not is_sym(be):
            return 0
        return be.checks([out] + extra) if extra else out

    def checks(self, main):
        """The pairing check on (-A, B, C) and the public inputs, and the range checks of the inputs."""
        be, cv = self.be, self.cv
        if is_sym(be): # the leaves and Q are witness nodes of their own
            (scalars, ((pts, ac), rz)), leaves, q = main, None, None
        else:
            scalars, ((pts, ac), (rz, (leaves, q))) = main
        chk = self.pc.program({'x': [Val(a, R - 1) for a in scalars], 'words': scalars}, pts, ac, rz, leaves, q)
        ranges = [cv.lt_const_check(Val(a, 0), R) for a in scalars]
        if not is_sym(be):
            return 0
        self.parts = dict(self.pc.parts)
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
        main = [wit['scalars'], pairing.witness_num(wit)]
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
    def compile(cls, vk, pad_blocks=0, depth=0, b=None):
        """The verifier of a key: (program text, its generator, cost bound in mWU)."""
        be = Sym(0)
        g = cls(Fp(be), vk, b=b or pairing.bounds(), pad_blocks=pad_blocks, depth=depth)
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
