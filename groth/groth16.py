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

The witness node w_in is the balanced pair of main and, with a binding, the siblings.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from . import bn254, merkle, pairing
from .curve import Curve
from .dsl import CheckFailed, Tbalanced, WSpec, balanced_paths, ensure, wbalanced, wpair, wv
from .fp import Fp, Val
from .pairing import PairingCheck
from .sym import E, Sym, Term, is_sym, words

SHA_PAD64 = (0x80 << 504) | 512  # the second SHA-256 block of a 64-byte message: 0x80, zeros, the bit length

R = bn254.R
VerifyingKey = dict[str, Any]  # alpha, beta, gamma, delta (bn254 points) and ic (a list of G1 points)
Proof = tuple[bn254.G1Point, bn254.G2Point, bn254.G1Point]


class Groth16:
    """Generator of the verifier of vk = dict(alpha, beta, gamma, delta, ic) (bn254 points).  b:
    pairing.bounds(); depth: depth of the public-signal Merkle tree (0: no transaction binding)."""

    def __init__(self, fp: Fp, vk: VerifyingKey, b: dict[str, int] | None = None, depth: int = 0) -> None:
        self.fp, self.be = fp, fp.be
        self.cv = Curve(fp)
        self.vk, self.depth = vk, depth
        self.n = len(vk['ic']) - 1
        ensure(self.n >= 1, 'the key has no public input')
        ensure(depth >= 0 and (depth == 0 or self.n == 1), 'a bound circuit has one public signal')
        self.pc = PairingCheck(
            fp,
            vk['delta'],
            bn254.multi_miller_loop_affine([(vk['alpha'], vk['beta'])]),
            pairing.gt_constants(vk['ic'], vk['gamma']),
            b,
        )

    # prover side
    def witness(
        self,
        proof: Proof,
        inputs: Sequence[int],
        sighash: bytes | int | None = None,
        siblings: Sequence[bytes | int] | None = None,
    ) -> dict[str, Any] | None:
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
            if sighash is None or siblings is None or len(siblings) != self.depth:
                raise CheckFailed('the sighash and its siblings')
            wit['sighash'] = int.from_bytes(merkle.leaf(sighash), 'big')
            wit['siblings'] = [int.from_bytes(merkle.leaf(x), 'big') for x in siblings]
            if self.root(wit['sighash'], wit['siblings']) != inputs[0]:
                return None
        return wit

    @staticmethod
    def root(sighash: bytes | int, siblings: Sequence[bytes | int]) -> int:
        """The public input that the siblings of leaf 0 bind to the sighash."""
        h = merkle.leaf(sighash)
        for s in siblings:
            h = merkle.node(h, merkle.leaf(s))
        return merkle.public_signal(h)

    def _with_siblings(self, main: Any, siblings: Any) -> list[Any]:
        """The parts of w_in: main, and the siblings if there is a binding."""
        return [main, siblings] if self.depth else [main]

    def witness_type(self) -> str:
        """The type of w_in, in the human-readable encoding."""
        main = f'({_words_type(self.n)} * {pairing.witness_type()})'
        return f'({main} * {_words_type(self.depth)})' if self.depth else main

    def witness_bits(self) -> int:
        """The bits of the program's witness node, w_in."""
        return 256 * (self.n + self.depth) + pairing.witness_bits()

    def witness_value(self, wit: dict[str, Any]) -> dict[str, WSpec]:
        """The witness dict as harness value specs (tools/harness), by witness node: w_in, the leaves and Q."""
        W = lambda ws: wbalanced([wv(256, x) for x in ws])
        main = wpair(W(wit['scalars']), pairing.witness_value(wit))
        w_in = wpair(main, W(wit['siblings'])) if self.depth else main
        return {'w_in': w_in, **pairing.witness_nodes(wit)}

    def witness_shape(self) -> list[Any]:
        return self._with_siblings([words(self.n), pairing.witness_shape()], words(self.depth))

    def num_input(self, wit: dict[str, Any]) -> list[Any]:
        """The witness dict as the nested value `verify` takes on the numeric backend."""
        return self._with_siblings(
            [wit['scalars'], pairing.witness_num(wit)], [wit.get('sighash'), wit.get('siblings')]
        )

    # the verifier
    def verify(self, acc: Any) -> Term:
        """All checks on the witness accessors `acc` (nested like witness_shape).  Sym: a unit-typed E
        over the witness environment; Num: runs the checks on the values."""
        be = self.be
        if is_sym(be):  # in an environment of main alone
            main_bits = self.witness_bits() - 256 * self.depth
            out = be.with_env(be.proj(balanced_paths(len(acc))[0], main_bits), self.witness_shape()[0], self.checks)
        else:
            out = self.checks(acc[0])
        if self.depth:
            bind = self.binding(acc[0][0][0], acc[1])
            if is_sym(be):
                out = be.checks([out, bind])
        return out if is_sym(be) else 0

    def checks(self, main: Any) -> Term:
        """The pairing check on (-A, B, C) and the public inputs, and the range checks of the inputs."""
        be, cv = self.be, self.cv
        if is_sym(be):  # the leaves and Q are witness nodes of their own
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

    def binding(self, a1: Term, siblings: Any) -> Term:
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
            top = be.jet('and_8', be.pair(be.sub(hv, 'OOOOO', 8), be.const(8, 0x1F)), 8)
            m = be.pair(
                be.pair(
                    be.pair(
                        be.pair(be.pair(top, be.sub(hv, 'OOOOI', 8)), be.sub(hv, 'OOOI', 16)), be.sub(hv, 'OOI', 32)
                    ),
                    be.sub(hv, 'OI', 64),
                ),
                be.sub(hv, 'I', 128),
            )
            return be.verify(be.eq256(a, m))

        out = be.scope([h, a1], masked)
        self.parts['binding'] = out.c
        return out

    def sha256_64(self, a: E, b: E) -> E:
        """SHA-256 of the 64-byte message a || b: two compressions."""
        be = self.be
        iv = be.jet('sha_256_iv', be.unit(), 256)
        m = be.jet('sha_256_block', be.pair(iv, be.pair(a, b)), 256)
        return be.jet('sha_256_block', be.pair(m, be.const(512, SHA_PAD64)), 256)

    def program(self) -> E:
        """Sym: the unit-typed E of the whole verifier over the witness environment."""
        self.be.env[0] = self.witness_bits()
        return self.verify(self.be._unpack('', self.witness_shape()))

    @classmethod
    def compile(cls, vk: VerifyingKey, depth: int = 0, b: dict[str, int] | None = None) -> tuple[str, Groth16, int]:
        """The verifier of a key: (program text, its generator, cost bound in mWU)."""
        be = Sym(0)
        g = cls(Fp(be), vk, b=b or pairing.bounds(), depth=depth)
        body = g.program()
        be.em.define('w_in', 'witness', f'_ -> {g.witness_type()}')
        be.em.define('main', f'comp w_in ({body.t})')
        # each witness node is read once: a spender may unshare a node and give each copy its own value
        uses = be.em.tree_uses()
        nodes = [name for name, expr, _ in be.em.defs if expr == 'witness']
        ensure(len(nodes) == 2 + pairing.N_STEPS, 'the witness nodes')
        ensure(all(uses.get(name) == 1 for name in nodes), 'a witness node is read more than once')
        return be.em.text(), g, 2 * (100 + g.witness_bits()) + body.c

    @staticmethod
    def budget_ok(cost: int, program_bytes: int, witness_bytes: int) -> bool:
        """The input's budget, 1000 mWU per byte of its witness stack plus 50, covers the cost.  The stack is
        counted low: the program, the witness, the control block (33 bytes) and 9 bytes of length prefixes,
        without the CMR's 32 bytes."""
        return cost <= 1000 * (program_bytes + witness_bytes + 33 + 9 + 50)


def _words_type(n: int) -> str:
    return Tbalanced(['2^256'] * n)
