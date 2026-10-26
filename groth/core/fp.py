"""BN254 field arithmetic from the secp256k1 jets: the base field p, and the scalar field r for fflonk
(Field, FP, FR).

An element x of F_q (q = p or r, both 254-bit primes) is a word X = x R mod q in Montgomery form, with
radix R = p_s, the secp256k1 field prime.  X is not reduced: the generator carries a static bound `hi` with
0 <= X <= hi.  A product is computed exactly, in CRT form, by the two secp256k1 jet families, then reduced:

    S = A B                                   fe_multiply(A, B), scalar_multiply(A, B): S mod p_s, S mod n_s
    m = S C1 mod p_s                          C1 = -p^-1 mod p_s
    Q = (S + m p) / p_s                       exact division, since S + m p = 0 (mod p_s)
      = (S + m p) p_s^-1 mod n_s              exact as long as Q < n_s
    Q = A B R^-1 (mod p),  Q <= (S + (p_s - 1) p) / p_s

The bound on S is what keeps Q below n_s, so every accumulator is checked against CRT_MAX when the
program is generated.  Sums of products are accumulated in CRT form and reduced once.  Subtraction adds
a multiple of p first, so every integer stays non-negative.
"""

from __future__ import annotations

from collections.abc import Callable, Container, Sequence
from typing import Any

from . import bn254
from .dsl import ensure, pairwise_sum
from .sym import Backend, E, Term

P_SECP = 2**256 - 2**32 - 977
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
R = P_SECP  # the Montgomery radix
C3 = pow(P_SECP, -1, N_SECP)  # p_s^-1 mod n_s
WORD_MAX = 2**256 - 1


def crt_of(v: int) -> tuple[int, int]:
    """CRT residues of an integer."""
    return v % P_SECP, v % N_SECP


class Field:
    """The constants of the arithmetic modulo an odd prime q below 2^254: BN254's base field p (FP), or its
    scalar field r (FR, for the fflonk verifier).  The method is the same for both; only the constants
    differ."""

    def __init__(self, q: int) -> None:
        ensure(q % 2 == 1 and q < 2**254, 'an odd prime below 2^254')
        self.P = q
        self.R_MOD_P = R % q
        self.R_INV = pow(R, -1, q)
        self.C1 = (-pow(q, -1, P_SECP)) % P_SECP  # -q^-1 mod p_s
        self.C2 = q % N_SECP
        self.C23 = self.C2 * C3 % N_SECP  # q p_s^-1 mod n_s
        self.CRT_MAX = (N_SECP - q) * P_SECP  # exclusive bound on a CRT accumulator: keeps Q < n_s

    def to_mont(self, x: int) -> int:
        return x * R % self.P

    def from_mont(self, X: int) -> int:
        return X * self.R_INV % self.P

    def mult_at_least(self, hi: int) -> int:
        """The smallest multiple of q that is >= hi."""
        return ((hi + self.P - 1) // self.P) * self.P


FP = Field(bn254.P)
FR = Field(bn254.R)
# the base field's constants, as the rest of the generator uses them
P = FP.P
R_MOD_P, R_INV, C1, C2, C23, CRT_MAX = FP.R_MOD_P, FP.R_INV, FP.C1, FP.C2, FP.C23, FP.CRT_MAX
to_mont, from_mont = FP.to_mont, FP.from_mont


class Val:
    """A field element in Montgomery form: backend value `e` (an E or an int), inclusive bound `hi`."""

    __slots__ = ('e', 'hi')

    def __init__(self, e: Term, hi: int) -> None:
        self.e, self.hi = e, hi

    def __repr__(self) -> str:
        return f'Val({self.e!r}, hi={self.hi / P:.3f} p)'


class Crt:
    """An integer in CRT form: residues mod p_s and mod n_s, inclusive bound `hi` on the integer."""

    __slots__ = ('sp', 'sn', 'hi')

    def __init__(self, sp: Term, sn: Term, hi: int) -> None:
        ensure(hi < CRT_MAX, 'CRT accumulator bound exceeded')
        self.sp, self.sn, self.hi = sp, sn, hi


def mult_of_p_at_least(hi: int) -> int:
    """The smallest multiple of p that is >= hi."""
    return FP.mult_at_least(hi)


class Fp:
    """Field operations over a backend (sym.Sym for expressions, sym.Num for numbers), modulo the prime of
    `field`: p by default, or r (FR)."""

    def __init__(self, be: Backend, field: Field = FP) -> None:
        self.be = be
        self.F = field
        self.P = field.P

    # constants and inputs
    def const(self, x: int) -> Val:
        """The field constant x (an integer mod p), in Montgomery form."""
        v = self.F.to_mont(x)
        return Val(self.be.word(v), v)

    def raw(self, e: Term, hi: int = WORD_MAX) -> Val:
        """A backend value with a known bound (default: any 256-bit word, e.g. a witness word)."""
        return Val(e, hi)

    # CRT products
    def crt_mul(self, a: Val, b: Val) -> Crt:
        """a b in CRT form.  Both jets read the operands, so computed operands are evaluated once first;
        reduce_dot avoids that by construction and is preferred."""
        be = self.be
        if a is b:
            sp, sn = self.once([a], lambda v: (be.fe_sqr(v[0].e), be.sc_sqr(v[0].e)))
            return Crt(sp, sn, a.hi * a.hi)
        sp, sn = self.once([a, b], lambda v: (be.fe_mul(v[0].e, v[1].e), be.sc_mul(v[0].e, v[1].e)))
        return Crt(sp, sn, a.hi * b.hi)

    def crt_add(self, x: Crt, y: Crt) -> Crt:
        be = self.be
        return Crt(be.fe_add(x.sp, y.sp), be.sc_add(x.sn, y.sn), x.hi + y.hi)

    def crt_sum(self, terms: Sequence[Crt]) -> Crt:
        return pairwise_sum(terms, self.crt_add)

    def crt_neg(self, x: Crt) -> Crt:
        """c - x for the smallest multiple c of p with c >= hi(x); bound c."""
        be = self.be
        c = self.F.mult_at_least(x.hi)
        cp, cn = crt_of(c)
        return Crt(be.fe_add(be.fe_neg(x.sp), be.word(cp)), be.sc_add(be.sc_neg(x.sn), be.word(cn)), c)

    def reduce_dot(self, pairs: Sequence[tuple[Val, Val]]) -> Val:
        """Sum of products a_i b_i with one reduction.  Every operand is read once (Sym.crt_dot); a pair
        (a, a) uses the squaring jets."""
        be = self.be
        hi = sum(a.hi * b.hi for a, b in pairs)
        ensure(hi < self.F.CRT_MAX, 'CRT accumulator bound exceeded')
        packed = be.crt_dot([(a.e, None if a is b else b.e) for a, b in pairs])
        out_hi = (hi + (P_SECP - 1) * self.P) // P_SECP
        ensure(out_hi < N_SECP, 'reduced bound exceeds n_s')

        def body(acc):
            sp, sn = acc
            m = be.fe_mul(sp, be.word(self.F.C1))
            return be.sc_mul(be.sc_add(sn, be.sc_mul(m, be.word(self.F.C2))), be.word(C3))

        q = be.with_env(packed, [E('', 256, 0), E('', 256, 0)], body)
        return Val(be.check(q, out_hi), out_hi)

    def lin_const(self, terms: Sequence[tuple[Val, int]]) -> Val:
        """Sum of k_i x_i for field constants k_i (any sign, taken mod p).  The constants are folded into
        the reduction, as in mul_const: four jets per term (mul_const is one term)."""
        be = self.be
        hi = sum(x.hi * self.F.to_mont(k % self.P) for x, k in terms)
        ensure(hi < self.F.CRT_MAX, 'CRT accumulator bound exceeded')
        out_hi = (hi + (P_SECP - 1) * self.P) // P_SECP
        ensure(out_hi < N_SECP, 'reduced bound exceeds n_s')

        def body(xs):
            fe_terms, sc_terms = [], []
            for x, (_, k) in zip(xs, terms):
                c = self.F.to_mont(k % self.P)
                fe_terms.append(be.fe_mul(x.e, be.word(c * self.F.C1 % P_SECP)))
                sc_terms.append(be.sc_mul(x.e, be.word(c * C3 % N_SECP)))
            m = pairwise_sum(fe_terms, be.fe_add)
            s = pairwise_sum(sc_terms, be.sc_add)
            return be.sc_add(s, be.sc_mul(m, be.word(self.F.C23)))

        return Val(be.check(self.once([x for x, _ in terms], body), out_hi), out_hi)

    def reduce(self, x: Crt) -> Val:
        """Montgomery reduction of a CRT value: Q = (x + m p) / p_s = x R^-1 (mod p)."""
        be = self.be
        m = be.fe_mul(x.sp, be.word(self.F.C1))
        q = be.sc_mul(be.sc_add(x.sn, be.sc_mul(m, be.word(self.F.C2))), be.word(C3))
        hi = (x.hi + (P_SECP - 1) * self.P) // P_SECP
        ensure(hi < N_SECP, 'reduced bound exceeds n_s')
        return Val(be.check(q, hi), hi)

    def once(self, vals: Sequence[Val], fn: Callable[[list[Val]], Any]) -> Any:
        """fn(vals) with every computed value evaluated once into the environment (see Sym.once)."""
        return self.be.once([v.e for v in vals], lambda es: fn([Val(e, v.hi) for e, v in zip(es, vals)]))

    # field operations
    def mul(self, a: Val, b: Val) -> Val:
        return self.reduce(self.crt_mul(a, b))

    def sqr(self, a: Val) -> Val:
        return self.reduce(self.crt_mul(a, a))

    def mul_const(self, a: Val, x: int) -> Val:
        """a times the field constant x.  The constant is folded into the reduction: 4 jets instead of 6."""
        be = self.be
        c = self.F.to_mont(x)
        hi = (a.hi * c + (P_SECP - 1) * self.P) // P_SECP
        ensure(hi < N_SECP, 'reduced bound exceeds n_s')

        def body(v):
            a = v[0]
            m = be.fe_mul(a.e, be.word(c * self.F.C1 % P_SECP))  # (a c mod p_s) C1
            return be.sc_add(be.sc_mul(a.e, be.word(c * C3 % N_SECP)), be.sc_mul(m, be.word(self.F.C23)))

        return Val(be.check(self.once([a], body), hi), hi)

    def dot(self, pairs: Sequence[tuple[Val, Val]], neg: Container[int] = ()) -> Val:
        """Sum of products a_i b_i with one reduction; the terms whose index is in `neg` are subtracted
        (crt_neg)."""
        terms = []
        for i, (a, b) in enumerate(pairs):
            t = self.crt_mul(a, b)
            terms.append(self.crt_neg(t) if i in neg else t)
        return self.reduce(self.crt_sum(terms))

    def add(self, a: Val, b: Val) -> Val:
        hi = a.hi + b.hi
        ensure(hi < P_SECP, 'sum bound exceeds p_s')
        return Val(self.be.check(self.be.fe_add(a.e, b.e), hi), hi)

    def neg(self, a: Val) -> Val:
        """c - a for the smallest multiple c of p with c >= hi(a), so the result is non-negative; bound c."""
        c = self.F.mult_at_least(a.hi)
        ensure(c < P_SECP, 'negation constant exceeds p_s')
        be = self.be
        return Val(be.check(be.fe_add(be.fe_neg(a.e), be.word(c)), c), c)

    def sub(self, a: Val, b: Val) -> Val:
        return self.add(a, self.neg(b))

    def double(self, a: Val) -> Val:
        return self.add(a, a)

    def normalize(self, a: Val) -> Val:
        """Multiply by the constant 1 (the word R mod p, about 0.29 p).  The bound drops to about
        p + 0.055 hi(a): below 1.3 p for any 256-bit word."""
        return self.mul_const(a, 1)

    def to_mont(self, a: Val) -> Val:
        """Plain integer word -> Montgomery form: a (R^2 mod p) R^-1 = a R."""
        return self.mul_const(a, self.F.R_MOD_P)

    def from_mont(self, a: Val) -> Val:
        """Montgomery form -> plain word: a 1 R^-1; bound p + hi / p_s."""
        return self.mul_const(a, self.F.R_INV)

    # Environments: let/scope take nested structures of Val and Crt (a Crt is two words); the body gets
    # the same structure made of accessors.
    @staticmethod
    def _to_be(v: Any) -> Any:
        if isinstance(v, Val):
            return v.e
        if isinstance(v, Crt):
            return [v.sp, v.sn]
        return [Fp._to_be(x) for x in v]

    @staticmethod
    def _from_be(v: Any, acc: Any) -> Any:
        if isinstance(v, Val):
            return Val(acc, v.hi)
        if isinstance(v, Crt):
            return Crt(acc[0], acc[1], v.hi)
        return [Fp._from_be(x, a) for x, a in zip(v, acc)]

    @staticmethod
    def _lift(v: Any, lift: Callable[[Term], Term]) -> Any:
        if isinstance(v, Val):
            return lift(v.e)
        if isinstance(v, Crt):
            return [lift(v.sp), lift(v.sn)]
        return [Fp._lift(x, lift) for x in v]

    def let(self, vals: Any, body: Callable[[Any, Callable[[Any], Any]], Term]) -> Term:
        """Evaluate vals once and run body(new_vals, lift) with them in the environment (Sym.let).  A value
        used twice, or read by both jets of a CRT product, must be bound here: an expression used twice
        runs twice."""

        def wrapped(accs, lift):
            return body(Fp._from_be(vals, accs), lambda v: Fp._from_be(v, Fp._lift(v, lift)))

        return self.be.let(Fp._to_be(vals), wrapped)

    def scope(self, vals: Any, body: Callable[[Any], Term]) -> Term:
        """Like let, but the body sees only the new values."""

        def wrapped(accs):
            return body(Fp._from_be(vals, accs))

        return self.be.scope(Fp._to_be(vals), wrapped)

    def pack(self, vals: Any) -> Term:
        """A nested structure of Vals as one backend value (a balanced tree)."""
        return self.be.pack(Fp._to_be(vals))

    # checks
    def assert_eq_const(self, a: Val, x: int) -> Term:
        """Verify a = x (a field constant) for a value below 2p: the word is X or X + p."""
        be = self.be
        v = self.F.to_mont(x)
        ensure(a.hi < 2 * self.P, 'assert_eq_const needs a bound below 2p')
        return self.once(
            [a], lambda w: be.verify(be.or1(be.eq256(w[0].e, be.word(v)), be.eq256(w[0].e, be.word(v + self.P))))
        )

    def assert_eq_word(self, a: Val, v: int) -> Term:
        """Verify that the word is exactly v (tests compare with the numeric model this way)."""
        be = self.be
        return be.verify(be.eq256(a.e, be.word(v)))
