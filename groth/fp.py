"""BN254 base-field arithmetic from the secp256k1 jets.

An element x of F_p (p the 254-bit BN254 prime) is a word X = x R mod p in Montgomery form, with radix
R = p_s, the secp256k1 field prime.  X is not reduced: the generator carries a static bound `hi` with
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
from . import bn254
from .dsl import ensure, pairwise_sum
from .sym import E

P = bn254.P
P_SECP = 2**256 - 2**32 - 977
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
R = P_SECP # the Montgomery radix
R_MOD_P = R % P
R_INV = pow(R, -1, P)
C1 = (-pow(P, -1, P_SECP)) % P_SECP # -p^-1 mod p_s
C2 = P % N_SECP
C3 = pow(P_SECP, -1, N_SECP) # p_s^-1 mod n_s
C23 = C2 * C3 % N_SECP # p p_s^-1 mod n_s
CRT_MAX = (N_SECP - P) * P_SECP # exclusive bound on a CRT accumulator: keeps Q < n_s
WORD_MAX = 2**256 - 1


def to_mont(x):
    return x * R % P


def from_mont(X):
    return X * R_INV % P


def crt_of(v):
    """CRT residues of an integer."""
    return v % P_SECP, v % N_SECP


class Val:
    """A field element in Montgomery form: backend value `e` (an E or an int), inclusive bound `hi`."""
    __slots__ = ('e', 'hi')

    def __init__(self, e, hi):
        self.e, self.hi = e, hi

    def __repr__(self):
        return f'Val({self.e!r}, hi={self.hi / P:.3f} p)'


class Crt:
    """An integer in CRT form: residues mod p_s and mod n_s, inclusive bound `hi` on the integer."""
    __slots__ = ('sp', 'sn', 'hi')

    def __init__(self, sp, sn, hi):
        ensure(hi < CRT_MAX, 'CRT accumulator bound exceeded')
        self.sp, self.sn, self.hi = sp, sn, hi


def mult_of_p_at_least(hi):
    """The smallest multiple of p that is >= hi."""
    return ((hi + P - 1) // P) * P


class Fp:
    """Field operations over a backend (sym.Sym for expressions, sym.Num for numbers)."""

    def __init__(self, be):
        self.be = be

    # constants and inputs
    def const(self, x):
        """The field constant x (an integer mod p), in Montgomery form."""
        v = to_mont(x)
        return Val(self.be.word(v), v)

    def raw(self, e, hi=WORD_MAX):
        """A backend value with a known bound (default: any 256-bit word, e.g. a witness word)."""
        return Val(e, hi)

    # CRT products
    def crt_mul(self, a, b):
        """a b in CRT form.  Both jets read the operands, so computed operands are evaluated once first;
        reduce_dot avoids that by construction and is preferred."""
        be = self.be
        if a is b:
            return Crt(*self.once([a], lambda v: (be.fe_sqr(v[0].e), be.sc_sqr(v[0].e))), a.hi * a.hi)
        return Crt(*self.once([a, b], lambda v: (be.fe_mul(v[0].e, v[1].e), be.sc_mul(v[0].e, v[1].e))), a.hi * b.hi)

    def crt_add(self, x, y):
        be = self.be
        return Crt(be.fe_add(x.sp, y.sp), be.sc_add(x.sn, y.sn), x.hi + y.hi)

    def crt_sum(self, terms):
        return pairwise_sum(terms, self.crt_add)

    def crt_neg(self, x):
        """c - x for the smallest multiple c of p with c >= hi(x); bound c."""
        be = self.be
        c = mult_of_p_at_least(x.hi)
        cp, cn = crt_of(c)
        return Crt(be.fe_add(be.fe_neg(x.sp), be.word(cp)), be.sc_add(be.sc_neg(x.sn), be.word(cn)), c)

    def reduce_dot(self, pairs):
        """Sum of products a_i b_i with one reduction.  Every operand is read once (Sym.crt_dot); a pair
        (a, a) uses the squaring jets."""
        be = self.be
        hi = sum(a.hi * b.hi for a, b in pairs)
        ensure(hi < CRT_MAX, 'CRT accumulator bound exceeded')
        packed = be.crt_dot([(a.e, None if a is b else b.e) for a, b in pairs])
        out_hi = (hi + (P_SECP - 1) * P) // P_SECP
        ensure(out_hi < N_SECP, 'reduced bound exceeds n_s')

        def body(acc):
            sp, sn = acc
            m = be.fe_mul(sp, be.word(C1))
            return be.sc_mul(be.sc_add(sn, be.sc_mul(m, be.word(C2))), be.word(C3))
        q = be.with_env(packed, [E('', 256, 0), E('', 256, 0)], body)
        return Val(be.check(q, out_hi), out_hi)

    def lin_const(self, terms):
        """Sum of k_i x_i for field constants k_i (any sign, taken mod p).  The constants are folded into
        the reduction, as in mul_const: two jets per term plus two."""
        be = self.be
        hi = sum(x.hi * to_mont(k % P) for x, k in terms)
        ensure(hi < CRT_MAX, 'CRT accumulator bound exceeded')
        out_hi = (hi + (P_SECP - 1) * P) // P_SECP
        ensure(out_hi < N_SECP, 'reduced bound exceeds n_s')

        def body(xs):
            fe_terms, sc_terms = [], []
            for x, (_, k) in zip(xs, terms):
                c = to_mont(k % P)
                fe_terms.append(be.fe_mul(x.e, be.word(c * C1 % P_SECP)))
                sc_terms.append(be.sc_mul(x.e, be.word(c * C3 % N_SECP)))
            m = pairwise_sum(fe_terms, be.fe_add)
            s = pairwise_sum(sc_terms, be.sc_add)
            return be.sc_add(s, be.sc_mul(m, be.word(C23)))
        return Val(be.check(self.once([x for x, _ in terms], body), out_hi), out_hi)

    def reduce(self, x):
        """Montgomery reduction of a CRT value: Q = (x + m p) / p_s = x R^-1 (mod p)."""
        be = self.be
        m = be.fe_mul(x.sp, be.word(C1))
        q = be.sc_mul(be.sc_add(x.sn, be.sc_mul(m, be.word(C2))), be.word(C3))
        hi = (x.hi + (P_SECP - 1) * P) // P_SECP
        ensure(hi < N_SECP, 'reduced bound exceeds n_s')
        return Val(be.check(q, hi), hi)

    def once(self, vals, fn):
        """fn(vals) with every computed value evaluated once into the environment (see Sym.once)."""
        return self.be.once([v.e for v in vals], lambda es: fn([Val(e, v.hi) for e, v in zip(es, vals)]))

    # field operations
    def mul(self, a, b):
        return self.reduce(self.crt_mul(a, b))

    def sqr(self, a):
        return self.reduce(self.crt_mul(a, a))

    def mul_const(self, a, x):
        """a times the field constant x.  The constant is folded into the reduction: 4 jets instead of 6."""
        be = self.be
        c = to_mont(x)
        hi = (a.hi * c + (P_SECP - 1) * P) // P_SECP
        ensure(hi < N_SECP, 'reduced bound exceeds n_s')

        def body(v):
            a = v[0]
            m = be.fe_mul(a.e, be.word(c * C1 % P_SECP)) # (a c mod p_s) C1
            return be.sc_add(be.sc_mul(a.e, be.word(c * C3 % N_SECP)), be.sc_mul(m, be.word(C23)))
        return Val(be.check(self.once([a], body), hi), hi)

    def dot(self, pairs, neg=()):
        """Sum of products a_i b_i with one reduction; the terms whose index is in `neg` are subtracted
        (crt_neg)."""
        terms = []
        for i, (a, b) in enumerate(pairs):
            t = self.crt_mul(a, b)
            terms.append(self.crt_neg(t) if i in neg else t)
        return self.reduce(self.crt_sum(terms))

    def add(self, a, b):
        hi = a.hi + b.hi
        ensure(hi < P_SECP, 'sum bound exceeds p_s')
        return Val(self.be.check(self.be.fe_add(a.e, b.e), hi), hi)

    def neg(self, a):
        """c - a for the smallest multiple c of p with c >= hi(a), so the result is non-negative; bound c."""
        c = mult_of_p_at_least(a.hi)
        ensure(c < P_SECP, 'negation constant exceeds p_s')
        be = self.be
        return Val(be.check(be.fe_add(be.fe_neg(a.e), be.word(c)), c), c)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def double(self, a):
        return self.add(a, a)

    def normalize(self, a):
        """Multiply by the constant 1 (the word R mod p, about 0.29 p).  The bound drops to about
        p + 0.055 hi(a): below 1.3 p for any 256-bit word."""
        return self.mul_const(a, 1)

    def to_mont(self, a):
        """Plain integer word -> Montgomery form: a (R^2 mod p) R^-1 = a R."""
        return self.mul_const(a, R_MOD_P)

    def from_mont(self, a):
        """Montgomery form -> plain word: a 1 R^-1; bound p + hi / p_s."""
        return self.mul_const(a, R_INV)

    # Environments: let/scope take nested structures of Val and Crt (a Crt is two words); the body gets
    # the same structure made of accessors.
    @staticmethod
    def _to_be(v):
        if isinstance(v, Val):
            return v.e
        if isinstance(v, Crt):
            return [v.sp, v.sn]
        return [Fp._to_be(x) for x in v]

    @staticmethod
    def _from_be(v, acc):
        if isinstance(v, Val):
            return Val(acc, v.hi)
        if isinstance(v, Crt):
            return Crt(acc[0], acc[1], v.hi)
        return [Fp._from_be(x, a) for x, a in zip(v, acc)]

    @staticmethod
    def _lift(v, lift):
        if isinstance(v, Val):
            return lift(v.e)
        if isinstance(v, Crt):
            return [lift(v.sp), lift(v.sn)]
        return [Fp._lift(x, lift) for x in v]

    def let(self, vals, body):
        """Evaluate vals once and run body(new_vals, lift) with them in the environment (Sym.let).  A value
        used twice, or read by both jets of a CRT product, must be bound here: an expression used twice
        runs twice."""
        def wrapped(accs, lift):
            return body(Fp._from_be(vals, accs), lambda v: Fp._from_be(v, Fp._lift(v, lift)))
        return self.be.let(Fp._to_be(vals), wrapped)

    def scope(self, vals, body):
        """Like let, but the body sees only the new values."""
        def wrapped(accs):
            return body(Fp._from_be(vals, accs))
        return self.be.scope(Fp._to_be(vals), wrapped)

    def pack(self, vals):
        """A nested structure of Vals as one backend value (a balanced tree)."""
        return self.be.pack(Fp._to_be(vals))

    # checks
    def assert_eq_const(self, a, x):
        """Verify a = x (a field constant) for a value below 2p: the word is X or X + p."""
        be = self.be
        v = to_mont(x)
        ensure(a.hi < 2 * P, 'assert_eq_const needs a bound below 2p')
        return self.once([a], lambda w: be.verify(be.or1(be.eq256(w[0].e, be.word(v)), be.eq256(w[0].e, be.word(v + P)))))

    def assert_eq_word(self, a, v):
        """Verify that the word is exactly v (tests compare with the numeric model this way)."""
        be = self.be
        return be.verify(be.eq256(a.e, be.word(v)))
