"""The pairing check e(A, B) e(L, gamma) e(C, delta) const = 1, without a final exponentiation.

The Miller value f of a pairing product equal to 1 satisfies f^h = 1, h = (p^12 - 1) / r.  Instead of
exponentiating, the prover supplies a residue witness (Novakovic and Eagen, "On Proving Pairings"):
c and a 27th root of unity w = W27^s with f w = c^lambda, lambda = 6x + 2 + p - p^2 + p^3.  Since r
divides lambda and 27 divides h, that equation implies f^h = 1.

The loop (miller.py, residue mode) already multiplies f by c^-(6x+2).  This module multiplies in
pi(c^-1) pi^2(c) pi^3(c^-1) and compares the result with the constant (W27^s const)^-1, selected from a
table of three by the two witness bits of s.  For Groth16, `const` is the Miller value of
(alpha, beta), so the fourth pair costs nothing.
"""
from . import bn254
from .dsl import ensure
from .fp import Val, P, to_mont
from .sym import E, words, is_sym
from .tower import ref_to_list
from .miller import Miller, K_HI


class PairingCheck:
    """Generator of the check over a backend.  gamma, delta: the fixed G2 points; const: a bn254.Fp12
    factor of the product (the Miller value of (alpha, beta)); b: miller.bounds()."""

    def __init__(self, fp, gamma, delta, const=None, b=None):
        self.fp, self.be = fp, fp.be
        self.const = const if const is not None else bn254.Fp12.one()
        self.m = Miller(fp, gamma, delta, b, residue=True)
        self.tw = self.m.tw
        self.table = [ref_to_list((bn254.W27 ** s * self.const).inv()) for s in range(3)]

    # prover side
    def witness(self, pairs):
        """(c words, c^-1 words, s) for the pairs (bn254 points); None if their product times const is
        not 1."""
        f = bn254.multi_miller_loop_affine(pairs)
        w = bn254.residue_witness(f * self.const)
        if w is None:
            return None
        c, s = w
        return [to_mont(v) for v in ref_to_list(c)], [to_mont(v) for v in ref_to_list(c.inv())], s

    # the verifier
    def frobenius(self, elem, n):
        """pi^n of a K element (12 words), normalised when it comes out of lin_const."""
        fp = self.fp
        out = self.tw.frobenius(elem, n, tight_neg=True)
        if n % 2:
            out = [fp.normalize(v) for v in out]
        for v in out:
            ensure(v.hi <= self.m.b['dm_g'], 'Frobenius bound')
        return out

    def final(self, final_state, sel):
        """Check that B is in G2 (Miller.g2_check), and F = f pi(c^-1) pi^2(c) pi^3(c^-1) against the
        table entry selected by sel, the two bits of s.  Sym: an E over (final_state, sel); Num: runs the
        checks."""
        be, m = self.be, self.m
        shape = [[words(12), words(4), m.k_shape], [E('', 1, 0), E('', 1, 0)]]

        def body(accs):
            (f, T, K), (s1, s0) = accs
            c = [Val(x, K_HI) for x in K[1]]
            ci = [Val(x, K_HI) for x in K[2]]
            g1 = [v.e for v in self.frobenius(ci, 1)]
            g2 = [v.e for v in self.frobenius(c, 2)]
            g3 = [v.e for v in self.frobenius(ci, 3)]
            F = be.call(m.DMULN, [g3, be.call(m.DMULN, [g2, be.call(m.DMULN, [g1, f])])])
            return be.checks([m.g2_check(T, K[0]), be.scope([F, [s1, s0]], self.compare)])
        return be.with_env(be.pair(final_state, sel), shape, body) if is_sym(be) else body([final_state, sel])

    def compare(self, accs):
        """F (12 words below 2p) equals entry s = 2 s1 + s0 of the table, s < 3: every word is the entry's
        Montgomery word or that word plus p."""
        be = self.be
        F, (s1, s0) = accs
        rows = [[to_mont(v) for v in row] for row in self.table]
        rows = [row + [v + P for v in row] for row in rows] # the two candidate words per coefficient
        if not is_sym(be):
            s = 2 * s1 + s0
            ensure(s < 3, 'selector')
            for i, a in enumerate(be.split(F, words(12))):
                ensure(a in (rows[s][i], rows[s][12 + i]), 'pairing check failed')
            return 0
        # select the entry with a case tree on the bits; s = 3 is rejected separately
        env = be.pair(s1, be.pair(s0, be.unit()))

        def leaf(s):
            return be.comp(be.unit(), be.pack([be.const(256, v) for v in rows[min(s, 2)]]))
        selected = be.comp(env, be.case(be.drop(be.case(leaf(0), leaf(1))), be.drop(be.case(leaf(2), leaf(3)))))
        not3 = be.verify(be.not1(be.and1(s1, s0)))

        def inner(v):
            Fv, W = be.split(v[0], words(12)), be.split(v[1], words(24))
            return be.checks([be.verify(be.or1(be.eq256(a, W[i]), be.eq256(a, W[12 + i]))) for i, a in enumerate(Fv)])
        return be.seq(not3, be.scope([F, selected], inner))

    def program(self, A, B, C, L, c, cinv, sel, hints):
        """The whole check: setup (on-curve checks, c c^-1 = 1), the loop, the final comparison.  Sym: a
        unit-typed E over the witness environment; Num: runs the checks."""
        m = self.m
        state0 = m.initial_state(A, B, C, L, c, cinv)
        state = m.loop(state0, hints)
        out = self.final(state, sel)
        if is_sym(self.be): # cost attribution of the three parts
            self.parts = {'setup': state0.c, 'loop': state.c - state0.c - hints.c, 'final': out.c - state.c - sel.c}
        return out
