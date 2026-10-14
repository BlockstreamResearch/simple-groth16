#!/usr/bin/env python3
"""The G2 membership check (Miller.g2_check): after the loop, T must equal -psi^3(B).  The program runs
the plain Miller loop and the check, and compares f with the reference, so that a point outside G2 can
only fail on the check.  B in G2 must pass; B plus a point of order 10069, and a random point of the
twist, must be rejected.

    python3 tests/test_g2_check.py
"""
import math, os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, miller as M
from groth.dsl import CheckFailed, wv, wpair, wbalanced, Tbalanced, balanced_paths
from groth.sym import Sym, Num, words
import harness

N = M.N_STEPS


def point_words(A, Bq, C, L):
    return [F.to_mont(v) for v in (A[0], A[1], Bq[0].c0, Bq[0].c1, Bq[1].c0, Bq[1].c1, C[0], C[1], L[0], L[1])]


def numeric(gamma, delta, pw, hw, b):
    """the loop and the check on the numeric backend: (f words, whether the check passed)"""
    fp = F.Fp(Num())
    m = M.Miller(fp, gamma, delta, b)
    v = [F.Val(w, F.WORD_MAX) for w in pw]
    f, T, K = m.loop(m.initial_state((v[0], v[1]), tuple(v[2:6]), (v[6], v[7]), (v[8], v[9])), hw)
    try:
        m.g2_check(T, K)
        return f, True
    except CheckFailed:
        return f, False


def program(gamma, delta, f_words, b):
    """the loop, the check, and f compared with f_words"""
    be = Sym(256 * 10 + 512 * N); fp = F.Fp(be)
    m = M.Miller(fp, gamma, delta, b)
    ins = [F.Val(be.proj('O' + p, 256), F.WORD_MAX) for p in balanced_paths(10)]
    state0 = m.initial_state((ins[0], ins[1]), tuple(ins[2:6]), (ins[6], ins[7]), (ins[8], ins[9]))
    final = m.loop(state0, be.proj('IH', 512 * N))

    def body(accs):
        f, T, K = accs
        return be.checks([m.g2_check(T, K)] + [fp.assert_eq_word(F.Val(a, 0), w) for a, w in zip(f, f_words)])
    main = be.with_env(final, [words(12), words(4), words(12)], body)
    be.em.define('w_in', 'witness', f'_ -> ({Tbalanced(["2^256"] * 10)} * {Tbalanced(["(2^256 * 2^256)"] * N)})')
    be.em.define('main', f'comp w_in ({main.t})')
    return be.em.text(), 2 * (100 + 256 * 10 + 512 * N) + main.c, m


def witness(pw, hw):
    return {'w_in': {'p': [wbalanced([wv(256, w) for w in pw]), wbalanced([wpair(wv(256, x), wv(256, y)) for x, y in hw])]}}


COFACTOR_PRIMES = [10069, 5864401, 1875725156269, 197620364512881247228717050342013327560683201906968909]


def check_kernel(rng):
    """phi = [6x+2] + psi - psi^2 + psi^3 kills G2 and no other point: E'(Fp2) is cyclic of squarefree
    order r h, so it suffices that phi is nonzero on a point of each prime order dividing h."""
    psi, mul = B.g2_frobenius, B.g2_mul_unreduced

    def phi(Q):
        Q1 = psi(Q); Q2 = psi(Q1); Q3 = psi(Q2)
        return B.g2_add(B.g2_add(B.g2_add(mul(Q, 6 * B.X + 2), Q1), B.g2_neg(Q2)), Q3)
    h = 2 * B.P - B.R
    assert h == math.prod(COFACTOR_PRIMES)
    assert phi(B.G2_GEN) is None
    for l in COFACTOR_PRIMES:
        T = mul(B.g2_random_point(rng), B.R * h // l)
        assert T is not None and mul(T, l) is None and phi(T) is not None, l
    print('phi has kernel G2')


def main():
    rng = random.Random(6)
    check_kernel(rng)
    key = random.Random(11)
    gamma, delta = B.g2_mul(B.G2_GEN, key.randrange(1, B.R)), B.g2_mul(B.G2_GEN, key.randrange(1, B.R))
    A, C, L = (B.g1_mul(B.G1_GEN, rng.randrange(1, B.R)) for _ in range(3))
    h = 2 * B.P - B.R
    good = B.g2_mul(B.G2_GEN, rng.randrange(1, B.R))
    small = B.g2_mul_unreduced(B.g2_random_point(rng), B.R * h // 10069) # order 10069
    cases = [('B in G2', good, True), ('B + order-10069 point', B.g2_add(good, small), False),
             ('random twist point', B.g2_random_point(rng), False)]
    b = M.bounds()
    for label, Bq, in_g2 in cases:
        assert B.g2_on_curve(*Bq) and B.g2_in_subgroup(Bq) == in_g2
        pw, hw = point_words(A, Bq, C, L), M.hint_words(Bq)
        f_words, passed = numeric(gamma, delta, pw, hw, b)
        assert passed == in_g2, (label, 'numeric model')
        text, estimate, m = program(gamma, delta, f_words, b)
        r = harness.run('g2_check', text, witness(pw, hw))
        if in_g2:
            harness.expect_ok(r, label)
            assert r['cost'] == estimate, (r['cost'], estimate)
            fp = F.Fp(Sym(0))
            mc = M.Miller(fp, gamma, delta, b)
            check = mc.g2_check([fp.be.proj(p, 256) for p in balanced_paths(4, 'O')],
                                [fp.be.proj(p, 256) for p in balanced_paths(12, 'I')])
            print(f'{label:24} accepted  (program cost {r["cost"]:,} mWU, the check alone about {check.c:,})')
        else:
            assert not r.get('ok') and r.get('stage') in ('exec', 'finalize'), (label, r)
            print(f'{label:24} rejected as expected')
    print('all ok')


if __name__ == '__main__':
    main()
