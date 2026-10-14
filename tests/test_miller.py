#!/usr/bin/env python3
"""The plain three-pair Miller loop (groth/miller.py) against bn254.py.  A wrong hint and an off-curve
point must be rejected.

    python3 tests/test_miller.py            # all 88 steps
    STEPS=3 python3 tests/test_miller.py    # the first steps only
"""
import os, random, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, miller as M
from groth.tower import ref_to_list
from groth.sym import Sym, Num, E
from groth.dsl import wv, wpair, wbalanced, Tbalanced, balanced_paths
import harness

P = F.P


def rand_g1(rng):
    return B.g1_mul(B.G1_GEN, rng.randrange(1, B.R))


def rand_g2(rng):
    return B.g2_mul(B.G2_GEN, rng.randrange(1, B.R))


def affine_loop(pairs, n_steps):
    """the reference product of the first n_steps steps (bn254.multi_miller_loop_affine restricted to a
    prefix of the loop), from the per-pair slopes of miller.slopes"""
    f = B.Fp12.one()
    per_pair = [M.slopes(Q) for _, Q in pairs]
    for k in range(n_steps):
        if M.STEPS[k] == 'D':
            f = f.square()
        for (Pt, Q), sl in zip(pairs, per_pair):
            lam, coeffs = sl[k]
            f = f.mul_by_034(*B.affine_line(coeffs, Pt))
    return f


def point_words(A, Bq, C, L):
    """the 10 witness words of the points (Montgomery form)"""
    return [F.to_mont(v) for v in (A[0], A[1], Bq[0].c0, Bq[0].c1, Bq[1].c0, Bq[1].c1, C[0], C[1], L[0], L[1])]


def main():
    rng = random.Random(int(os.environ.get('SEED', '4')))
    n_steps = int(os.environ.get('STEPS', M.N_STEPS))
    key = random.Random(11) # the fixed points of the verifying key
    gamma, delta = rand_g2(key), rand_g2(key)
    A, C, L = rand_g1(rng), rand_g1(rng), rand_g1(rng)
    Bq = rand_g2(rng)
    pairs = [(A, Bq), (L, gamma), (C, delta)]
    # the reference and the hints
    hints = []
    f_full = B.multi_miller_loop_affine(pairs, hints)
    assert [lam for lam, _ in M.slopes(Bq)] == hints[0]
    f_ref = affine_loop(pairs, n_steps)
    if n_steps == M.N_STEPS:
        assert f_ref == f_full
        assert B.final_exponentiation(f_ref) == B.final_exponentiation(B.multi_miller_loop(pairs))
    b = M.bounds()
    hint_words = M.hint_words(Bq)
    pw = point_words(A, Bq, C, L)
    # numeric pass
    be = Num(); fp = F.Fp(be)
    m = M.Miller(fp, gamma, delta, b, n_steps)
    vals = [F.Val(w, F.WORD_MAX) for w in pw]
    state0 = m.initial_state((vals[0], vals[1]), tuple(vals[2:6]), (vals[6], vals[7]), (vals[8], vals[9]))
    state = m.loop(state0, hint_words)
    f_words = state[0]
    assert [F.from_mont(w) for w in f_words] == ref_to_list(f_ref), 'numeric model disagrees with the reference'
    print(f'numeric model ok ({n_steps} steps)')
    # symbolic pass: witness = (points, hints tree)
    nh = n_steps
    be = Sym(256 * 10 + 512 * nh); fp = F.Fp(be)
    m = M.Miller(fp, gamma, delta, b, n_steps)
    ins = [F.Val(be.proj('O' + p, 256), F.WORD_MAX) for p in balanced_paths(10)]
    hints_root = be.proj('IH', 512 * nh)
    state0 = m.initial_state((ins[0], ins[1]), tuple(ins[2:6]), (ins[6], ins[7]), (ins[8], ins[9]))
    setup_cost = state0.c
    final = m.loop(state0, hints_root)
    shape = [[E('', 256, 0) for _ in range(12)], [E('', 256, 0) for _ in range(4)], [E('', 256, 0) for _ in range(12)]]
    body = be.with_env(final, shape, lambda accs: be.checks([fp.assert_eq_word(F.Val(a, 0), w) for a, w in zip(accs[0], f_words)]))
    ty = f'({Tbalanced(["2^256"] * 10)} * {Tbalanced(["(2^256 * 2^256)"] * nh)})'
    be.em.define('w_in', 'witness', f'_ -> {ty}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * 10 + 512 * nh) + body.c
    text = be.em.text()

    def witness(points, hw):
        return {'w_in': {'p': [wbalanced([wv(256, w) for w in points]),
                               wbalanced([wpair(wv(256, lx), wv(256, ly)) for lx, ly in hw[:nh]])]}}
    bad_hint = [list(h) for h in hint_words]
    bad_hint[nh - 1][0] = (bad_hint[nh - 1][0] + 1) % (1 << 256)
    off_curve = list(pw)
    off_curve[1] = (off_curve[1] + 1) % (1 << 256) # yA + 1: A off the curve
    t0 = time.time()
    results = harness.run('miller', text, witness(pw, hint_words), multi=[witness(pw, bad_hint), witness(off_curve, hint_words)])
    seconds = time.time() - t0
    r = harness.expect_ok(results[0], 'miller')
    assert r['cost'] == estimate, (r['cost'], estimate)
    for bad, label in zip(results[1:], ('wrong hint', 'off-curve A')):
        assert not bad.get('ok') and bad.get('stage') in ('exec', 'finalize'), (label, bad)
        print(f'{label:12} rejected as expected')
    print(f'miller ({n_steps} steps) cost {r["cost"]:,}  estimate {estimate:,}  ok  prog {r["program_bytes"]} B  '
          f'text {len(text) // 1024} KB  ({seconds:.0f}s for three runs)')
    if os.environ.get('STATS'):
        print(be.report())
    # the cost table
    loop_cost = final.c - state0.c - hints_root.c
    rows = [(name, m.costs[name]) for name in ('SQRN', 'LM1', 'LM2', 'LMN', 'BSTEP_DBL', 'BSTEP_ADD', 'ITER_D0', 'ITER_D', 'ITER_F')]
    rows += [('setup (normalisation, on-curve checks)', setup_cost), (f'loop ({n_steps} steps)', loop_cost),
             ('whole program', r['cost'])]
    for name, c in rows:
        print(f'{name:42} {c:>12,}')


if __name__ == '__main__':
    main()
