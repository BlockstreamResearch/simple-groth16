#!/usr/bin/env python3
"""On-curve checks and the MSM with hinted slopes (groth/curve.py) against bn254.py.  Off-curve points,
a wrong hint and a scalar >= r must be rejected.

    python3 tests/test_curve.py
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B
from groth.curve import Curve
from groth.sym import Sym, Num, E
from groth.dsl import wv, wbalanced, Tbalanced, balanced_paths
import harness

P = F.P


def run(name, words, build, expect_ok=True, verbose=True, hi=None):
    """words: flat list of witness words; build(fp, cv, ins, check) -> E; `check(label, val)` records a
    value in the numeric pass and verifies it in the symbolic pass; hi: bound declared for the inputs"""
    hi = [P - 1] * len(words) if hi is None else ([hi] * len(words) if isinstance(hi, int) else hi)
    expected = []
    be = Num(); fp = F.Fp(be)

    def check_num(label, v):
        expected.append((label, be.check(v.e, v.hi), v.hi))
        return F.Val(0, 0)
    try:
        build(fp, Curve(fp), [F.Val(w, h) for w, h in zip(words, hi)], check_num)
    except AssertionError:
        if expect_ok:
            raise
    exp = {label: w for label, w, h in expected}
    be = Sym(256 * len(words)); fp = F.Fp(be)
    ins = [F.Val(be.proj(p, 256), h) for p, h in zip(balanced_paths(len(words)), hi)]
    body = build(fp, Curve(fp), ins, lambda label, v: F.Val(fp.assert_eq_word(v, exp[label]), 0) if label in exp else F.Val(be.unit(), 0))
    be.em.define('w_in', 'witness', f'_ -> {Tbalanced(["2^256"] * len(words))}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * len(words)) + body.c
    r = harness.run(name, be.em.text(), {'w_in': wbalanced([wv(256, w) for w in words])})
    if expect_ok:
        harness.expect_ok(r, name)
        assert r['cost'] == estimate, (r['cost'], estimate)
        if verbose:
            print(f'{name:22} cost {r["cost"]:>10}  estimate {estimate:>10}  ok  prog {r["program_bytes"]} B')
    else:
        assert not r.get('ok') and r.get('stage') in ('exec', 'finalize'), (name, r)
        if verbose:
            print(f'{name:22} rejected as expected ({r.get("error", "")[:60]})')
    return r, exp


def rand_g2(rng):
    return B.g2_mul(B.G2_GEN, rng.randrange(1, B.R))


def rand_g1(rng):
    return B.g1_mul(B.G1_GEN, rng.randrange(1, B.R))


def g2_words(T):
    return [F.to_mont(T[0].c0), F.to_mont(T[0].c1), F.to_mont(T[1].c0), F.to_mont(T[1].c1)]


def build_g1_on_curve(fp, cv, ins, check):
    return cv.g1_on_curve_check(ins[0], ins[1])


def build_g2_on_curve(fp, cv, ins, check):
    return cv.g2_on_curve_check((ins[0], ins[1]), (ins[2], ins[3]))


def run_msm(name, rng, n_scalars, w, nbits=254, verbose=True, tamper=None):
    """L = IC_0 + sum a_i IC_i with random fixed bases and random scalars: numeric model, then the
    symbolic program with the witness (scalars, hints tree).  tamper: a function on (scalars, hints)
    producing a witness that must be rejected."""
    bases = [rand_g1(rng) for _ in range(n_scalars)]
    ic0 = rand_g1(rng)
    scalars = [rng.randrange(1 << nbits) % B.R for _ in range(n_scalars)]
    tables, offset = Curve.msm_tables(bases, w, nbits)
    start = B.g1_add(ic0, offset)
    hints, L = Curve.msm_hints(start, scalars, tables, w, nbits)
    want = ic0
    for a, base in zip(scalars, bases):
        want = B.g1_add(want, B.g1_mul(base, a))
    assert L == want
    nwin = (nbits + w - 1) // w
    # numeric pass
    be = Num(); fp = F.Fp(be); cv = Curve(fp)
    (x, y), checks = cv.msm([F.Val(a, B.R - 1) for a in scalars],
                            [[F.Val(F.to_mont(h), 0) for h in hi] for hi in hints], tables, start, w, nbits)
    assert (F.from_mont(x.e), F.from_mont(y.e)) == L
    exp_x, exp_y = x.e, y.e
    # symbolic pass: witness = (scalars tree, hints tree)
    nh = n_scalars * nwin
    be = Sym(256 * (n_scalars + nh)); fp = F.Fp(be); cv = Curve(fp)
    sc_vals = [F.Val(be.proj('O' + p, 256), B.R - 1) for p in balanced_paths(n_scalars)]
    hints_root = be.proj('IH', 256 * nh)
    state = cv.msm_sym(sc_vals, hints_root, tables, start, w, nbits)
    shape = [E('', 256, 0), E('', 256, 0), [E('', 256, 0)] * n_scalars]
    body = be.with_env(state, shape, lambda accs: be.checks([
        fp.assert_eq_word(F.Val(accs[0], 0), exp_x), fp.assert_eq_word(F.Val(accs[1], 0), exp_y)]
        + [cv.lt_const_check(F.Val(a, 0), B.R).e for a in accs[2]])) # scalars < r (reads every limb)
    ty = f'({Tbalanced(["2^256"] * n_scalars)} * {Tbalanced(["2^256"] * nh)})'
    be.em.define('w_in', 'witness', f'_ -> {ty}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * (n_scalars + nh)) + body.c
    hint_words = [F.to_mont(h) for hi in hints for h in hi]
    if tamper:
        scalars, hint_words = tamper(list(scalars), list(hint_words))
    wit = {'w_in': {'p': [wbalanced([wv(256, a) for a in scalars]), wbalanced([wv(256, h) for h in hint_words])]}}
    r = harness.run(name, be.em.text(), wit)
    if tamper:
        assert not r.get('ok') and r.get('stage') in ('exec', 'finalize'), (name, r)
        if verbose:
            print(f'{name:22} rejected as expected')
        return r
    harness.expect_ok(r, name)
    assert r['cost'] == estimate, (r['cost'], estimate)
    if verbose:
        print(f'{name:22} cost {r["cost"]:>10}  estimate {estimate:>10}  ok  prog {r["program_bytes"]} B  '
              f'({nwin} windows of {w} bits per scalar; {r["seconds"]:.1f}s)')
    return r


def main():
    rng = random.Random(int(os.environ.get('SEED', '3')))
    T, Pt = rand_g2(rng), rand_g1(rng)
    # on-curve checks
    run('g1_on_curve', [F.to_mont(Pt[0]), F.to_mont(Pt[1])], build_g1_on_curve)
    run('g1_off_curve', [F.to_mont(Pt[0]), F.to_mont(Pt[1] + 1)], build_g1_on_curve, expect_ok=False)
    run('g2_on_curve', g2_words(T), build_g2_on_curve)
    bad = (T[0], T[1] + B.Fp2(0, 1))
    run('g2_off_curve', g2_words(bad), build_g2_on_curve, expect_ok=False)
    # MSM: one full-size scalar (51 windows of 5 bits), two short scalars (the multi-scalar state), and
    # rejections: a wrong hint, a scalar >= r
    run_msm('msm_1x5', rng, 1, 5)
    run_msm('msm_2x5_short', rng, 2, 5, nbits=30)

    def bad_hint(scalars, hints):
        hints[3] = (hints[3] + 1) % (1 << 256)
        return scalars, hints
    run_msm('msm_badhint', rng, 1, 5, nbits=30, tamper=bad_hint)

    def big_scalar(scalars, hints):
        return [B.R + 5], hints
    run_msm('msm_scalar_ge_r', rng, 1, 5, nbits=30, tamper=big_scalar)
    print('all ok')


if __name__ == '__main__':
    main()
