#!/usr/bin/env python3
"""On-curve checks, table lookups and the range check of an input (groth/curve.py) against bn254.py.
Off-curve points, a wrong table entry and an input >= r must be rejected.

    python3 tests/test_curve.py
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth import bn254 as B
from groth import fp as F
from groth.curve import Curve
from groth.dsl import Tbalanced, balanced_paths, wbalanced, wv
from groth.sym import Num, Sym, flat, words

P = F.P


def run(name, words, build, expect_ok=True, verbose=True, hi=None):
    """words: flat list of witness words; build(fp, cv, ins, check) -> E; `check(label, val)` records a
    value in the numeric pass and verifies it in the symbolic pass; hi: bound declared for the inputs"""
    hi = [P - 1] * len(words) if hi is None else ([hi] * len(words) if isinstance(hi, int) else hi)
    expected = []
    be = Num()
    fp = F.Fp(be)

    def check_num(label, v):
        expected.append((label, be.check(v.e, v.hi), v.hi))
        return F.Val(0, 0)

    try:
        build(fp, Curve(fp), [F.Val(w, h) for w, h in zip(words, hi)], check_num)
    except AssertionError:
        if expect_ok:
            raise
    exp = {label: w for label, w, h in expected}
    be = Sym(256 * len(words))
    fp = F.Fp(be)
    ins = [F.Val(be.proj(p, 256), h) for p, h in zip(balanced_paths(len(words)), hi)]
    body = build(
        fp,
        Curve(fp),
        ins,
        lambda label, v: F.Val(fp.assert_eq_word(v, exp[label]), 0) if label in exp else F.Val(be.unit(), 0),
    )
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


def run_select(name, rng, lo, w, expect_ok=True, verbose=True):
    """A table of 2^w entries of 6 random words, selected by bits lo .. lo+w-1 of a random witness word;
    the program checks the selected words against the entry the digit picks (or, to be rejected, the next
    entry).  w = 8 at an aligned position takes the byte as one projection and splits it with BITS8."""
    table = [
        [[rng.randrange(1 << 256) for _ in range(4)], [rng.randrange(1 << 256) for _ in range(2)]]
        for _ in range(1 << w)
    ]
    word = rng.randrange(1 << 254)
    d = (word >> lo) & ((1 << w) - 1)
    assert Curve(F.Fp(Num())).select_const(F.Val(word, F.WORD_MAX), lo, w, table) == table[d]
    want = table[d if expect_ok else (d + 1) % (1 << w)]
    be = Sym(256)
    fp = F.Fp(be)
    cv = Curve(fp)
    sel = cv.select_const(F.Val(be.proj('H', 256), F.WORD_MAX), lo, w, table)
    found = be.with_env(
        sel,
        [words(4), words(2)],
        lambda acc: be.checks([fp.assert_eq_word(F.Val(e, 0), v) for e, v in zip(flat(acc), flat(want))]),
    )
    # the whole word is read too, so that its type is the witness's (an unread part would be inferred as 1)
    body = be.checks([found, fp.assert_eq_word(F.Val(be.proj('H', 256), 0), word)])
    be.em.define('w_in', 'witness', '_ -> 2^256')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256) + body.c
    r = harness.run(name, be.em.text(), {'w_in': wv(256, word)})
    if expect_ok:
        harness.expect_ok(r, name)
        assert r['cost'] == estimate, (r['cost'], estimate)
        if verbose:
            print(f'{name:22} cost {r["cost"]:>10}  estimate {estimate:>10}  ok  prog {r["program_bytes"]} B')
    else:
        assert not r.get('ok') and r.get('stage') in ('exec', 'finalize'), (name, r)
        if verbose:
            print(f'{name:22} rejected as expected')


def build_lt_r(fp, cv, ins, check):
    return cv.lt_const_check(F.Val(ins[0].e, 0), B.R).e


def main():
    rng = random.Random(int(os.environ.get('SEED', '3')))
    T, Pt = rand_g2(rng), rand_g1(rng)
    # on-curve checks
    run('g1_on_curve', [F.to_mont(Pt[0]), F.to_mont(Pt[1])], build_g1_on_curve)
    run('g1_off_curve', [F.to_mont(Pt[0]), F.to_mont(Pt[1] + 1)], build_g1_on_curve, expect_ok=False)
    run('g2_on_curve', g2_words(T), build_g2_on_curve)
    bad = (T[0], T[1] + B.Fp2(0, 1))
    run('g2_off_curve', g2_words(bad), build_g2_on_curve, expect_ok=False)
    # tables: a byte (BITS8), the 6 top bits of an input; a wrong entry must be rejected
    run_select('select_byte', rng, 40, 8)
    run_select('select_top6', rng, 248, 6)
    run_select('select_wrong', rng, 40, 8, expect_ok=False)
    # an input below r, and one above
    run('input_lt_r', [B.R - 1], build_lt_r, hi=0)
    run('input_ge_r', [B.R + 5], build_lt_r, expect_ok=False, hi=0)
    print('all ok')


if __name__ == '__main__':
    main()
