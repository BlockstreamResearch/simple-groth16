#!/usr/bin/env python3
"""The G1 multi-scalar multiplication of the fflonk verifier (groth/msm.py) against bn254.py.

    python3 tests/test_msm.py [quick]

The group law on numbers and in hand; a wrong slope or inverse is rejected.  The variable-base MSM with
8-bit columns (no GLV), then with the full 128-bit GLV columns of 4 points, and the fixed-base product
of a canonical scalar, each checked against bn254.py at the estimated cost.  A wrong step hint and a
column word too large are rejected.
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth import bn254 as B
from groth import fp as F
from groth import msm as M
from groth.curve import Curve
from groth.dsl import Tbalanced, wbalanced, wv
from groth.sym import Num, Sym, words

P, R = B.P, B.R
QUICK = 'quick' in sys.argv[1:]


def rand_point(rng):
    return B.g1_mul(B.G1_GEN, rng.randrange(1, R))


def wspec(ws):
    return wbalanced([wv(256, x) for x in ws])


def check_point(fp, t, expect):
    """t (an E of a pair of words below KB) is the point expect."""
    be, cv = fp.be, Curve(fp)

    def body(a):
        x, y = a
        return be.checks(
            [cv.eq_check(F.Val(x, M.KB), fp.const(expect[0])).e, cv.eq_check(F.Val(y, M.KB), fp.const(expect[1])).e]
        )

    return be.with_env(t, words(2), body)


def run(name, shape_words, values, build, nodes, ok=True):
    """w_in: shape_words words; build(fp, accessors) -> unit E; nodes: the witness nodes' values."""
    be = Sym(256 * shape_words)
    fp = F.Fp(be)
    body = build(fp, be._unpack('', words(shape_words)))
    be.em.define('w_in', 'witness', f'_ -> {Tbalanced(["2^256"] * shape_words)}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * shape_words) + body.c
    r = harness.run(name, be.em.text(), {'w_in': wspec(values), **nodes})
    if not ok:
        harness.expect_rejected(r, name)
        print(f'{name:26} rejected as expected ({r.get("error", "")[:50]})')
        return r
    harness.expect_ok(r, name)
    assert r['cost'] == estimate, (name, r['cost'], estimate)
    print(f'{name:26} cost {r["cost"]:>12,}  prog {r["program_bytes"]:>7,} B  witness {r["witness_bytes"]:>6,} B  ok')
    return r


def group_law(rng):
    t, q = rand_point(rng), rand_point(rng)
    s, h = M.add_hint(t, q)
    d, hd = M.dbl_hint(t)
    fp = F.Fp(Num())
    g = M.G1(fp)
    assert [F.from_mont(x) for x in g.add(M.mont(t), M.mont(q), M.mont(h))] == list(s)
    assert [F.from_mont(x) for x in g.dbl(M.mont(t), M.mont(hd)[0])] == list(d)

    def build(add, hints, expect):
        def b(fp, a):
            g, sub = M.G1(fp), fp.be.pack
            out = g.add(sub(a[0:2]), sub(a[2:4]), sub(a[4:6])) if add else g.dbl(sub(a[0:2]), a[2])
            return check_point(fp, out, expect)

        return b

    run('g1_add', 6, M.mont(t) + M.mont(q) + M.mont(h), build(True, h, s), {})
    run('g1_dbl', 3, M.mont(t) + M.mont(hd), build(False, hd, d), {})
    run('g1_add_wrong_slope', 6, M.mont(t) + M.mont(q) + M.mont([h[0] + 1, h[1]]), build(True, h, s), {}, ok=False)
    run('g1_add_wrong_inverse', 6, M.mont(t) + M.mont(q) + M.mont([h[0], h[1] + 1]), build(True, h, s), {}, ok=False)
    run('g1_dbl_wrong_slope', 3, M.mont(t) + M.mont([hd[0] + 1]), build(False, hd, d), {}, ok=False)
    print('group law: ok')


def var_nodes(w, prefix='wv'):
    """The witness nodes of var_witness's hints."""
    nodes = {}
    for g, hs in enumerate(w['tables']):
        for j, h in enumerate(hs):
            nodes[f'{prefix}t{g}_{j}'] = wspec(M.mont(h))
    bits = len(w['steps'])
    for si, hs in enumerate(w['steps']):
        j = bits - 1 - si
        it = iter(hs)
        if si:
            nodes[f'{prefix}s{j}d'] = wspec(M.mont(next(it)))
        for g in range(len(w['tables'])):
            nodes[f'{prefix}s{j}a{g}'] = wspec(M.mont(next(it)))
    return nodes


def var_msm(rng, n_points, bits, name):
    pts = [rand_point(rng) for _ in range(n_points)]
    if bits == M.HALF_BITS:
        scalars = [rng.randrange(R) for _ in range(n_points)]
    else:
        scalars = [rng.randrange(-(2**bits) + 1, 2**bits) | 1 for _ in range(n_points)]
    w = M.var_witness(pts, scalars, bits)
    expect = M.var_offset(bits)  # the sum carries the start point's multiple
    for pt, k in zip(pts, scalars):
        expect = B.g1_add(expect, B.g1_mul(pt, k % R))
    assert w['result'] == expect
    # Num
    fp = F.Fp(Num())
    t = M.VarMsm(fp, bits=bits).program([M.mont(p) for p in pts], w['cols'], w)[0]
    assert [F.from_mont(x) for x in t] == list(expect), 'Num MSM'
    vals = [x for p in pts for x in M.mont(p)] + w['cols']

    def build(fp, a):
        n = 2 * n_points
        pts_a = [a[2 * i : 2 * i + 2] for i in range(n_points)]
        t, checks = M.VarMsm(fp, bits=bits).program(pts_a, a[n:])
        return fp.be.checks(checks + [check_point(fp, t, expect)])

    nodes = var_nodes(w)
    r = run(name, len(vals), vals, build, nodes)
    return r, w, vals, build, nodes


def main():
    rng = random.Random(5)
    group_law(rng)
    _, _, vals, build, nodes = var_msm(rng, 4, 8, 'var_msm_8bit')
    # a wrong step hint, and a column word with a bit above its width
    bad = dict(nodes)
    k = next(n for n in bad if n.endswith('a0') and 's3' in n)
    bad[k] = wspec([1, 1])
    run('var_msm_bad_hint', len(vals), vals, build, bad, ok=False)
    v2 = list(vals)
    v2[-1] |= 1 << 200
    run('var_msm_bad_column', len(v2), v2, build, nodes, ok=False)
    if not QUICK:
        var_msm(rng, 4, M.HALF_BITS, 'var_msm_glv_4_points')
    # fixed base
    v = rng.randrange(R)
    fw = M.fixed_witness(B.G1_GEN, v)
    fp = F.Fp(Num())
    t = M.FixedMsm(fp).program(v, fw['hints'])
    assert [F.from_mont(x) for x in t] == list(fw['result'])

    def build_fixed(fp, a):  # the caller checks v < r, which also reads the word's top bits
        rng_chk = Curve(fp).lt_const_check(F.Val(a[0], 0), R).e
        return fp.be.checks([rng_chk, check_point(fp, M.FixedMsm(fp).program(a[0]), fw['result'])])

    run('fixed_msm', 1, [v], build_fixed, {f'wf{j}': wspec(M.mont(h)) for j, h in enumerate(fw['hints'])})
    print('all ok')


if __name__ == '__main__':
    main()
