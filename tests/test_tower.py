#!/usr/bin/env python3
"""Tower products and Frobenius maps (groth/tower.py) against bn254.py, with their costs.

    python3 tests/test_tower.py
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B
from groth.tower import Tower, ref_to_list, embed_fp2, embed_fp6
from groth.sym import Sym, Num
from groth.dsl import wv, wbalanced, Tbalanced, balanced_paths
import harness

P = F.P


def rand_fp12(rng):
    return B.Fp12(B.Fp6(*[B.Fp2(rng.randrange(P), rng.randrange(P)) for _ in range(3)]),
                  B.Fp6(*[B.Fp2(rng.randrange(P), rng.randrange(P)) for _ in range(3)]))



def run_op(name, inputs, build, rng, verbose=True):
    """inputs: list of lists of field values (each becomes a group of witness words in Montgomery form);
    build(fp, tower, groups, check) -> E (the checks); returns the harness result and the recorded words"""
    words = [[F.to_mont(v) for v in grp] for grp in inputs]
    flat = [w for grp in words for w in grp]
    sizes = [len(g) for g in words]

    def split(vals):
        out, i = [], 0
        for n in sizes:
            out.append(vals[i:i + n]); i += n
        return out

    # numeric pass
    be = Num(); fp = F.Fp(be); expected = []

    def check_num(label, v):
        expected.append((label, be.check(v.e, v.hi), v.hi))
        return 0
    build(fp, Tower(fp), split([F.Val(w, P - 1) for w in flat]), check_num)
    exp = {label: w for label, w, hi in expected}
    # symbolic pass
    be = Sym(256 * len(flat)); fp = F.Fp(be)
    ins = [F.Val(be.proj(p, 256), P - 1) for p in balanced_paths(len(flat))]
    body = build(fp, Tower(fp), split(ins), lambda label, v: fp.assert_eq_word(v, exp[label]))
    be.em.define('w_in', 'witness', f'_ -> {Tbalanced(["2^256"] * len(flat))}')
    be.em.define('main', f'comp w_in ({body.t})')
    estimate = 2 * (100 + 256 * len(flat)) + body.c
    r = harness.run(name, be.em.text(), {'w_in': wbalanced([wv(256, w) for w in flat])})
    harness.expect_ok(r, name)
    ok = r['cost'] == estimate
    if verbose:
        print(f'{name:16} cost {r["cost"]:>10}  estimate {estimate:>10}  {"ok" if ok else "MISMATCH"}  '
              f'prog {r["program_bytes"]} B  ({r["seconds"]:.1f}s)')
        if os.environ.get('STATS'):
            print(be.report())
    assert ok
    return r, exp


def decode(exp, labels):
    """recorded words -> field values"""
    return [F.from_mont(exp[l]) if l in exp else None for l in labels]


def check_elem(exp, prefix, ref):
    got = decode(exp, [f'{prefix}{k}' for k in range(12)])
    want = ref_to_list(ref)
    for k in range(12):
        if got[k] is None:
            assert want[k] == 0, (prefix, k)
        else:
            assert got[k] == want[k], (prefix, k, got[k], want[k])


def checks_of(fp, check, prefix, elem):
    return [check(f'{prefix}{k}', v) for k, v in enumerate(elem) if v is not None]


# operations under test
def op_fp12_mul(fp, tw, groups, check):
    A, Bv = groups
    return tw.mul_bound(A, Bv, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)))


def op_fp12_sqr(fp, tw, groups, check):
    (A,) = groups
    return tw.mul_bound(A, A, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)), symmetric=True)


def op_fp12_mul034(fp, tw, groups, check):
    A, L = groups # L = (c0x, c0y, c3x, c3y, c4x, c4y)
    Bv = [None] * 12
    Bv[0], Bv[1], Bv[6], Bv[7], Bv[8], Bv[9] = L
    return tw.mul_bound(A, Bv, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)))


def op_fp12_mul_line(fp, tw, groups, check):
    """f times an affine-style line yP + c3 w + c4 v w (c0 a scalar): 60 terms"""
    A, L = groups # L = (yP, c3x, c3y, c4x, c4y)
    Bv = [None] * 12
    Bv[0], Bv[6], Bv[7], Bv[8], Bv[9] = L
    return tw.mul_bound(A, Bv, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)))


def op_frobenius(n):
    def op(fp, tw, groups, check):
        (A,) = groups
        C = tw.frobenius(A, n)
        return fp.be.checks(checks_of(fp, check, 'c', C))
    return op


def op_fp6_mul(fp, tw, groups, check):
    A6, B6 = groups
    return tw.mul_bound(embed_fp6(A6), embed_fp6(B6), lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)))


def op_fp6_sqr(fp, tw, groups, check):
    (A6,) = groups
    E = embed_fp6(A6)
    return tw.mul_bound(E, E, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)), symmetric=True)


def op_fp2_mul(fp, tw, groups, check):
    A2, B2 = groups
    return tw.mul_bound(embed_fp2(*A2), embed_fp2(*B2), lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)))


def op_fp2_sqr(fp, tw, groups, check):
    (A2,) = groups
    E = embed_fp2(*A2)
    return tw.mul_bound(E, E, lambda C, lift: fp.be.checks(checks_of(fp, check, 'c', C)), symmetric=True)


def main():
    rng = random.Random(int(os.environ.get('SEED', '2')))
    a, b = rand_fp12(rng), rand_fp12(rng)
    # F_p2
    r, exp = run_op('fp2_mul', [[a.c0.c0.c0, a.c0.c0.c1], [b.c0.c0.c0, b.c0.c0.c1]], op_fp2_mul, rng)
    check_elem(exp, 'c', B.Fp12(B.Fp6(a.c0.c0 * b.c0.c0)))
    r, exp = run_op('fp2_sqr', [[a.c0.c0.c0, a.c0.c0.c1]], op_fp2_sqr, rng)
    check_elem(exp, 'c', B.Fp12(B.Fp6(a.c0.c0.square())))
    # F_p6
    a6 = ref_to_list(a)[:6]; b6 = ref_to_list(b)[:6]
    r, exp = run_op('fp6_mul', [a6, b6], op_fp6_mul, rng)
    check_elem(exp, 'c', B.Fp12(a.c0 * b.c0))
    r, exp = run_op('fp6_sqr', [a6], op_fp6_sqr, rng)
    check_elem(exp, 'c', B.Fp12(a.c0.square()))
    # F_p12
    r, exp = run_op('fp12_mul', [ref_to_list(a), ref_to_list(b)], op_fp12_mul, rng)
    check_elem(exp, 'c', a * b)
    r, exp = run_op('fp12_sqr', [ref_to_list(a)], op_fp12_sqr, rng)
    check_elem(exp, 'c', a.square())
    l0, l3, l4 = b.c0.c0, b.c1.c0, b.c1.c1
    r, exp = run_op('fp12_mul034', [ref_to_list(a), [l0.c0, l0.c1, l3.c0, l3.c1, l4.c0, l4.c1]], op_fp12_mul034, rng)
    check_elem(exp, 'c', a.mul_by_034(l0, l3, l4))
    yP = rng.randrange(P)
    r, exp = run_op('fp12_mul_line', [ref_to_list(a), [yP, l3.c0, l3.c1, l4.c0, l4.c1]], op_fp12_mul_line, rng)
    check_elem(exp, 'c', a.mul_by_034(B.Fp2(yP, 0), l3, l4))
    for n in (1, 2, 3):
        r, exp = run_op(f'frobenius{n}', [ref_to_list(a)], op_frobenius(n), rng)
        check_elem(exp, 'c', a.frobenius(n))
    print('all ok')


if __name__ == '__main__':
    main()
