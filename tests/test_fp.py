#!/usr/bin/env python3
"""F_p arithmetic (groth/core/fp.py): the program against the numeric model, on random words and on words the
jets must reduce first (at least the secp256k1 field prime or group order, as a spender may give them).

python3 tests/test_fp.py          # tests
python3 tests/test_fp.py bench    # cost of each operation
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth.core import fp as F
from groth.core.dsl import Tpairs, wpairs, wv
from groth.core.sym import Num, Sym

P = F.P


def random_words(rng, n, hi):
    return [rng.randrange(hi + 1) for _ in range(n)]


def run_case(name, ops, rng, inputs_hi=F.WORD_MAX, nwords=3, verbose=True, words=None):
    """ops(fp, ins, check) builds the computation and returns its checks.  check(label, val) records the
    word in the numeric pass and verifies the program's word against it in the symbolic pass.  words: the
    input words (random by default)."""
    words = random_words(rng, nwords, inputs_hi) if words is None else words
    # numeric pass: run the model, record every checked word
    be = Num()
    fp = F.Fp(be)
    expected = []

    def check_num(label, v):
        expected.append((label, be.check(v.e, v.hi), v.hi))
        return 0

    ops(fp, [F.Val(w, inputs_hi) for w in words], check_num)
    exp_words = {label: w for label, w, hi in expected}
    # symbolic pass: the same computation with verify(eq_256) against the recorded words
    be = Sym(256 * nwords)
    fp = F.Fp(be)
    paths, path = [], ''
    for i in range(nwords):
        paths.append(path + ('OH' if i < nwords - 1 else 'H'))
        path += 'I'
    ins = [F.Val(be.proj(p, 256), inputs_hi) for p in paths]
    body = ops(fp, ins, lambda label, v: fp.assert_eq_word(v, exp_words[label]))
    ty = Tpairs(*(['2^256'] * nwords))
    be.em.define('w_in', 'witness', f'_ -> {ty}')
    be.em.define('main', f'comp w_in ({body.t})')
    program = be.em.text()
    estimate = 100 + 256 * nwords + 100 + 256 * nwords + body.c
    witness = {'w_in': wpairs(*[wv(256, w) for w in words])}
    r = harness.run(name, program, witness)
    harness.expect_ok(r, name)
    r['words_in'] = words
    ok = r['cost'] == estimate
    if verbose:
        print(
            f'{name:28} cost {r["cost"]:>10}  estimate {estimate:>10}  {"ok" if ok else "MISMATCH"}  '
            f'prog {r["program_bytes"]} B  ({r["seconds"]:.1f}s)'
        )
    assert ok, (r['cost'], estimate)
    return r, expected


def field_value(word):
    return F.from_mont(word)


# the operation chains
def ops_basic(fp, ins, check):
    be = fp.be
    a, b, c = (fp.normalize(x) for x in ins)
    out = [check('a', a), check('b', b), check('c', c)]

    def body(v, lift):
        a, b, c = v
        m = fp.mul(a, b)
        out.append(check('a*b', m))
        s = fp.sqr(a)
        out.append(check('a^2', s))
        t = fp.add(m, s)
        out.append(check('ab+a^2', t))
        n = fp.neg(t)
        out.append(check('-(ab+a^2)', n))
        u = fp.sub(a, n)
        out.append(check('a+(ab+a^2)', u))  # bound 4.29 p
        u = fp.normalize(u)
        out.append(check('normalized', u))  # bound 1.24 p
        d = fp.double(u)
        out.append(check('2(...)', d))
        mc = fp.mul_const(d, 12345)
        out.append(check('*12345', mc))
        dt = fp.dot([(a, b), (c, a), (b, b), (c, c)], neg=(1, 3))
        out.append(check('ab-ca+bb-cc', dt))
        return be.checks(out[3:])

    inner = fp.let([a, b, c], body)
    tm = fp.to_mont(fp.raw(ins[0].e, F.WORD_MAX))
    fm = fp.from_mont(tm)
    return be.checks(out[:3] + [inner, check('to_mont(a_raw)', tm), check('from_mont', fm)])


def ops_chain(fp, ins, check):
    """A long multiplication chain through `let` (every operand must be bound, since an expression used
    twice runs twice); the bounds settle at 1.34 p.  Then sums up to the p_s limit."""
    be = fp.be
    a, b, c = (fp.normalize(x) for x in ins)

    def step(i, x, a, b, c):
        if i == 12:
            y = fp.add(fp.add(x, a), fp.add(b, c))  # four terms below 1.34 p: 5.1 p < 5.29 p
            return be.checks([check('chain12', x), check('sum4', y), check('y*b', fp.mul(y, b))])
        nxt = fp.mul(x, b) if i % 2 == 0 else fp.sqr(x)
        return fp.let([nxt], lambda nv, lift: step(i + 1, nv[0], lift(a), lift(b), lift(c)))

    return fp.let([a, b, c], lambda nv, lift: step(0, nv[0], nv[0], nv[1], nv[2]))


def ops_dot(fp, ins, check):
    """Large dot products near the CRT bound."""
    be = fp.be
    a, b, c = (fp.normalize(x) for x in ins)

    def body(v, lift):
        a, b, c = v
        # 12 products of 1.29 p values: 12 * 1.67 = 20 p^2 < 22.7 p^2
        terms = [(a, b), (b, c), (c, a), (a, a), (b, b), (c, c)] * 2
        return be.checks([check('dot12', fp.dot(terms)), check('dot6neg', fp.dot(terms[:6], neg=(0, 2, 4)))])

    return fp.let([a, b, c], body)


def main():
    rng = random.Random(int(os.environ.get('SEED', '1')))
    # words that random draws below 2^256 almost never give: the jets reduce them modulo their primes
    edge = [2**256 - 1, Num.P_SECP + 5, Num.N_SECP + 7]
    for it in [*range(int(os.environ.get('ITERS', '2'))), 'edge']:
        words = edge if it == 'edge' else None
        r, exp = run_case(f'fp_basic_{it}', ops_basic, rng, words=words)
        d = {label: word for label, word, hi in exp}
        a, b, c = (field_value(d[k]) for k in 'abc')
        f = field_value
        assert f(d['a*b']) == a * b % P and f(d['a^2']) == a * a % P
        assert f(d['ab+a^2']) == (a * b + a * a) % P and f(d['-(ab+a^2)']) == -(a * b + a * a) % P
        assert f(d['a+(ab+a^2)']) == (a + a * b + a * a) % P
        assert f(d['2(...)']) == 2 * (a + a * b + a * a) % P
        assert f(d['*12345']) == 12345 * 2 * (a + a * b + a * a) % P
        assert f(d['ab-ca+bb-cc']) == (a * b - c * a + b * b - c * c) % P
        assert f(d['to_mont(a_raw)']) == r['words_in'][0] % P
        assert d['from_mont'] % P == r['words_in'][0] % P  # a plain (non-Montgomery) word
        r, exp = run_case(f'fp_chain_{it}', ops_chain, rng, words=words)
        d = {label: word for label, word, hi in exp}
        a, b, c = (field_value(w) for w in r['words_in'])
        x = a
        for i in range(12):
            x = x * b % P if i % 2 == 0 else x * x % P
        assert f(d['chain12']) == x and f(d['sum4']) == (x + a + b + c) % P and f(d['y*b']) == (x + a + b + c) * b % P
        r, exp = run_case(f'fp_dot_{it}', ops_dot, rng, words=words)
        d = {label: word for label, word, hi in exp}
        a, b, c = (field_value(w) for w in r['words_in'])
        assert f(d['dot12']) == 2 * (a * b + b * c + c * a + a * a + b * b + c * c) % P
        assert f(d['dot6neg']) == (-a * b + b * c - c * a + a * a - b * b + c * c) % P
    print('all ok')


def bench():
    """Cost of each operation on operands read from the witness (bounds 2p), net of reading the
    operands and of the check that observes the result."""
    rng = random.Random(5)

    def one(label, fn, nwords=3, hi=2 * P - 1):
        def ops(fp, ins, check):
            vals = [fp.raw(x.e, hi) for x in ins]
            touch = [check(f'in{i}', v) for i, v in enumerate(vals)]  # every witness part must be consumed
            res = [] if fn is None else [check(label, fn(fp, vals))]
            return fp.be.checks(touch + res)

        r, _ = run_case(
            'bench_' + label.replace(' ', '_').replace('(', '').replace(')', ''),
            ops,
            rng,
            inputs_hi=hi,
            nwords=nwords,
            verbose=False,
        )
        return r['cost']

    base = one('base', None)
    read = one('read', lambda fp, v: v[0])  # check of a plain projection (take iden = 456 mWU)
    overhead = read - base - 456  # cost of observing a result: verify(eq_256(x, const))
    cases = [
        ('mul', lambda fp, v: fp.mul(v[0], v[1])),
        ('sqr', lambda fp, v: fp.sqr(v[0])),
        ('mul_const', lambda fp, v: fp.mul_const(v[0], 7)),
        ('normalize', lambda fp, v: fp.normalize(v[0])),
        ('add', lambda fp, v: fp.add(v[0], v[1])),
        ('double', lambda fp, v: fp.double(v[0])),
        ('neg', lambda fp, v: fp.neg(v[0])),
        ('sub', lambda fp, v: fp.sub(v[0], v[1])),
        ('dot2', lambda fp, v: fp.dot([(v[0], v[1]), (v[1], v[2])])),
        ('dot2 (one term negated)', lambda fp, v: fp.dot([(v[0], v[1]), (v[1], v[2])], neg=(1,))),
        ('dot3', lambda fp, v: fp.dot([(v[0], v[1]), (v[1], v[2]), (v[2], v[0])])),
        ('dot4', lambda fp, v: fp.dot([(v[0], v[1]), (v[1], v[2]), (v[2], v[0]), (v[0], v[0])])),
        (
            'dot6 (operands < 1.5p)',
            lambda fp, v: fp.dot([(v[0], v[1]), (v[1], v[2]), (v[2], v[0]), (v[0], v[0]), (v[1], v[1]), (v[2], v[2])]),
        ),
    ]
    for label, fn in cases:
        c = one(label, fn, hi=(3 * P // 2 if 'dot6' in label else 2 * P - 1)) - base - overhead
        print(f'{label:26} {c:>8} mWU')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'bench':
        bench()
    else:
        main()
