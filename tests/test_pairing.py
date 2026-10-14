#!/usr/bin/env python3
"""The pairing check as one polynomial identity (groth/pairing.py), on an instance with
e(A, B) e(L, gamma) e(C, delta) = 1.  The model's S(z) must equal Q(z) M(z), the program must accept,
and it must reject witnesses that are wrong in one place but sealed consistently (r, Q and z
recomputed), so that only the identity can catch them: a wrong slope, a wrong Miller value, a wrong s.
A wrong challenge and a false instance must be rejected too.

    python3 tests/test_pairing.py
"""
import os, random, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import fp as F, bn254 as B, poly, pairing as PC
from groth.dsl import CheckFailed, Tbalanced, wv, wpair, wbalanced
from groth.sym import Sym, Num, words
import harness

P = F.P


def instance(rng, key):
    """gamma, delta from the key; A, B, L random, C solving a b + l g + c d = 0"""
    g, d = key.randrange(1, B.R), key.randrange(1, B.R)
    a, b, l = (rng.randrange(1, B.R) for _ in range(3))
    c = (-(a * b + l * g)) * pow(d, -1, B.R) % B.R
    gamma, delta = B.g2_mul(B.G2_GEN, g), B.g2_mul(B.G2_GEN, d)
    A, Bq, L, C = B.g1_mul(B.G1_GEN, a), B.g2_mul(B.G2_GEN, b), B.g1_mul(B.G1_GEN, l), B.g1_mul(B.G1_GEN, c)
    return gamma, delta, [(A, Bq), (L, gamma), (C, delta)]


INPUT = 12345 # a public input word: the check only hashes it


def numeric(gamma, delta, const, L, w, b):
    pc = PC.PairingCheck(F.Fp(Num()), gamma, delta, const, b)
    Lw = [F.Val(F.to_mont(L[0]), F.WORD_MAX), F.Val(F.to_mont(L[1]), F.WORD_MAX)]
    (pts, (c, ci)), ((sel, rz), (leaves, q)) = PC.witness_num(w)
    return pc.program({'L': Lw, 'words': [INPUT]}, pts, c, ci, sel, rz, leaves, q)


def program(gamma, delta, const, b):
    """The check alone; witness ((xL, yL), input word, the check's witness)."""
    bits = 3 * 256 + PC.witness_bits()
    be = Sym(bits); fp = F.Fp(be)
    pc = PC.PairingCheck(fp, gamma, delta, const, b)
    (Lw, inp), ((pts, (c, ci)), ((sel, rz), (leaves, q))) = be._unpack('', [[words(2), words(1)], PC.witness_shape()])
    body = pc.program({'L': [F.Val(x, F.WORD_MAX) for x in Lw], 'words': inp}, pts, c, ci, sel, rz, leaves, q)
    be.em.define('w_in', 'witness', f'_ -> (({Tbalanced(["2^256"] * 2)} * 2^256) * {PC.witness_type()})')
    be.em.define('main', f'comp w_in ({body.t})')
    return be.em.text(), 2 * (100 + bits) + body.c, pc


def witness(L, w):
    return {'w_in': wpair(wpair(wbalanced([wv(256, F.to_mont(L[0])), wv(256, F.to_mont(L[1]))]), wv(256, INPUT)),
                          PC.witness_value(w))}


def tampered(prover, w, how):
    """The honest values with one change, sealed again."""
    v = {k: (list(x) if isinstance(x, list) else dict(x) if isinstance(x, dict) else x) for k, x in w['values'].items()}
    v['f'] = [None if f is None else list(f) for f in v['f']]
    if how == 'slope':
        v['lam'][10] = v['lam'][10] + 1
    elif how == 'Miller value':
        k = next(i for i in range(40, PC.N_STEPS) if PC.COMMIT[i])
        v['f'][k][3] += 1
    elif how == 's':
        v['s'] = (v['s'] + 1) % 3
    return prover.seal(v, [INPUT], check=False)


def main():
    rng = random.Random(int(os.environ.get('SEED', '5')))
    gamma, delta, pairs = instance(rng, random.Random(11))
    assert B.multi_pairing(pairs).is_one()
    (A, Bq), (L, _), (C, _) = pairs # the check's first point is A itself here (Groth16 passes -A)
    const = B.Fp12.one()
    print(f'{PC.N_RELS} relations, S of degree {PC.DEG_S}, Q of {PC.N_Q} coefficients')
    # prover and model
    prover = PC.Prover(gamma, delta, const)
    t0 = time.time()
    w = prover.witness(pairs, [INPUT])
    r, z = F.from_mont(w['r']), F.from_mont(w['z'])
    R = PC.NumRing(z)
    S = PC.horner(R, PC.relations(R, w['values'], prover.lines, prover.table), r)
    assert S == poly.evaluate([F.from_mont(x) for x in w['q']], z) * poly.evaluate(poly.M, z) % P
    print(f'witness in {time.time() - t0:.1f}s: s = {w["s"]}, S(z) = Q(z) M(z)')
    bad = [(how, tampered(prover, w, how)) for how in ('slope', 'Miller value', 's')]
    wrong_r = dict(w); wrong_r['r'] ^= 1
    # numeric model
    b = PC.bounds()
    numeric(gamma, delta, const, L, w, b)
    for how, wb in bad + [('challenge', wrong_r)]:
        try:
            numeric(gamma, delta, const, L, wb, b)
            raise AssertionError(f'numeric model accepted a wrong {how}')
        except CheckFailed:
            pass
    print('numeric model ok, rejects the tampered witnesses')
    # false instance: no witness
    false = [pairs[0], pairs[1], (B.g1_add(C, B.G1_GEN), delta)]
    assert prover.witness(false, [INPUT]) is None
    # the program
    text, estimate, pc = program(gamma, delta, const, b)
    t0 = time.time()
    res = harness.run('pairing', text, witness(L, w), multi=[witness(L, wb) for _, wb in bad + [('challenge', wrong_r)]])
    ok = harness.expect_ok(res[0], 'pairing check')
    assert ok['cost'] == estimate, (ok['cost'], estimate)
    for (how, _), rb in zip(bad + [('challenge', None)], res[1:]):
        assert not rb.get('ok') and rb.get('stage') in ('exec', 'finalize'), (how, rb)
        print(f'wrong {how:13} rejected')
    print(f'pairing check cost {ok["cost"]:,}: setup {pc.parts["setup"]:,}, loop {pc.parts["loop"]:,}, final {pc.parts["final"]:,}')
    print('steps: ' + ', '.join(f'{k} {v:,}' for k, v in pc.costs.items()))
    print(f'program {ok["program_bytes"]:,} B, witness {ok["witness_bytes"]:,} B ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
