#!/usr/bin/env python3
"""The pairing check as one polynomial identity (groth/pairing.py), on an instance with
e(A, B) e(L, gamma) e(C, delta) e(alpha, beta) = 1, L = IC_0 + x IC_1 for a public input x.  The model's
S(z) must equal Q(z) M(z), the program must accept, and it must reject witnesses that are wrong in one
place but sealed consistently (r, Q and z recomputed), so that only the identity can catch them: a wrong
slope, a wrong Miller value, a wrong residue witness, a wrong public input.  A wrong challenge and a
false instance must be rejected too.

    python3 tests/test_pairing.py
"""

import os
import random
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth import bn254 as B
from groth import fp as F
from groth import pairing as PC
from groth import poly
from groth.dsl import CheckFailed, Tbalanced, wbalanced, wpair, wv
from groth.sym import Num, Sym, words

P = F.P


def instance(rng, key):
    """delta, the Miller value of (alpha, beta) and the inputs' constants (gamma, IC_0, IC_1) from the key;
    A, B and the input x random, C solving a b + l g + c d + al be = 0 for l = ic_0 + x ic_1."""
    g, d, al, be, ic0, ic1 = (key.randrange(1, B.R) for _ in range(6))
    a, b, x = rng.randrange(1, B.R), rng.randrange(1, B.R), rng.randrange(B.R)
    l = (ic0 + x * ic1) % B.R
    c = (-(a * b + l * g + al * be)) * pow(d, -1, B.R) % B.R
    gamma, delta = B.g2_mul(B.G2_GEN, g), B.g2_mul(B.G2_GEN, d)
    A, Bq, C = B.g1_mul(B.G1_GEN, a), B.g2_mul(B.G2_GEN, b), B.g1_mul(B.G1_GEN, c)
    ic = [B.g1_mul(B.G1_GEN, ic0), B.g1_mul(B.G1_GEN, ic1)]
    alpha_beta = (B.g1_mul(B.G1_GEN, al), B.g2_mul(B.G2_GEN, be))
    L = B.g1_add(ic[0], B.g1_mul(ic[1], x))
    assert B.multi_pairing([(A, Bq), (L, gamma), (C, delta), alpha_beta]).is_one()
    return delta, B.multi_miller_loop_affine([alpha_beta]), PC.gt_constants(ic, gamma), [(A, Bq), (C, delta)], x


def numeric(pc, xs, w):
    (pts, ac), (rz, (leaves, q)) = PC.witness_num(w)
    return pc.program({'x': [F.Val(x, F.WORD_MAX) for x in xs], 'words': xs}, pts, ac, rz, leaves, q)


def program(delta, const, gt, b):
    """The check alone; witness (the input words, the check's witness), or the check's witness alone
    without inputs, and the check's witness nodes."""
    n = len(gt) - 1
    bits = 256 * n + PC.witness_bits()
    be = Sym(bits)
    fp = F.Fp(be)
    pc = PC.PairingCheck(fp, delta, const, gt, b)
    inp, ((pts, ac), rz) = (
        be._unpack('', [words(n), PC.witness_shape()]) if n else ([], be._unpack('', PC.witness_shape()))
    )
    body = pc.program({'x': [F.Val(x, F.WORD_MAX) for x in inp], 'words': inp}, pts, ac, rz)
    wt = f'({Tbalanced(["2^256"] * n)} * {PC.witness_type()})' if n else PC.witness_type()
    be.em.define('w_in', 'witness', f'_ -> {wt}')
    be.em.define('main', f'comp w_in ({body.t})')
    return be.em.text(), 2 * (100 + bits) + body.c, pc


def witness(xs, w):
    main = wpair(wbalanced([wv(256, x) for x in xs]), PC.witness_value(w)) if xs else PC.witness_value(w)
    return {'w_in': main, **PC.witness_nodes(w)}


def tampered(prover, w, x, how):
    """The honest values with one change, sealed again, with the input they are sealed for."""
    v = {k: (list(y) if isinstance(y, list) else dict(y) if isinstance(y, dict) else y) for k, y in w['values'].items()}
    v['a'] = [None if a is None else list(a) for a in v['a']]
    if how == 'slope':
        v['lam'][10] = v['lam'][10] + 1
    elif how == 'Miller value':
        k = next(i for i in range(40, PC.N_STEPS) if PC.COMMIT[i])
        v['a'][k][3] += 1
    elif how == 'residue witness':
        v['ac'][2] += 1
    elif how == 'public input':  # another input, with the honest values: the program selects other factors
        x ^= 1 << 100
    return [x], prover.seal(v, [x], check=False)


def main():
    rng = random.Random(int(os.environ.get('SEED', '5')))
    delta, const, gt, pairs, x = instance(rng, random.Random(11))
    _, (C, _) = pairs  # the check's first point is A itself here (Groth16 passes -A)
    deg = PC.window_plan(1)[0]
    print(f'{PC.N_RELS} relations, S of degree {deg}, Q of {PC.q_words(deg)} coefficients')
    # prover and model
    t0 = time.time()
    prover = PC.Prover(delta, const, gt)
    print(
        f'tables in {time.time() - t0:.1f}s: windows at steps '
        + ', '.join(f'{s} ({len(ws)})' for s, ws in prover.plan.items())
    )
    t0 = time.time()
    w = prover.witness(pairs, [x])
    r, z = F.from_mont(w['r']), F.from_mont(w['z'])
    R = PC.NumRing(z)
    S = PC.horner(R, PC.relations(R, w['values'], prover.lines), r)
    assert poly.evaluate([F.from_mont(q) for q in w['q']], z) * poly.evaluate(poly.M, z) % P == S
    # the degrees the generator counts (and sizes Q by) are the relations' degrees
    degs = [len(poly.trim(rel)) - 1 for rel in PC.relations(PC.PolyRing, w['values'], prover.lines)]
    assert degs == PC._degrees(PC.COMMIT, {s: len(ws) for s, ws in prover.plan.items()})
    print(f'witness in {time.time() - t0:.1f}s, S(z) = Q(z) M(z), relation degrees as counted (at most {max(degs)})')
    bad = [(how, *tampered(prover, w, x, how)) for how in ('slope', 'Miller value', 'residue witness', 'public input')]
    wrong_r = dict(w)
    wrong_r['r'] ^= 1
    bad.append(('challenge', [x], wrong_r))
    # numeric model
    b = PC.bounds()
    pcn = PC.PairingCheck(F.Fp(Num()), delta, const, gt, b)
    numeric(pcn, [x], w)
    for how, xb, wb in bad:
        try:
            numeric(pcn, xb, wb)
            raise AssertionError(f'numeric model accepted a wrong {how}')
        except CheckFailed:
            pass
    print('numeric model ok, rejects the tampered witnesses')
    # false instance: no witness
    assert prover.witness([pairs[0], (B.g1_add(C, B.G1_GEN), delta)], [x]) is None
    # the program
    text, estimate, pc = program(delta, const, gt, b)
    t0 = time.time()
    res = harness.run('pairing', text, witness([x], w), multi=[witness(xb, wb) for _, xb, wb in bad])
    ok = harness.expect_ok(res[0], 'pairing check')
    assert ok['cost'] == estimate, (ok['cost'], estimate)
    for (how, _, _), rb in zip(bad, res[1:]):
        assert not rb.get('ok') and rb.get('stage') in ('exec', 'finalize'), (how, rb)
        print(f'wrong {how:15} rejected')
    print(
        f'pairing check cost {ok["cost"]:,}: setup {pc.parts["setup"]:,}, loop {pc.parts["loop"]:,}, final {pc.parts["final"]:,}'
    )
    print('steps: ' + ', '.join(f'{k} {v:,}' for k, v in pc.costs.items()))
    print(f'program {ok["program_bytes"]:,} B, witness {ok["witness_bytes"]:,} B ({time.time() - t0:.0f}s)')


if __name__ == '__main__':
    main()
