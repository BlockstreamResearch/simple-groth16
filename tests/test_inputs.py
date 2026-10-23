#!/usr/bin/env python3
"""The verifier of keys with more public inputs (groth/groth16.py): the program is generated within the
bounds of the field arithmetic, and its numeric model accepts a proof and rejects a wrong input, also when
r, Q and z are sealed again so that the identity is what rejects it.  With three or more inputs, some
additions carry ten or more windows, whose factors' product is normalised partway (PairingCheck.prod).

The whole programs do not run here: their text grows by about 2.6 MB per input, and the harness takes 25
minutes to parse the 7.9 MB of three inputs (`INPUTS=3 python3 tests/test_groth16.py` runs that one).
Instead, the window factors of the 3-input key's last step, where the product is normalised, run in the
harness as a program of their own, and must give the numeric model's words.

    python3 tests/test_inputs.py
"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import harness

from groth import bn254 as B
from groth import fp as F
from groth import pairing as PC
from groth.dsl import CheckFailed, Tbalanced, wbalanced, wv
from groth.groth16 import Groth16
from groth.sym import Num, Sym, flat, words


def rejected(g, w, label):
    """The numeric model rejects the witness at the identity ('verify failed'; it runs before the challenge
    and the range checks)."""
    try:
        g.verify(g.num_input(w))
    except CheckFailed as e:
        assert str(e) == 'verify failed', (label, str(e))
        return
    raise AssertionError(f'the numeric model accepted {label}')


def win_factors_program(g, s, names):
    """win_factors at step s as a program of its own: w_in = (the run values `names`, expected g_N, g_D),
    and the program checks that the factors equal the expected words.  (text, cost estimate)"""
    be = Sym(256 * (len(names) + 2))
    pc = PC.PairingCheck(F.Fp(be), g.vk['delta'], g.pc.prover.const, g.pc.prover.gt, PC.bounds())
    acc = be._unpack('', words(len(names) + 2))
    out = pc.win_factors(s, dict(zip(names, acc)), PC.Q_KEYS[PC.STEPS[s]][2:])
    expect = acc[len(names) :]
    same = be.with_env(
        be.pair(out, be.pair(expect[0], expect[1])),
        [words(2), words(2)],
        lambda a: be.checks([be.verify(be.eq256(a[0][k], a[1][k])) for k in range(2)]),
    )
    # every word is read whole, so that the witness has the declared type even where the step reads part of it
    body = be.checks([same] + [be.verify(be.eq256(x, x)) for x in acc])
    be.em.define('w_in', 'witness', f'_ -> {Tbalanced(["2^256"] * (len(names) + 2))}')
    be.em.define('main', f'comp w_in ({body.t})')
    uses = be.em.tree_uses()
    be.em.defs = [d for d in be.em.defs if d[0] in uses]  # the step functions PairingCheck defines are not used
    return be.em.text(), 2 * (100 + 256 * (len(names) + 2)) + body.c


def check_win_factors(g, wit, s):
    """The Sym code of win_factors at step s in the harness against the numeric model, on the honest run
    values and on run values at their bounds; and a wrong expected word must be rejected."""
    pc = g.pc
    scalars, ((pts, ac), (rz, _)) = g.num_input(wit)[0]
    (_, run), _ = pc.setup({'x': [F.Val(a, B.R - 1) for a in scalars], 'words': scalars}, pts, ac, rz)
    honest = dict(zip(pc.run, flat(run)))
    names = [f'in{i}' for i in pc.ins] + ['z1', 'z2', 'zeta', 'cm', 'cp']
    edge = dict.fromkeys(names, PC.KB) | {f'in{i}': 2**256 - 1 for i in pc.ins}
    base = PC.Q_KEYS[PC.STEPS[s]][2:]
    cases = []
    for rv in (honest, edge):
        gn, gd = pc.win_factors(s, rv, base)
        cases.append({'w_in': wbalanced([wv(256, rv[k]) for k in names] + [wv(256, gn), wv(256, gd)])})
    gn, gd = pc.win_factors(s, honest, base)
    wrong = {'w_in': wbalanced([wv(256, honest[k]) for k in names] + [wv(256, gn + 1), wv(256, gd)])}
    text, estimate = win_factors_program(g, s, names)
    res = harness.run(f'win_factors_{len(pc.ins)}_{s}', text, cases[0], multi=cases[1:] + [wrong])
    for r in res[:-1]:
        harness.expect_ok(r, f'win_factors at step {s}')
        assert r['cost'] == estimate, (r['cost'], estimate)
    harness.expect_rejected(res[-1], 'a wrong factor')
    print(f'  the window factors of step {s} ({len(pc.prover.plan[s])} windows) run as the model computes them')


def main():
    bnd = PC.bounds()
    for n in (3, 4, 5):
        t0 = time.time()
        vk, proof, inputs = B.groth16_instance(n, seed=7)
        text, _, cost = Groth16.compile(vk, b=bnd)
        g = Groth16(F.Fp(Num()), vk, b=bnd)
        wit = g.witness(proof, inputs)
        assert wit is not None
        g.verify(g.num_input(wit))
        wrong = [inputs[0], (inputs[1] + 1) % B.R, *inputs[2:]]
        rejected(g, dict(wit, scalars=wrong), 'a wrong input')
        # sealed again with the honest values: the challenges pass and the relations the prover computes hold,
        # but the factors the tables give for the wrong input are not the values', so the identity rejects it
        sealed = g.pc.prover.seal(wit['values'], wrong)
        rejected(g, dict(sealed, scalars=wrong), 'a wrong input, sealed')
        deg = PC.window_plan(n)[0]
        print(
            f'{n} inputs: cost {cost:,} mWU, S of degree {deg}, Q of {PC.q_words(deg)} words, '
            f'program text {len(text) / 1e6:.1f} MB ({time.time() - t0:.0f}s)'
        )
        if n == 3:  # the last step, where prod normalises
            check_win_factors(g, wit, PC.N_STEPS - 1)
    print('all ok')


if __name__ == '__main__':
    main()
