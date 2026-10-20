#!/usr/bin/env python3
"""The verifier of keys with more public inputs (groth/groth16.py): the program is generated within the
bounds of the field arithmetic, and its numeric model accepts a proof and rejects a wrong input.  With three
or more inputs, some additions carry ten or more windows, whose factors' product is normalised partway.

This test does not run the programs: their text grows by about 2.6 MB per input, and the harness takes
25 minutes to parse the 7.9 MB of three inputs.  `INPUTS=3 python3 tests/test_groth16.py` runs that one.

    python3 tests/test_inputs.py
"""

import os
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import bn254 as B
from groth import fp as F
from groth import pairing as PC
from groth.dsl import CheckFailed
from groth.groth16 import Groth16
from groth.sym import Num


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
        bad = dict(wit)
        bad['scalars'] = [inputs[0], (inputs[1] + 1) % B.R, *inputs[2:]]
        try:
            g.verify(g.num_input(bad))
            raise AssertionError('the numeric model accepted a wrong input')
        except CheckFailed:
            pass
        deg = PC.window_plan(n)[0]
        print(
            f'{n} inputs: cost {cost:,} mWU, S of degree {deg}, Q of {PC.q_words(deg)} words, '
            f'program text {len(text) / 1e6:.1f} MB ({time.time() - t0:.0f}s)'
        )
    print('all ok')


if __name__ == '__main__':
    main()
