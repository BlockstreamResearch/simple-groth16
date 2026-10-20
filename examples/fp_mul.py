#!/usr/bin/env python3
"""Writes fp_mul.simpl: one F_p product of the two witness words in fp_mul.w0.json, checked against
the expected product.

    python3 examples/fp_mul.py > examples/fp_mul.simpl
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from groth import fp as F
from groth.sym import Sym

with open(os.path.join(HERE, 'fp_mul.w0.json')) as f:
    w = json.load(f)['w_in']['p']
a, b = (int(x['w'], 16) for x in w)
be = Sym(512)
fp = F.Fp(be)
x, y = F.Val(be.proj('OH', 256), F.P - 1), F.Val(be.proj('IH', 256), F.P - 1)
body = fp.assert_eq_const(fp.mul(x, y), F.from_mont(a) * F.from_mont(b) % F.P)
be.em.define('w_in', 'witness', '_ -> (2^256 * 2^256)')
be.em.define('main', f'comp w_in ({body.t})')
sys.stdout.write(be.em.text())
