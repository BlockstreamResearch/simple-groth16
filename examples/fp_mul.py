#!/usr/bin/env python3
"""Writes fp_mul.simpl: one F_p product of the two witness words in fp_mul.w0.json, checked against
the expected product.  Each word is first checked below 2^254, as the verifiers check the words they
multiply: the reduction is exact only within the static bound the generator assumes.

    python3 examples/fp_mul.py > examples/fp_mul.simpl
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from groth.core import fp as F
from groth.core.sym import Sym

with open(os.path.join(HERE, 'fp_mul.w0.json')) as f:
    w = json.load(f)['w_in']['p']
a, b = (int(x['w'], 16) for x in w)
be = Sym(512)
fp = F.Fp(be)
F_HI = 2**254 - 1  # the bound of a checked word (pairing.F_HI)
x, y = F.Val(be.proj('OH', 256), F_HI), F.Val(be.proj('IH', 256), F_HI)


def below_2_254(w):
    """The word's two top bits are 0 (pairing.PairingCheck.top2_zero)."""
    return be.verify(be.not1(be.jet('or_1', be.sub(w, 'OOOOOOO', 2), 1)))


product = fp.assert_eq_const(fp.mul(x, y), F.from_mont(a) * F.from_mont(b) % F.P)
body = be.checks([below_2_254(x.e), below_2_254(y.e), product])
be.em.define('w_in', 'witness', '_ -> (2^256 * 2^256)')
be.em.define('main', f'comp w_in ({body.t})')
sys.stdout.write(be.em.text())
