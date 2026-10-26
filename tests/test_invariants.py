#!/usr/bin/env python3
"""The generator refuses to emit a program whose soundness argument would not hold: loop bounds that the
step functions do not keep, a projection that is not a whole subtree, a binding by the tree for a key with
more than one public input.  For a witness node read twice, the use count follows the tree unfolding,
which compile() checks.  (No addition meeting T = Q: tests/test_g2_check.py.)  And every
check of the generated verifier is on the path of every spend: none under a branch that pruning could drop.

    python3 tests/test_invariants.py
"""

import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth.core import bn254 as B
from groth.core import fp as F
from groth.core import pairing as PC
from groth.core.dsl import CheckFailed, Emitter
from groth.core.sym import Sym, words
from groth.groth16 import Groth16


def parse(expr):
    """The human encoding's expression as nested lists of atoms, one list per parenthesis."""
    stack = [[]]
    for tok in re.findall(r'[()]|[^\s()]+', expr):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            inner = stack.pop()
            stack[-1].append(inner)
        else:
            stack[-1].append(tok)
    return stack[0]


def atoms(node):
    return [node] if isinstance(node, str) else [a for x in node for a in atoms(x)]


def case_branches(expr):
    """The two branches of every case in the expression, nested ones included."""
    out, todo = [], [parse(expr)]
    while todo:
        items = todo.pop()
        for i, x in enumerate(items):
            if x == 'case':
                out += items[i + 1 : i + 3]
            elif isinstance(x, list):
                todo.append(x)
    return out


def verify_nodes(text):
    """(the definitions that apply jet_verify, those reachable from main, those under a case branch, the
    number of cases) of a program text"""
    defs = dict(line.split(' := ', 1) for line in text.splitlines())
    exprs = {k: v.split(' : ')[0] for k, v in defs.items()}  # without the witness nodes' types
    refs = {k: [t for t in atoms(parse(v)) if t in defs] for k, v in exprs.items()}

    def reach(roots):
        seen, todo = set(), list(roots)
        while todo:
            k = todo.pop()
            if k not in seen:
                seen.add(k)
                todo += refs[k]
        return seen

    verifies = {k for k, v in exprs.items() if 'jet_verify' in atoms(parse(v))}
    in_case = reach(t for v in exprs.values() for branch in case_branches(v) for t in atoms(branch) if t in defs)
    n_cases = sum(atoms(parse(v)).count('case') for v in exprs.values())
    return verifies, reach(['main']), in_case, n_cases


def refused(f, expect):
    try:
        f()
    except CheckFailed as e:
        assert expect in str(e), (expect, str(e))
        return
    raise AssertionError(f'not refused: {expect}')


def main():
    # the tree unfolding: a node shared by two parents occurs twice
    em = Emitter()
    em.define('w', 'witness', '_ -> 2')
    n = em.share('k', 'pair w w')
    em.define('main', f'comp {n} unit')
    assert em.tree_uses() == {'main': 1, n: 1, 'w': 2}
    # the verifier's witness nodes each occur once (Groth16.compile checks it)
    vk, _, _ = B.groth16_instance(1, seed=7)
    text, _, _ = Groth16.compile(vk, 1)
    print('each witness node is read once')
    # every check of the verifier runs: each node that applies jet_verify is reachable from main, and none
    # lies under a branch of a case, which pruning could drop
    verifies, reachable, in_case, n_cases = verify_nodes(text)
    assert n_cases > 1000 and verifies and verifies <= reachable and not verifies & in_case
    print(f'all {len(verifies)} checks of the verifier are reachable, none under a branch of its {n_cases:,} cases')
    v, _, c, _ = verify_nodes('a := comp unit jet_verify\nb := comp (case (drop a) iden) unit\nmain := b\n')
    assert v == {'a'} and v <= c  # and a check under a case is seen
    # bounds of the loop state that the step functions would exceed
    for nm in ('N', 'D', 'acc', 'x', 'y', 'qz'):
        b = dict(PC.bounds())
        b[nm] = b[nm] * 9 // 10
        refused(lambda b=b: Groth16(F.Fp(Sym(0)), vk, b=b), f'the loop state {nm} exceeds its bound')
    print('loop bounds that do not hold are refused')
    # projections
    be = Sym(0)
    acc = be._unpack('', words(4))
    assert be.subtree(acc).t == 'iden' and be.subtree(acc[:2]).path is not None
    refused(lambda: be.subtree(acc[:3]), 'not a whole subtree')
    refused(lambda: be.subtree([acc[0], acc[0], acc[1]]), 'not a whole subtree')
    refused(lambda: be.subtree([acc[1], acc[0]]), 'out of order')
    refused(lambda: be.split(be.subtree(acc[:2]), words(3)), 'another width')
    print('projections of part of a subtree are refused')
    # a binding needs the one-signal convention
    vk2, _, _ = B.groth16_instance(2, seed=7)
    refused(lambda: Groth16(F.Fp(Sym(0)), vk2, depth=1), 'one public signal')
    # one binding at a time: by the tree, or by the first input
    refused(lambda: Groth16(F.Fp(Sym(0)), vk, depth=1, sighash_input=True), 'one binding')
    print('all ok')


if __name__ == '__main__':
    main()
