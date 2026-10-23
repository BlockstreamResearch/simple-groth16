"""Straight-line F_r code, written once and run two ways: on integers mod r (the prover's side, which
also records the inverse hints in order), and as a program (FrDag records the operations; `emit` lays
them out in the program, each value computed once and bound in the environment).

An inverse is a hint: the prover gives w = x^-1 and the program checks x w = 1.  Values are normalised
to 1.3 r when bound, so that any product of a few of them stays within the CRT bound.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Any

from .curve import Curve, chain
from .dsl import ensure
from .fp import Fp, Val

KBR_NUM, KBR_DEN = 13, 10  # bound of a bound value: 1.3 r


class FrInts:
    """The operations on integers mod q; `inv` records each inverse it computes (the hints)."""

    def __init__(self, q: int) -> None:
        self.q = q
        self.hints: list[int] = []
        self.checks: list[tuple[str, int]] = []

    def mul(self, a: int, b: int) -> int:
        return a * b % self.q

    def sqr(self, a: int) -> int:
        return a * a % self.q

    def dot(self, pairs: Sequence[tuple[int, int]]) -> int:
        return sum(a * b for a, b in pairs) % self.q

    def lin(self, terms: Sequence[tuple[int, int]], c0: int = 0) -> int:
        return (sum(a * k for a, k in terms) + c0) % self.q

    def mulc(self, a: int, k: int) -> int:
        return a * k % self.q

    def add(self, a: int, b: int) -> int:
        return (a + b) % self.q

    def sub(self, a: int, b: int) -> int:
        return (a - b) % self.q

    def inv(self, a: int) -> int:
        ensure(a % self.q != 0, 'inverse of 0')
        w = pow(a, -1, self.q)
        self.hints.append(w)
        return w

    def check_zero(self, label: str, terms: Sequence[tuple[int, int]], c0: int = 0) -> None:
        """sum k_i a_i + c0 = 0."""
        ensure(self.lin(terms, c0) == 0, f'check {label}')
        self.checks.append((label, 0))


class Node:
    __slots__ = ('op', 'args', 'k', 'name', 'level', 'last')

    def __init__(self, op: str, args: Sequence[Any], k: Any = None) -> None:
        self.op, self.args, self.k = op, list(args), k
        self.name = ''
        self.level: int = 1 + max((int(a.level) for a in self.args if isinstance(a, Node)), default=0)
        self.last: int = self.level


class FrDag:
    """The same operations, recorded: inputs and inverse hints are named leaves of level 0."""

    def __init__(self, inputs: dict[str, Val], hints: Sequence[Val]) -> None:
        self.nodes: list[Node] = []
        self.checks: list[Node] = []
        self.inputs: dict[str, Node] = {}
        for nm in inputs:
            self.inputs[nm] = self._leaf(nm)
        self.input_vals = dict(inputs)
        self.hint_vals = list(hints)
        self.n_hints = 0

    def _leaf(self, nm: str) -> Node:
        n = Node('in', [])
        n.level, n.last, n.name = 0, 0, nm
        return n

    def __getitem__(self, nm: str) -> Node:
        return self.inputs[nm]

    def _node(self, op: str, args: Sequence[Any], k: Any = None) -> Node:
        n = Node(op, args, k)
        n.name = f'v{len(self.nodes)}'
        self.nodes.append(n)
        return n

    def mul(self, a: Node, b: Node) -> Node:
        return self._node('dot', [a, b], [(0, 1)])

    def sqr(self, a: Node) -> Node:
        return self._node('dot', [a], [(0, 0)])

    def dot(self, pairs: Sequence[tuple[Node, Node]]) -> Node:
        args: list[Node] = []
        idx = []
        for a, b in pairs:
            ia = next((i for i, x in enumerate(args) if x is a), None)
            if ia is None:
                args.append(a)
                ia = len(args) - 1
            ib = next((i for i, x in enumerate(args) if x is b), None)
            if ib is None:
                args.append(b)
                ib = len(args) - 1
            idx.append((ia, ib))
        return self._node('dot', args, idx)

    def lin(self, terms: Sequence[tuple[Node, int]], c0: int = 0) -> Node:
        return self._node('lin', [a for a, _ in terms], ([k for _, k in terms], c0))

    def mulc(self, a: Node, k: int) -> Node:
        return self.lin([(a, k)])

    def add(self, a: Node, b: Node) -> Node:
        return self.lin([(a, 1), (b, 1)])

    def sub(self, a: Node, b: Node) -> Node:
        return self.lin([(a, 1), (b, -1)])

    def inv(self, a: Node) -> Node:
        """The next hint, with the check a w = 1."""
        h = self._leaf(f'hint{self.n_hints}')
        self.inputs[h.name] = h
        self.input_vals[h.name] = self.hint_vals[self.n_hints]
        self.n_hints += 1
        c = Node('check', [a, h], ('inv', 'inverse'))
        self.checks.append(c)
        return h

    def check_zero(self, label: str, terms: Sequence[tuple[Node, int]], c0: int = 0) -> None:
        self.checks.append(Node('check', [a for a, _ in terms], ('zero', label, [k for _, k in terms], c0)))

    # the program
    def emit(self, fr: Fp, outputs: Sequence[Node] = (), flatten: int = 6) -> Any:
        """The code: levels of values, each bound before the next level reads it; a check runs as soon as
        its arguments are bound.  Every `flatten` levels the live values are re-packed into a fresh
        environment (chain's let), otherwise pushed in front of it.  Returns the unit-typed checks (Sym) and
        the outputs' Vals are passed to `done`, which this returns: done(ctx, checks, outputs)."""
        cv = Curve(fr)
        for n in self.nodes + self.checks:
            for a in n.args:
                if isinstance(a, Node):
                    a.last = max(a.last, n.level)
        for o in outputs:
            o.last = 10**9
        top = max([n.level for n in self.nodes + self.checks], default=0)
        kb = fr.P * KBR_NUM // KBR_DEN

        def norm(v: Val) -> Val:
            return v if v.hi <= kb else fr.normalize(v)

        def value(n: Node, c: dict[str, Any]) -> Val:
            a = [c[x.name] for x in n.args]
            if n.op == 'dot':
                return norm(fr.reduce_dot([(a[i], a[j]) for i, j in n.k]))
            if n.op == 'lin':
                ks, c0 = n.k
                terms = list(zip(a, ks)) + ([(fr.const(1), c0)] if c0 else [])
                return norm(fr.lin_const(terms))
            raise ValueError(n.op)

        def check(n: Node, c: dict[str, Any]) -> Val:
            a = [c[x.name] for x in n.args]
            if n.k[0] == 'inv':
                return cv.zero_check(fr.reduce_dot([(a[0], a[1]), (fr.const(1), fr.const(fr.P - 1))]))
            _, _label, ks, c0 = n.k
            terms = list(zip(a, ks)) + ([(fr.const(1), c0)] if c0 else [])
            return cv.zero_check(fr.lin_const(terms))

        def check_step(ch: Node) -> tuple:
            return ('check', lambda c: check(ch, c))

        def values(here: list[Node]) -> Any:
            return lambda c: [value(n, c) for n in here]

        steps: list[tuple] = []
        for lvl in range(1, top + 1):
            steps += [check_step(ch) for ch in self.checks if ch.level == lvl]
            here = [n for n in self.nodes if n.level == lvl]
            if here:
                names = [n.name for n in here]
                if lvl % flatten == 0:
                    dead = [x.name for x in list(self.inputs.values()) + self.nodes if x.level < lvl and x.last < lvl]
                    steps.append(('let', names, values(here), dead))
                else:
                    steps.append(('push', names, values(here)))
        steps += [check_step(ch) for ch in self.checks if ch.level > top]
        return steps

    def run(self, fr: Fp, outputs: Sequence[Node], done: Callable[[dict[str, Any], list[Val], list[Val]], Any]) -> Any:
        """emit, then chain over the inputs: done(ctx, checks, output Vals)."""
        steps = self.emit(fr, outputs)
        return chain(fr, dict(self.input_vals), steps, lambda c, checks: done(c, checks, [c[o.name] for o in outputs]))
