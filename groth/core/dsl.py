"""Small helpers: Simplicity's human-readable encoding, balanced trees, witness files, checks.

A program is a list of definitions `name := expression`, one of them `main`.  An expression acts on its
environment (its input value): `iden` is the whole environment, `take` / `drop` its left / right half,
`comp s t` feeds the output of s into t.  A path over {O, I} ending in H names a component of the
environment, as in the Simplicity papers: 'OIH' = take (drop iden).

Tuples are packed as balanced trees of pairs; long sums are added level by level.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Iterable, Sequence
from typing import Any, TypeVar

T = TypeVar('T')
WSpec = dict[str, Any]  # a witness value spec of tools/harness: {'w': hex} or {'p': [spec, spec]}


class CheckFailed(AssertionError):
    """A static bound, a numeric-model check or a check on an input (a snarkjs file, a proof, a witness)
    failed; the tools report it as a refusal."""


def ensure(cond: object, msg: str = 'check failed') -> None:
    """Like `assert`, but also active under `python -O`: the static bounds are what make the generated
    program sound, so they must never be skipped."""
    if not cond:
        raise CheckFailed(msg)


def balanced(items: Sequence[T], pair_fn: Callable[[T, T], T]) -> T:
    """Balanced binary tree of items; the left half gets ceil(n/2) items."""
    if len(items) == 1:
        return items[0]
    h = (len(items) + 1) // 2
    return pair_fn(balanced(items[:h], pair_fn), balanced(items[h:], pair_fn))


def balanced_paths(n: int, prefix: str = '') -> list[str]:
    """Paths (O/I letters + H) of the n leaves of a balanced tree, in order."""
    if n == 1:
        return [prefix + 'H']
    h = (n + 1) // 2
    return balanced_paths(h, prefix + 'O') + balanced_paths(n - h, prefix + 'I')


def pairwise_sum(items: Iterable[T], add: Callable[[T, T], T]) -> T:
    """Sum level by level: neighbours are added, an odd last item is carried up."""
    items = list(items)
    while len(items) > 1:
        nxt = [add(items[i], items[i + 1]) for i in range(0, len(items) - 1, 2)]
        if len(items) % 2:
            nxt.append(items[-1])
        items = nxt
    return items[0]


def Tbalanced(types: Iterable[str]) -> str:
    """Type of a balanced tree of the given types."""
    return balanced(list(types), lambda a, b: f'({a} * {b})')


def Tpairs(*types: str) -> str:
    """Right-nested product type."""
    e = types[-1]
    for t in reversed(types[:-1]):
        e = f'({t} * {e})'
    return e


class Emitter:
    """The definitions of a program, in dependency order."""

    def __init__(self) -> None:
        self.defs: list[tuple[str, str, str | None]] = []  # (name, expression, type or None)
        self.names: dict[str, str] = {}  # sharing key -> name
        self.counter = 0

    def define(self, name: str, expr: str, ty: str | None = None) -> str:
        self.defs.append((name, expr, ty))
        return name

    def share(self, key: str, expr: str, prefix: str = 'n') -> str:
        """Name of `expr`, defined on first use.  Equal keys share one DAG node."""
        if key in self.names:
            return self.names[key]
        self.counter += 1
        name = f'{prefix}{self.counter}'
        self.names[key] = name
        self.defs.append((name, expr, None))
        return name

    def tree_uses(self, root: str = 'main') -> dict[str, int]:
        """How often each definition occurs in the tree unfolding of `root` (the DAG's sharing undone).
        A spender may unshare a node, so a witness node that occurs twice could be given two values."""
        defined = {name for name, _, _ in self.defs}
        refs = {name: [t for t in _NAME.findall(expr) if t in defined] for name, expr, _ in self.defs}
        order: list[str] = []  # post-order from root
        seen = {root}
        stack = [(root, iter(refs[root]))]
        while stack:
            name, it = stack[-1]
            child = next(it, None)
            if child is None:
                order.append(name)
                stack.pop()
            elif child not in seen:
                seen.add(child)
                stack.append((child, iter(refs[child])))
        uses = dict.fromkeys(order, 0)
        uses[root] = 1
        for name in reversed(order):  # parents before children
            for child in refs[name]:
                uses[child] += uses[name]
        return uses

    def text(self) -> str:
        """The definitions, with the constants last and atoms without parentheses.  The parser of
        rust-simplicity 0.9 finds the line and column of each token by scanning the text from its start,
        so it takes time (tokens) x (text before them); the long constant literals at the end and fewer
        tokens make it several times faster.  Definitions may refer to later ones."""
        out: list[str] = []
        consts: list[str] = []
        for name, expr, ty in self.defs:
            expr = _ATOM.sub(r'\1', expr)
            line = f'{name} := {expr} : {ty}' if ty else f'{name} := {expr}'
            (consts if ty is None and _CONST.match(name) else out).append(line)
        return '\n'.join(out + consts) + '\n'


_NAME = re.compile(r'[A-Za-z_]\w*')
_ATOM = re.compile(r'\((iden|unit|[nk]\d+|jet_\w+|[A-Z][A-Z_0-9]*)\)')
_CONST = re.compile(r'k\d+$')  # Sym.const's names


# Witness values in the JSON format of tools/harness (see src/witness.rs).
def wv(bits: int, v: int) -> WSpec:
    ensure(0 <= v < 1 << bits, f'a {bits}-bit witness word out of range')
    return {'w': f'{v:0{bits // 4}x}'}


def wpair(a: WSpec, b: WSpec) -> WSpec:
    return {'p': [a, b]}


def wpairs(*xs: WSpec) -> WSpec:
    """Right-nested pair."""
    e = xs[-1]
    for x in reversed(xs[:-1]):
        e = wpair(x, e)
    return e


def wbalanced(xs: Iterable[WSpec]) -> WSpec:
    return balanced(list(xs), wpair)
