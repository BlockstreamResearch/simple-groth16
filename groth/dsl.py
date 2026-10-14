"""Small helpers: Simplicity's human-readable encoding, balanced trees, witness files, checks.

A program is a list of definitions `name := expression`, the last one `main`.  An expression acts on its
environment (its input value): `iden` is the whole environment, `take` / `drop` its left / right half,
`comp s t` feeds the output of s into t.  A path over {O, I} ending in H names a component of the
environment, as in the Simplicity papers: 'OIH' = take (drop iden).

Tuples are packed as balanced trees of pairs; long sums are added level by level.
"""


class CheckFailed(AssertionError):
    """A static bound or a numeric-model check failed."""


def ensure(cond, msg='check failed'):
    """Like `assert`, but also active under `python -O`: the static bounds are what make the generated
    program sound, so they must never be skipped."""
    if not cond:
        raise CheckFailed(msg)


def balanced(items, pair_fn):
    """Balanced binary tree of items; the left half gets ceil(n/2) items."""
    if len(items) == 1:
        return items[0]
    h = (len(items) + 1) // 2
    return pair_fn(balanced(items[:h], pair_fn), balanced(items[h:], pair_fn))


def balanced_paths(n, prefix=''):
    """Paths (O/I letters + H) of the n leaves of a balanced tree, in order."""
    if n == 1:
        return [prefix + 'H']
    h = (n + 1) // 2
    return balanced_paths(h, prefix + 'O') + balanced_paths(n - h, prefix + 'I')


def pairwise_sum(items, add):
    """Sum level by level: neighbours are added, an odd last item is carried up."""
    items = list(items)
    while len(items) > 1:
        nxt = [add(items[i], items[i + 1]) for i in range(0, len(items) - 1, 2)]
        if len(items) % 2:
            nxt.append(items[-1])
        items = nxt
    return items[0]


def Tbalanced(types):
    """Type of a balanced tree of the given types."""
    return balanced(list(types), lambda a, b: f'({a} * {b})')


def Tpairs(*types):
    """Right-nested product type."""
    e = types[-1]
    for t in reversed(types[:-1]):
        e = f'({t} * {e})'
    return e


class Emitter:
    """The definitions of a program, in dependency order."""

    def __init__(self):
        self.defs = [] # (name, expression, type or None)
        self.names = {} # sharing key -> name
        self.counter = 0

    def define(self, name, expr, ty=None):
        self.defs.append((name, expr, ty))
        return name

    def share(self, key, expr, prefix='n'):
        """Name of `expr`, defined on first use.  Equal keys share one DAG node."""
        if key in self.names:
            return self.names[key]
        self.counter += 1
        name = f'{prefix}{self.counter}'
        self.names[key] = name
        self.defs.append((name, expr, None))
        return name

    def text(self):
        out = []
        for name, expr, ty in self.defs:
            out.append(f'{name} := {expr} : {ty}' if ty else f'{name} := {expr}')
        return '\n'.join(out) + '\n'


# Witness values in the JSON format of tools/harness (see src/witness.rs).
def wv(bits, v):
    return {'w': f'{v:0{bits // 4}x}'}


def wbit(b):
    return {'bit': b}


def wpair(a, b):
    return {'p': [a, b]}


def wpairs(*xs):
    """Right-nested pair."""
    e = xs[-1]
    for x in reversed(xs[:-1]):
        e = wpair(x, e)
    return e


def wbalanced(xs):
    return balanced(list(xs), wpair)
