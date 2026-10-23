"""The two backends every generator is written against.

`Sym` builds Simplicity expressions together with their exact static cost; `Num` computes the same
thing on integers.  A generator calls the same methods on either one, so one piece of Python both
writes the program and models it word for word; the tests compare the two.

Costs follow rust-simplicity 0.9 (src/analysis.rs), in milliweight units (mWU):

    iden: 100 + width(env)          unit: 100          take, drop, injl, injr: 100 + child
    comp s t: 100 + width(mid) + s + t                 pair s t: 100 + s + t
    case s t: 100 + max(s, t)       witness: 100 + width
    jet: 100 + jet cost             const: 100 + width (300 + width as `comp unit (const w)`)

The cost of a DAG is the cost of its tree unfolding: a shared node used twice runs twice.  Sharing only
saves program bytes; a value needed twice must be bound into the environment (`let`, `scope`), and
every copy of the environment costs its width, so environments are kept small.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Any

from .dsl import CheckFailed, Emitter, balanced, balanced_paths, ensure, pairwise_sum

# jet costs (mWU), as in rust-simplicity 0.9 and Elements 23.3; add a jet here before using it
JET_COST = {
    'fe_multiply': 808,
    'fe_square': 556,
    'fe_add': 755,
    'fe_negate': 531,
    'scalar_multiply': 774,
    'scalar_square': 575,
    'scalar_add': 739,
    'scalar_negate': 490,
    'eq_256': 225,
    'eq_64': 100,
    'lt_64': 76,
    'and_1': 79,
    'or_1': 77,
    'complement_1': 79,
    'and_8': 91,
    'verify': 57,
    'sha_256_iv': 93,
    'sha_256_block': 771,
    'sha_256_ctx_8_init': 118,
    'sha_256_ctx_8_add_512': 5299,
    'sha_256_ctx_8_add_1': 642,
    'sha_256_ctx_8_add_32': 896,
    'sha_256_ctx_8_add_64': 1187,
    'sha_256_ctx_8_add_128': 1779,
    'sha_256_ctx_8_add_256': 2912,
    'sha_256_ctx_8_finalize': 835,
    'sig_all_hash': 133,
}
SHA_CTX_W = 830  # width of the SHA-256 context type (buffer, counter, midstate)

# The generators are written against either backend, Sym or Num, which have the same methods; their values
# are E's on Sym and ints (or nested lists of them, for pairs) on Num.
Backend = Any
Term = Any  # a backend value
Shape = Any  # an E (its width) or a nested list of shapes: the structure of an environment


class E:
    """An expression: text, output width in bits, tree cost in mWU.  `path` (O/I letters) is set when the
    expression is a plain projection of the environment, so that its components can be read directly."""

    __slots__ = ('t', 'w', 'c', 'path')

    def __init__(self, t: str, w: int, c: int, path: str | None = None) -> None:
        self.t, self.w, self.c, self.path = t, w, c, path

    def __repr__(self) -> str:
        return f'E({self.t[:40]!r}, w={self.w}, c={self.c})'


def words(n: int) -> list[E]:
    """Shape of n 256-bit words (for function, with_env, split)."""
    return [E('', 256, 0) for _ in range(n)]


def flat(v: Any) -> list[Any]:
    """Leaves of a nested list."""
    return [v] if not isinstance(v, (list, tuple)) else [x for y in v for x in flat(y)]


def is_sym(be: Backend) -> bool:
    return isinstance(be, Sym)


class Sym:
    """Builds E's over the current environment, kept as a stack of widths (changed by let/scope)."""

    def __init__(self, env_width: int, em: Emitter | None = None) -> None:
        self.em = em or Emitter()
        self.env = [env_width]
        self.env_ids = [0]  # a named node has one type, so texts are only shared within one environment
        self.next_env_id = 1
        self.fns: dict[str, E] = {}  # functions defined once per program, by name (curve.digit_fn, curve.bits_fn)

    # sharing and environments
    def share(self, e: E, prefix: str = 'n') -> E:
        """The named node of e (one per text and environment)."""
        return E(self.em.share(f'{self.env_ids[-1]}|{e.t}', e.t, prefix), e.w, e.c)

    def _push_env(self, width: int) -> None:
        self.env.append(width)
        self.env_ids.append(self.next_env_id)
        self.next_env_id += 1

    def _pop_env(self) -> None:
        self.env.pop()
        self.env_ids.pop()

    def define(self, name: str, e: E, ty: str | None = None) -> E:
        self.em.define(name, e.t, ty)
        return E(name, e.w, e.c)

    # core combinators
    def iden(self) -> E:
        w = self.env[-1]
        return E('iden', w, 100 + w)

    def unit(self) -> E:
        return E('unit', 0, 100)

    def proj(self, path: str, width: int) -> E:
        """The `width`-bit component of the environment at `path` (O/I letters, ending in H)."""
        assert path.endswith('H')
        t = 'iden'
        for ch in reversed(path[:-1]):
            t = ('take ' if ch == 'O' else 'drop ') + '(' + t + ')'
        return E(t, width, 100 * (len(path) - 1) + 100 + width, path[:-1])

    def sub(self, e: E, subpath: str, width: int) -> E:
        """A component of a projected value (the paths are concatenated, no comp)."""
        assert e.path is not None, 'sub-projection of a computed value'
        return self.proj(e.path + subpath + 'H', width)

    def bit(self, e: E, i: int) -> E:
        """Bit i (0 = least significant) of a projected 256-bit word, as a value of type 2."""
        assert e.w == 256
        return self.sub(e, ''.join('O' if (255 - i) >> (7 - k) & 1 == 0 else 'I' for k in range(8)), 1)

    def drop(self, e: E) -> E:
        return E(f'drop ({e.t})', e.w, 100 + e.c, None if e.path is None else 'I' + e.path)

    def pair(self, a: E, b: E) -> E:
        return E(f'pair ({a.t}) ({b.t})', a.w + b.w, 100 + a.c + b.c)

    def pairs(self, *xs: E) -> E:
        """Right-nested pairs."""
        e = xs[-1]
        for x in reversed(xs[:-1]):
            e = self.pair(x, e)
        return e

    def comp(self, s: E, t: E) -> E:
        return E(f'comp ({s.t}) ({t.t})', t.w, 100 + s.w + s.c + t.c)

    def injl(self, e: E, w: int) -> E:
        """The left injection into a sum type of width w (1 + the wider side)."""
        return E(f'injl ({e.t})', w, 100 + e.c)

    def injr(self, e: E, w: int) -> E:
        return E(f'injr ({e.t})', w, 100 + e.c)

    def case(self, l: E, r: E) -> E:
        assert l.w == r.w
        return E(f'case ({l.t}) ({r.t})', l.w, 100 + max(l.c, r.c))

    def witness(self, name: str, ty: str, width: int) -> E:
        """A witness node of its own, `name := witness : _ -> ty`: its value is read where the node is, so
        it need not be carried there through the environment."""
        self.em.define(name, 'witness', f'_ -> {ty}')
        return E(name, width, 100 + width)

    def const(self, bits: int, v: int) -> E:
        lit = f'0x{v:0{bits // 4}x}' if bits % 4 == 0 else f'0b{v:0{bits}b}'
        return self.share(E(f'comp unit (const {lit})', bits, 300 + bits), 'k')

    def words_const(self, values: Sequence[int], bits: int = 256) -> E:
        """Constant words as a balanced tree.  A power-of-two number of them is one wide constant: the same
        type and value as the tree of words, in one program node instead of 2n - 1."""
        n = len(values)
        if n & (n - 1) == 0:
            v = 0
            for x in values:
                v = (v << bits) | x
            return self.const(bits * n, v)
        return self.pack([self.const(bits, x) for x in values])

    def consts(self, bits: int, groups: Sequence[Sequence[int]]) -> E:
        """comp unit (groups of constant words, as a balanced tree of words_const).  They are created in an
        environment of their own: under comp unit their source type is 1, so they must not share a node
        with the same constant used elsewhere."""
        self._push_env(0)
        try:
            packed = self.pack([self.words_const(g, bits) for g in groups])
        finally:
            self._pop_env()
        return self.comp(self.unit(), packed)

    def jet(self, name: str, arg: E, out_w: int) -> E:
        """comp arg jet_name"""
        return self.share(E(f'comp ({arg.t}) (jet_{name})', out_w, 100 + arg.w + arg.c + 100 + JET_COST[name]))

    def jet_at(self, name: str, path: str, out_w: int) -> E:
        """A jet applied in place to the component of the environment at `path` (O/I letters): the jet
        node is wrapped in take/drop, so its operands are neither copied nor passed through a comp."""
        t = f'jet_{name}'
        for ch in reversed(path):
            t = ('take ' if ch == 'O' else 'drop ') + '(' + t + ')'
        return E(t, out_w, 100 * len(path) + 100 + JET_COST[name])

    def with_env(self, e: E, shape: Shape, body: Callable[[Any], E]) -> E:
        """comp e body: body(accessors) runs in the environment produced by e, structured like `shape`."""
        self._push_env(e.w)
        try:
            accs = self._unpack('', shape)
            res = body(accs)
        finally:
            self._pop_env()
        return self.comp(e, res)

    def crt_dot(self, pairs: Sequence[tuple[E, E | None]]) -> E:
        """Sum of products of (a, b) operand pairs in CRT form, as one 512-bit E (S mod p_s, S mod n_s).
        The pairs are packed into a balanced tree, so each operand is read once; both multiplication jets
        are then applied to every leaf in place (jet_at) and summed per modulus.  A pair (a, None) is a
        square and uses the squaring jets."""
        tree = self.pack([a if b is None else self.pair(a, b) for a, b in pairs])
        paths = balanced_paths(len(pairs))
        self._push_env(tree.w)  # the sums live in the environment of the pair tree
        try:
            fe = pairwise_sum(
                [
                    self.jet_at('fe_square' if b is None else 'fe_multiply', p[:-1], 256)
                    for p, (a, b) in zip(paths, pairs)
                ],
                self.fe_add,
            )
            sc = pairwise_sum(
                [
                    self.jet_at('scalar_square' if b is None else 'scalar_multiply', p[:-1], 256)
                    for p, (a, b) in zip(paths, pairs)
                ],
                self.sc_add,
            )
        finally:
            self._pop_env()
        return self.comp(tree, self.pair(fe, sc))

    # 256-bit jets: the interface fp.py uses
    def fe_mul(self, a: E, b: E) -> E:
        return self.jet('fe_multiply', self.pair(a, b), 256)

    def fe_sqr(self, a: E) -> E:
        return self.jet('fe_square', a, 256)

    def fe_add(self, a: E, b: E) -> E:
        return self.jet('fe_add', self.pair(a, b), 256)

    def fe_neg(self, a: E) -> E:
        return self.jet('fe_negate', a, 256)

    def sc_mul(self, a: E, b: E) -> E:
        return self.jet('scalar_multiply', self.pair(a, b), 256)

    def sc_sqr(self, a: E) -> E:
        return self.jet('scalar_square', a, 256)

    def sc_add(self, a: E, b: E) -> E:
        return self.jet('scalar_add', self.pair(a, b), 256)

    def sc_neg(self, a: E) -> E:
        return self.jet('scalar_negate', a, 256)

    def word(self, v: int) -> E:
        return self.const(256, v)

    def eq256(self, a: E, b: E) -> E:
        return self.jet('eq_256', self.pair(a, b), 1)

    def or1(self, a: E, b: E) -> E:
        return self.jet('or_1', self.pair(a, b), 1)

    def and1(self, a: E, b: E) -> E:
        return self.jet('and_1', self.pair(a, b), 1)

    def not1(self, a: E) -> E:
        return self.jet('complement_1', a, 1)

    def verify(self, bit: E) -> E:
        return self.jet('verify', bit, 0)

    def lt64(self, a: E, b: E) -> E:
        return self.jet('lt_64', self.pair(a, b), 1)

    def eq64(self, a: E, b: E) -> E:
        return self.jet('eq_64', self.pair(a, b), 1)

    def checks(self, units: Sequence[E]) -> E:
        """Several unit-typed checks as one unit-typed expression."""
        return self.comp(self.pairs(*units), self.unit())

    def check(self, e: E, hi: int) -> E:
        """A bound assertion: only the numeric backend checks it."""
        return e

    # Environments.  A value passed to let/scope is an E or a nested list of values (packed as a
    # balanced pair tree); the body gets accessors (projections) with the same nesting.
    def pack(self, v: Any) -> E:
        """An E stays an E; a nested list becomes the balanced pair tree of its packed items, or, when its
        leaves are exactly the leaves of one subtree of the environment, a projection of that subtree."""
        if isinstance(v, E):
            return v
        sub = self._as_subtree(v)
        if sub is not None:
            return sub
        return balanced([self.pack(x) for x in v], self.pair)

    def _as_subtree(self, v: Any) -> E | None:
        leaves = flat(v)
        if len(leaves) < 2 or any(e.path is None for e in leaves):
            return None
        pre = leaves[0].path
        for a in leaves[1:]:
            while not a.path.startswith(pre):
                pre = pre[:-1]
        expected = flat(self._unpack(pre, v))  # the leaves a subtree at pre, shaped like v, would have
        if [e.path for e in expected] != [e.path for e in leaves]:
            return None
        return self.proj(pre + 'H', sum(e.w for e in leaves))

    def _unpack(self, prefix: str, v: Shape) -> Any:
        """Accessors for the value v placed at path prefix."""
        if isinstance(v, E):
            return self.proj(prefix + 'H', v.w)
        paths = balanced_paths(len(v), prefix)
        return [self._unpack(pth[:-1], x) for pth, x in zip(paths, v)]

    def let(self, vals: Any, body: Callable[[Any, Callable[[E], E]], E]) -> E:
        """Evaluate vals, then run body(accessors, lift) in the environment (vals, old env).  lift(e)
        re-expresses an E of the old environment (cost 100 + e)."""
        packed = self.pack(vals)
        outer = self.iden()
        self._push_env(packed.w + self.env[-1])
        try:
            accs = self._unpack('O', vals)
            res = body(accs, self.drop)
        finally:
            self._pop_env()
        return self.comp(self.pair(packed, outer), res)

    def scope(self, vals: Any, body: Callable[[Any], E]) -> E:
        """Evaluate vals, then run body(accessors) in an environment holding only them."""
        packed = self.pack(vals)
        self._push_env(packed.w)
        try:
            accs = self._unpack('', vals)
            res = body(accs)
        finally:
            self._pop_env()
        return self.comp(packed, res)

    def once(self, es: Sequence[E], body: Callable[[Sequence[E]], Any]) -> Any:
        """body(es) with every computed expression of es evaluated once into a scope (projections and
        constants are passed as they are; with none computed, body is called directly).  body may return
        an E or a tuple of E's; a tuple is packed and each component projected out, which evaluates the
        scope once per component."""
        computed = [e for e in es if e.path is None and not e.t.startswith('k')]
        if not computed:
            return body(es)
        results: dict[str, list[E]] = {}

        def inner(accs):
            res = body(accs)
            if isinstance(res, tuple):
                results['parts'] = list(res)
                return self.pack(list(res))
            return res

        whole = self.scope(list(es), inner)
        if 'parts' not in results:
            return whole
        parts = results['parts']
        out = []
        for pth, part in zip(balanced_paths(len(parts)), parts):
            self._push_env(whole.w)
            try:
                acc = self.proj(pth, part.w)
            finally:
                self._pop_env()
            out.append(self.comp(whole, acc))
        return tuple(out)

    def call(self, fn: E, args: Any) -> E:
        """Apply a named function (an E whose text is its name) to args."""
        return self.comp(self.pack(args), fn)

    def function(self, name: str, shape: Shape, body: Callable[[Any], E]) -> E:
        """Define a named function over an environment structured like `shape` (E's of the right widths);
        body(accessors) -> E."""
        packed = self.pack(shape)
        self._push_env(packed.w)
        try:
            accs = self._unpack('', shape)
            res = body(accs)
        finally:
            self._pop_env()
        return self.define(name, res)

    def split(self, e: E, shape: Shape) -> Any:
        """Accessors, nested like `shape`, for the components of a projected value."""
        if e.path is None:
            raise CheckFailed('split of a computed value')
        ensure(sum(x.w for x in flat(shape)) == e.w, 'split into components of another width')
        return self._unpack(e.path, shape)

    def subtree(self, leaves: Any) -> E:
        """Projection of the smallest subtree holding the (nested) projected leaves, which must be all of
        its leaves, in order."""
        leaves = flat(leaves)
        ensure(all(a.path is not None for a in leaves), 'subtree of a computed value')
        pre = leaves[0].path
        for a in leaves[1:]:
            while not a.path.startswith(pre):
                pre = pre[:-1]
        paths = [a.path for a in leaves]
        ensure(len(paths) == len(set(paths)) and _partition(pre, set(paths)), 'not a whole subtree')
        # in the subtree's order (O before I), as the numeric backend takes them
        ensure(paths == sorted(paths, key=lambda p: p.replace('O', '0').replace('I', '1')), 'leaves out of order')
        return self.proj(pre + 'H', sum(a.w for a in leaves))

    def seq(self, chk: E, e: E) -> E:
        """Run a unit-typed check, then return e: comp (pair chk e) (drop iden)."""
        return self.comp(self.pair(chk, e), E('drop (iden)', e.w, 200 + e.w))


def _partition(pre: str, paths: set[str]) -> bool:
    """The paths are exactly the leaves of a subtree at pre: pre itself, or a partition of both halves."""
    if pre in paths:
        return not any(p != pre and p.startswith(pre) for p in paths)
    if not any(p.startswith(pre) for p in paths):
        return False
    return _partition(pre + 'O', paths) and _partition(pre + 'I', paths)


class Num:
    """The numeric backend: values are ints (256-bit words), nested lists stand for pairs, and the
    environment operations pass values through."""

    P_SECP = 2**256 - 2**32 - 977
    N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

    # the jets reduce any 256-bit input modulo their prime, as the C implementation does
    def fe_mul(self, a: int, b: int) -> int:
        return a * b % self.P_SECP

    def fe_sqr(self, a: int) -> int:
        return a * a % self.P_SECP

    def fe_add(self, a: int, b: int) -> int:
        return (a + b) % self.P_SECP

    def fe_neg(self, a: int) -> int:
        return (-a) % self.P_SECP

    def sc_mul(self, a: int, b: int) -> int:
        return a * b % self.N_SECP

    def sc_sqr(self, a: int) -> int:
        return a * a % self.N_SECP

    def sc_add(self, a: int, b: int) -> int:
        return (a + b) % self.N_SECP

    def sc_neg(self, a: int) -> int:
        return (-a) % self.N_SECP

    def word(self, v: int) -> int:
        return v

    def eq256(self, a: int, b: int) -> int:
        return int(a == b)

    def or1(self, a: int, b: int) -> int:
        return a | b

    def and1(self, a: int, b: int) -> int:
        return a & b

    def not1(self, a: int) -> int:
        return 1 - a

    def lt64(self, a: int, b: int) -> int:
        return int(a < b)

    def eq64(self, a: int, b: int) -> int:
        return int(a == b)

    def verify(self, bit: int) -> int:
        ensure(bit == 1, 'verify failed')
        return 0

    def checks(self, units: Sequence[int]) -> int:
        return 0

    def pair(self, a: Any, b: Any) -> tuple[Any, Any]:
        return (a, b)

    def check(self, v: int, hi: int) -> int:
        ensure(0 <= v <= hi, f'value {v} exceeds bound {hi}')
        return v

    def pack(self, v: Any) -> Any:
        return v

    def once(self, es: Sequence[Any], body: Callable[[Sequence[Any]], Any]) -> Any:
        return body(es)

    def bit(self, e: int, i: int) -> int:
        return (e >> i) & 1

    def sub(self, e: Any, path: str, w: int) -> Any:
        for ch in path:
            e = e[0] if ch == 'O' else e[1]
        return e

    def let(self, vals: Any, body: Callable[[Any, Callable[[Any], Any]], Any]) -> Any:
        return body(list(vals), lambda e: e)

    def scope(self, vals: Any, body: Callable[[Any], Any]) -> Any:
        return body(list(vals))

    def with_env(self, e: Any, shape: Shape, body: Callable[[Any], Any]) -> Any:
        return body(e)

    def function(self, name: str, shape: Shape, body: Callable[[Any], Any]) -> Callable[[Any], Any]:
        return body

    def call(self, fn: Callable[[Any], Any], args: Sequence[Any]) -> Any:
        return fn(args[0] if len(args) == 1 else list(args))  # a one-item pack is the item

    def split(self, e: Any, shape: Shape) -> Any:
        return e

    def subtree(self, leaves: Any) -> Any:
        return leaves

    def seq(self, chk: Any, e: Any) -> Any:
        return e

    def crt_dot(self, pairs: Sequence[tuple[int, int | None]]) -> list[int]:
        tot = sum(a * (a if b is None else b) for a, b in pairs)
        return [tot % self.P_SECP, tot % self.N_SECP]
