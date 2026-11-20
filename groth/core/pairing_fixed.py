"""The pairing check e(P1, Q1) e(P2, Q2) e0 = 1 for two fixed points Q1, Q2 of G2 and a fixed e0 of GT, as
pairing.py's polynomial identity.  It is the pairing check of a KZG opening (fflonk, PLONK): the proof has
points of G1 only, and both points of G2 belong to the key.

pairing.py takes its first point of G2 from the proof (Groth16's B).  Its prover commits B's slope at
each of the 88 steps, and its identity has a relation for each slope and two for the point the loop ends
at.  Here both points are constants, and so are their lines: (c3, c4) of bn254's affine steps, 4 words
for each point at each step, written in the program.  The witness has no slopes and the loop state no
point.  What is left are the relations of the Miller values, with u = E(f) = N / D, c' = E(c) and l the
product of the two lines at P1 and P2, as in pairing.py:

    doubling     N' = N^2 conj(l),  D' = D^2 l
    addition     N' = N g_N conj(l),  D' = D g_D l       g = E(c^-1) at A+, E(c) at A-, 1 at F1 and F2
    committed    N' (a - w) - D' (a + w),  then N, D = a + w, a - w
    at the end   u pi(c'^-1) pi^2(c') pi^3(c'^-1) - tau as a fraction

Each of them is an odd polynomial, so S = sum rho^j R_j is odd, Q = S / M = w Q'(w^2), and the program
checks S(z) = z Q'(z^2) M(z).  e0 is given as an element t0 of F_p12 with e0 = t0^h, h = (p^12 - 1) / r,
and tau is E(t0)^-1: the relations show (m(P1, Q1) m(P2, Q2) t0)^h = 1 for the Miller values m.  For
fflonk, t0 is the Miller value of (-C0, [1]_2).  t0 must not lie in F_p6, where E(t0) = 1 has no
compressed form; a Miller value does not, but for a negligible part of the points.

A line of a fixed point is yP + c3 xP w + c4 w^3 with c3, c4 in F_p2: degree 9, where the line of B has
degree 21.  The relations are shorter for it, so more steps go between two committed values under one
degree cap, and here an addition may be left uncommitted as well (`schedule`).

Soundness is pairing.py's, with fewer relations.  rho is the SHA-256 of the two points and everything
committed (a_c and the committed values), z the SHA-256 of rho and Q'.  If a relation is not 0 modulo M,
S is not 0 modulo M except for at most N_RELS - 1 values of rho, and S - w Q'(w^2) M is then a nonzero
polynomial of degree at most max(deg S, 2 n_Q + 11), which vanishes at z with probability at most that
degree over p.  The lines need no relation: they are constants of the program, and
tests/test_pairing_fixed.py compares the product they give with bn254's Miller loop.

`relations` is written once over an abstract ring, as in pairing.py: the prover runs it on polynomials,
the tests on numbers.
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from typing import Any

from . import bn254, poly
from . import pairing as PC
from .curve import Curve, chain
from .dsl import Tbalanced, WSpec, ensure, wbalanced, wpair, wv
from .fp import WORD_MAX, Fp, P, Val, from_mont, to_mont
from .pairing import F_HI, KB, N_STEPS, STEPS, Ring
from .sym import SHA_CTX_W, E, Num, Shape, Term, flat, is_sym, words

Lines = Sequence[Sequence[tuple[bn254.Fp2, bn254.Fp2]]]  # fixed_lines of Q1 and of Q2


# ---------------------------------------------------------------------------------------------------
# The relations, over a ring
def relations(R: Ring, v: dict[str, Any], lines: Lines, commit: Sequence[bool] | None = None) -> list[Any]:
    """The relations in order, over the ring R (pairing.py's PolyRing, NumRing or DegRing).  v: the values
    (Prover.witness(...)['values']): the points P1, P2, a_c, the committed values a and the end's
    constant tau; lines: pairing.fixed_lines of Q1 and of Q2; commit: the steps whose Miller value is
    committed (COMMIT).  u = E(f) is kept as a fraction N / D with D(w) = N(-w), as in pairing.relations,
    and every relation is an odd polynomial."""
    commit = COMMIT if commit is None else commit
    X = R.X
    X3 = R.mul(R.mul(X, X), X)
    U = R.sub(R.mul(X3, X3), R.k(9))  # u = w^6 - 9

    def phi(a):  # an F_p2 element as a polynomial
        return R.add(R.k(a.c0), R.mul(R.k(a.c1), U))

    ac = R.even(v['ac'])
    cp, cm = R.add(ac, X), R.sub(ac, X)  # c' = E(c) = cp / cm
    N, D = cm, cp  # u = E(c^-1) = cm / cp
    rels = []
    for i, kind in enumerate(STEPS):
        if kind == 'D':
            N, D = R.mul(N, N), R.mul(D, D)
        elif kind in ('A+', 'A-'):  # times E(c^-1) or E(c)
            N, D = (R.mul(N, cm), R.mul(D, cp)) if kind == 'A+' else (R.mul(N, cp), R.mul(D, cm))
        for (xp, yp), ln in zip(v['P'], lines, strict=True):
            c3, c4 = ln[i]
            o = R.add(R.mul(R.mul(R.k(xp), X), phi(c3)), R.mul(X3, phi(c4)))  # the line is yP + o, o odd
            N, D = R.mul(N, R.sub(R.k(yp), o)), R.mul(D, R.add(R.k(yp), o))  # E(l) = conj(l) / l
        if commit[i]:
            a = R.even(v['a'][i])
            rels.append(R.conj_sub(R.mul(N, R.sub(a, X)), R.mul(D, R.add(a, X))))
            N, D = R.add(a, X), R.sub(a, X)
    rels.append(PC.last_relation(R, v, N, D))
    return rels


def combine(R: Ring, rels: Sequence[Any], r: int) -> Any:
    """S = sum r^j R_j by Horner's rule, the first relation with the highest power: what the program
    accumulates.  Every relation is odd, and S with them."""
    acc = R.k(0)
    for rel in rels:
        acc = R.add(R.mul(acc, R.k(r)), rel)
    return acc


def _degrees(commit: Sequence[bool]) -> list[int]:
    """The degrees of the relations (DegRing reads only the structure)."""
    z = bn254.Fp2(0)
    v = {'P': [(0, 0)] * 2, 'ac': [0] * 6, 'a': [[0] * 6] * N_STEPS, 'tau': [0] * 6}
    return [max(d) for d in relations(PC.DegRing, v, [[(z, z)] * N_STEPS] * 2, commit)]


def schedule(cap: int) -> list[bool]:
    """The steps whose Miller value is committed: left to right, a step is left out whenever every relation
    stays within the degree cap, so each relation carries as many steps as fit."""
    commit = [True] * N_STEPS
    for i in range(N_STEPS):
        commit[i] = False
        if max(_degrees(commit)) > cap:
            commit[i] = True
    return commit


# Under this cap a relation carries up to four steps, three doublings and an addition, and 23 of the 88
# Miller values are committed.  The cap is higher than pairing.py's because a committed value costs the
# program about as much as ten words of Q.  For each size of Q from 80 to 240 words, `schedule` gives the
# fewest committed values it allows, and this size, 136 words, has the lowest cost: 80 words need 33
# values, 160 words still 22.  Up to this size the committed values and Q together take 272 to 282 words.
DEG_CAP = 283
COMMIT = schedule(DEG_CAP)
N_RELS = sum(COMMIT) + 1
DEG_S = max(_degrees(COMMIT))
N_Q = PC.q_words(DEG_S)  # the words of Q'


def spans() -> list[list[int]]:
    """The steps in spans: each ends with the next committed value, the last with the loop."""
    out: list[list[int]] = [[]]
    for k in range(N_STEPS):
        out[-1].append(k)
        if COMMIT[k] and k + 1 < N_STEPS:
            out.append([])
    return out


# ---------------------------------------------------------------------------------------------------
# The prover.  The transcript: r = SHA-256(points, a_c, committed values), z = SHA-256(r, Q'), all words
# big-endian
class Prover:
    """The witness for the points P1, P2 of G1, for the fixed points q1, q2 of G2 and the constant `const`
    of F_p12: the check is (m(P1, q1) m(P2, q2) const)^h = 1."""

    def __init__(self, q1: bn254.G2Point, q2: bn254.G2Point, const: bn254.Fp12) -> None:
        self.q = (q1, q2)
        self.lines = [PC.fixed_lines(q1), PC.fixed_lines(q2)]
        self.const = const
        self.tau = PC.compress(PC.easy(const).conj())  # E(const)^-1
        self.n_q = N_Q

    def pairs(self, points: Sequence[bn254.G1Point]) -> list[tuple[bn254.G1Point, bn254.G2Point]]:
        ensure(len(points) == 2, 'two points of G1')
        return list(zip(points, self.q))

    def product(self, points: Sequence[bn254.G1Point]) -> bn254.Fp12:
        """The Miller value of everything: its h-th power is 1 iff the pairing check holds."""
        return PC.miller_values(self.pairs(points))[-1] * self.const

    def witness(
        self,
        points: Sequence[bn254.G1Point],
        residue: tuple[bn254.Fp12, int] | None = None,
        check: bool = True,
    ) -> dict[str, Any] | None:
        """The witness for (P1, P2), or None if the check does not hold for them.  Tests may give the
        residue witness (c, s) and seal without checking the relations (seal)."""
        res = residue or bn254.residue_witness(self.product(points))
        if res is None:
            return None
        c, _ = res
        fs = PC.miller_values(self.pairs(points), c)
        v = {
            'P': [tuple(pt) for pt in points],
            'ac': PC.compress(PC.easy(c)),
            'a': [PC.compress(PC.easy(f)) if COMMIT[i] else None for i, f in enumerate(fs)],
            'tau': self.tau,
        }
        return self.seal(v, check)

    def seal(self, v: dict[str, Any], check: bool = True) -> dict[str, Any]:
        """The witness words of the values v: the points, a_c and the committed values, then r, Q (its
        coefficients of odd degree) and z.  check=False lets a test seal values whose relations do not
        hold (Q is then S / M without its remainder)."""
        mont = lambda xs: [to_mont(x % P) for x in xs]
        w: dict[str, Any] = {
            'points': mont([x for pt in v['P'] for x in pt]),
            'ac': mont(v['ac']),
            'leaves': [mont(v['a'][i]) for i in range(N_STEPS) if COMMIT[i]],
        }
        t = PC.wbytes(w['points']) + PC.wbytes(w['ac']) + b''.join(map(PC.wbytes, w['leaves']))
        w['r'] = int.from_bytes(hashlib.sha256(t).digest(), 'big')
        q, rem = poly.divmod_m(combine(PC.PolyRing, relations(PC.PolyRing, v, self.lines), from_mont(w['r'])))
        ensure(not check or rem == [0] * 12, 'the relations do not hold')
        ensure(not any(q[0::2]), 'Q is not odd')
        q = q[1::2]  # Q = w Q'(w^2): the coefficients of Q'
        ensure(len(q) <= self.n_q, 'Q is longer than its words')
        w['q'] = mont(q + [0] * (self.n_q - len(q)))
        w['z'] = int.from_bytes(hashlib.sha256(PC.wbytes([w['r']] + w['q'])).digest(), 'big')
        w['values'] = v
        return w


# ---------------------------------------------------------------------------------------------------
# The program
#
# The loop state is ((((N, D), so), h), run): N / D = u at z, so the Horner sum in r of the relations so
# far (`combine`), h the SHA-256 context of the transcript, and the run values, computed once in the setup
# from z, r and the points.  zeta = z^6 - 9 is the tower's u at z, where an element of F_p2 is evaluated.
#
# run = (RUN_STEP, RUN_REST).  A step function gets RUN_STEP only.  It is two subtrees: RUN_ANY, which
# every step reads (what the two lines at z need: the line of Q_k at P_k is y_k + c3 x_k z + c4 z^3), and
# RUN_COMMIT, which only a committed step reads (the powers of z for a(z), r, and -2 z), so a step without
# a commitment gets (N, D) and RUN_ANY alone.  RUN_REST has E(c) = cp / cm at z, the factor of the
# additions A+ and A-.
#
# The loop goes span by span (`spans`): the steps up to the next committed value.  Within a span (N, D)
# passes from one step function to the next, and so, h and the run values, which only a committed step
# changes or reads in full, are read and put back once.
RUN_ANY = ['z3', 'z3zeta', 'x1z', 'x1zz', 'y1', 'x2z', 'x2zz', 'y2']
RUN_COMMIT = ['z1', 'z2', 'z4', 'z6', 'z8', 'z10', 'r', 'm2z']
RUN_STEP = RUN_ANY + RUN_COMMIT
RUN_REST = ['cp', 'cm']
# computed in the setup, used at the end only: the last relation is N pn + D npd; z^12, z^14 and z^16 are
# read by Q(z) and M(z)
END = ['pn', 'npd', 'z12', 'z14', 'z16']
CORE = ('N', 'D')  # what every step changes
STATE = (*CORE, 'so')
DATA_WORDS = 8  # a step's constants: c3, c4 of Q1's line, then of Q2's, two words each


class FixedCheck(PC.Parts):
    """Generator of the check over a backend.  q1, q2: the fixed points of G2; const: the constant of
    F_p12 (see Prover); b: the bounds of the loop state (bounds())."""

    def __init__(
        self, fp: Fp, q1: bn254.G2Point, q2: bn254.G2Point, const: bn254.Fp12, b: dict[str, int] | None = None
    ) -> None:
        self.fp, self.be, self.cv = fp, fp.be, Curve(fp)
        self.prover = pr = Prover(q1, q2, const)
        self.data = [
            [to_mont(a % P) for ln in pr.lines for cf in ln[i] for a in (cf.c0, cf.c1)] for i in range(N_STEPS)
        ]
        self.tau_const = [[to_mont(x) for x in pr.tau[:4]], [to_mont(x) for x in pr.tau[4:]]]
        self.run = RUN_STEP + RUN_REST
        self.b = dict(b) if b is not None else {}
        if not self.b:
            ensure(not is_sym(self.be), 'the bounds are computed with the numeric backend')
            self.sample_bounds()
        be = self.be
        self.TOP2 = be.function('TOP2', [words(4), words(2)], lambda a: be.checks([self.top2_zero(w) for w in flat(a)]))
        self.steps: dict[tuple[str, bool], Any] = {}
        for kind, commit in sorted({self.fn_of(k) for k in range(N_STEPS)}, key=lambda kc: ('DAF'.index(kc[0]), kc[1])):
            name = f'STEP_{kind}' + ('' if commit else '_')
            self.steps[(kind, commit)] = be.function(name, self.step_shape(kind, commit), self.step_body(kind, commit))
        self.QCHUNK = be.function('QCHUNK', [[words(2), words(7)], words(8)], self.qchunk_body)
        # the step functions and QCHUNK take the loop state within these bounds and must give it back within
        # them (sample_bounds found them so; a stale or hand-made bounds dict must not slip through)
        for nm in (*STATE, 'qz'):
            ensure(self.b.get(nm + '_out', 0) <= self.b[nm], f'the loop state {nm} exceeds its bound')
        self.EVAL = be.function('EVAL', [[words(4), words(2)], E('', 256, 0)], self.eval_body)
        if is_sym(be):
            self.costs = {fn.t: fn.c for fn in [*self.steps.values(), self.QCHUNK, self.EVAL]}

    @staticmethod
    def fn_of(k: int) -> tuple[str, bool]:
        """(function kind, commit) of step k: 'D' squares N and D, 'A' multiplies them by a factor it is
        given, 'F' (the Frobenius additions) does neither."""
        return STEPS[k][0], COMMIT[k]

    # the shapes
    @staticmethod
    def run_shape(commit: bool = True) -> Shape:
        """The shape of RUN_STEP, or of RUN_ANY alone."""
        return [words(len(RUN_ANY)), words(len(RUN_COMMIT))] if commit else words(len(RUN_ANY))

    @staticmethod
    def core_shape(commit: bool = True) -> Shape:
        """((N, D), so), or (N, D) alone."""
        return [words(len(CORE)), E('', 256, 0)] if commit else words(len(CORE))

    def state_shape(self) -> Shape:
        """((((N, D), so), h), (RUN_STEP, RUN_REST))"""
        return [[self.core_shape(), E('', SHA_CTX_W, 0)], [self.run_shape(), words(len(RUN_REST))]]

    def step_shape(self, kind: str, commit: bool) -> Shape:
        """A step function's arguments: (state, constants), the state being (((N, D), so), RUN_STEP) with the
        committed value, or ((N, D), RUN_ANY) if the step commits nothing; an addition's constants come
        after its factor (g_N, g_D)."""
        st = [self.core_shape(commit), self.run_shape(commit)]
        data = words(DATA_WORDS)
        return [[st, leaf_shape()] if commit else st, [words(2), data] if kind == 'A' else data]

    # one step
    def step_body(self, kind: str, commit: bool) -> Any:
        """Body of a step function (step_shape) -> the state, ((N, D), so) or (N, D).  Evaluates the two
        lines at z and at -z, the next N and D, and a committed value at z, whose relation it adds to so
        as `combine` does.  The loop absorbs the committed value into h."""
        fp, be, b = self.fp, self.be, self.b
        rd, one = self.rd, self.one

        def body(accs):
            env, args = accs
            st, leaf = env if commit else (env, None)
            run = dict(zip(RUN_STEP if commit else RUN_ANY, flat(st[1])))
            c: dict[str, Any] = {
                nm: Val(w, b[nm]) for nm, w in zip(STATE if commit else CORE, flat(st[0]), strict=True)
            }
            c['dd'] = [Val(w, P - 1) for w in (args[1] if kind == 'A' else args)]
            for nm in RUN_STEP if commit else RUN_ANY:
                c[nm] = Val(run[nm], KB)
            if commit:
                c['a'] = [Val(w, F_HI) for w in flat(leaf)]
            if kind == 'A':
                c['gn'], c['gd'] = (Val(w, KB) for w in args[0])

            def odd(c, k):  # the odd part of Q_k's line at z: x_k z c3 + z^3 c4, with c3 and c4 at zeta
                d = c['dd'][4 * k - 4 : 4 * k]
                return rd([(c[f'x{k}z'], d[0]), (c[f'x{k}zz'], d[1]), (c['z3'], d[2]), (c['z3zeta'], d[3])])

            def first(c):
                out = [odd(c, 1), odd(c, 2)]
                if commit:  # a(z) + z, for a(z) = sum a_k z^2k
                    az = rd([(c['a'][0], one())] + [(c['a'][k], c[f'z{2 * k}']) for k in range(1, 6)])
                    out.append(fp.normalize(fp.add(az, c['z1'])))
                return out

            # the lines' odd parts and a(z) + z are read twice: they go to a fresh environment with what is
            # still needed, which is less to copy than everything else is to keep
            kept = [*(STATE if commit else CORE), 'y1', 'y2', *(['r', 'm2z'] if commit else []), 'gn', 'gd']
            steps = [('let', ['o1', 'o2'] + (['azp'] if commit else []), first, [nm for nm in c if nm not in kept])]

            def final(c, _):
                # a line at z is y + o, at -z (its conjugate) y - o
                lp = [fp.add(c[f'y{k}'], c[f'o{k}']) for k in (1, 2)]
                lm = [fp.sub(c[f'y{k}'], c[f'o{k}']) for k in (1, 2)]
                Lp, Lm = rd([(lp[0], lp[1])]), rd([(lm[0], lm[1])])
                if kind == 'D':
                    N2, D2 = rd([(c['N'], c['N'])]), rd([(c['D'], c['D'])])
                elif kind == 'A':
                    N2, D2 = rd([(c['N'], c['gn'])]), rd([(c['D'], c['gd'])])
                else:
                    N2, D2 = c['N'], c['D']
                Nn, Dn = rd([(N2, Lm)]), rd([(D2, Lp)])
                if commit:  # N (a - z) - D (a + z) joins the sum, then N, D = a + z, a - z = (a + z) - 2 z
                    azp = c['azp']
                    azm = lambda: fp.add(azp, c['m2z'])  # one jet, so it is computed where it is read
                    outs = [azp, azm(), rd([(c['so'], c['r']), (Nn, azm()), (Dn, fp.neg(azp))])]
                else:
                    outs = [Nn, Dn]
                for nm, v in zip(STATE, outs):
                    b[nm + '_out'] = max(b.get(nm + '_out', 0), v.hi)
                return fp.pack([outs[:2], outs[2]] if commit else outs)

            new = chain(fp, c, steps, final)
            return be.seq(self.top2_6(leaf), new) if commit else new

        return body

    def sample_bounds(self) -> None:
        """The bounds of the loop state: a fixed point of the step bodies, found on the numeric backend by
        widening the inputs (1% slack) until the outputs fit."""
        b = self.b
        names = (*STATE, 'qz')
        b.update(dict.fromkeys(names, KB))
        zeros = lambda n: [0] * n
        for _ in range(30):
            for nm in names:
                b[nm + '_out'] = 0
            for kind in 'DAF':
                for commit in (False, True):
                    run = [zeros(len(RUN_ANY)), zeros(len(RUN_COMMIT))]
                    st = [[zeros(2), 0], run] if commit else [zeros(2), run[0]]
                    data = zeros(DATA_WORDS)
                    self.step_body(kind, commit)(
                        [[st, [zeros(4), zeros(2)]] if commit else st, [zeros(2), data] if kind == 'A' else data]
                    )
            self.qchunk_body([[[0, 0], zeros(7)], zeros(8)])
            if all(b[nm + '_out'] <= b[nm] for nm in names):
                return
            for nm in names:
                b[nm] = max(b[nm], b[nm + '_out'] * 101 // 100)
        raise RuntimeError('no fixed point for the loop bounds')

    # the loop
    def span_value(self, span: Sequence[int], st: Any, leaf: Any = None, datas: Any = None) -> Any:
        """The state after the steps of `span`, of which only the last may commit a value (`spans`).  (N, D)
        goes from one step function to the next, and the rest of the state is put back once, after the
        last.  leaf: the committed value, if the span ends with one; datas: each step's line constants, if
        they are given (accessors), else constants here."""
        be = self.be
        sub = be.subtree if is_sym(be) else (lambda v: v)
        if datas is None:
            datas = [be.words_const(self.data[k]) if is_sym(be) else self.data[k] for k in span]
        (nd, so), h = st[0]
        nd = out = sub(nd)
        run = dict(zip(self.run, flat(st[1])))
        for k, data in zip(span, datas, strict=True):
            fn = self.steps[self.fn_of(k)]
            if STEPS[k] in ('A+', 'A-'):  # u times E(c^-1) = cm / cp at A+, E(c) = cp / cm at A-
                g = ('cm', 'cp') if STEPS[k] == 'A+' else ('cp', 'cm')
                data = [[sub(run[g[0]]), sub(run[g[1]])], data]
            if COMMIT[k]:
                ensure(k == span[-1], 'a committed value ends its span')
                out = be.call(fn, [[[[nd, so], sub(st[1][0])], leaf], data])
                lf = be.split(leaf, leaf_shape()) if is_sym(be) else leaf
                h = self.sha_add(h, [lf[0], lf[1]])  # the transcript absorbs the committed value
            else:
                nd = be.call(fn, [[nd, sub(st[1][0][0])], data])
                out = [nd, so]
        return be.pack([[out, h], sub(st[1])]) if is_sym(be) else [[out, h], st[1]]

    def loop(self, state0: Any, leaves: Any) -> Any:
        """The state after the 88 steps, span by span.  Sym: a span reads its committed value from a witness
        node of its own (LEAF_NAMES), and the spans with the same steps share their code, which takes
        ((state, committed value), the steps' constants), or (state, constants) for a last span without
        one.  Num: leaves has the committed values in order."""
        be = self.be
        if not is_sym(be):
            it = iter(leaves)
            for span in spans():
                state0 = self.span_value(span, state0, next(it) if COMMIT[span[-1]] else None)
            return state0
        shape = self.state_shape()
        state_w = sum(e.w for e in flat(shape))
        e = state0
        bodies: dict[tuple[str, ...], E] = {}
        for span in spans():
            last = span[-1]
            w = 256 * LEAF_WORDS if COMMIT[last] else 0
            key = (*(STEPS[k] for k in span), 'C' if w else '')
            if key not in bodies:
                be._push_env(state_w + w + 256 * DATA_WORDS * len(span))
                try:
                    datas = [be.subtree(d) for d in be._unpack('I', [words(DATA_WORDS)] * len(span))]
                    st = be._unpack('OO' if w else 'O', shape)
                    bodies[key] = be.share(self.span_value(span, st, be.proj('OIH', w) if w else None, datas))
                finally:
                    be._pop_env()
            if w:
                e = be.pair(e, be.witness(LEAF_NAMES[last], leaf_type(), w))
            consts = be.pack([be.words_const(self.data[k]) for k in span])
            e = be.share(be.comp(be.pair(e, consts), bodies[key]))  # one line of the program text per span
        return e

    # before the loop
    def setup(self, pts: Any, ac: Any, rz: Any) -> Term:
        """((((N, D), so), h), run) and the END values.  Checks P1 and P2 on the curve and the words of a_c,
        computes the run values, starts u = E(c^-1) as N / D = (a_c(z) - z) / (a_c(z) + z), and starts h
        with the points and a_c."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, lc = self.rd, self.one, fp.lin_const
        z = lambda k: 'z' if k == 1 else f'z{k}'
        raw = lambda w: Val(w, WORD_MAX)
        ctx = {
            'raw': [raw(rz[1]), raw(rz[0]), [raw(w) for w in flat(pts)]],
            'ac': [[Val(w, F_HI) for w in g] for g in ac],
        }
        t_at = lambda n, c: lc([(c[z(k)], g) for k, g in poly.FROB_W[n]])  # t_n(z)
        sq = lambda a: lambda c: rd([(c[a], c[a])])
        mu = lambda a, b: lambda c: rd([(c[a], c[b])])
        layer = lambda fs: lambda c: [f(c) for _, f in fs]  # the values of one layer
        layers = [
            [('z2', sq('z'))],
            [('z3', mu('z2', 'z')), ('z4', sq('z2'))],
            [('z6', sq('z3')), ('z7', mu('z4', 'z3')), ('z8', sq('z4'))],
            [('z10', mu('z4', 'z6')), ('z12', sq('z6')), ('z14', mu('z6', 'z8')), ('z16', sq('z8'))],
        ]
        # The first layer normalises the inputs into a fresh environment, which the on-curve checks then read;
        # every later layer pushes its values in front of it, so a_c and the points are not copied along.
        norm = lambda c: [fp.normalize(c['raw'][0]), fp.normalize(c['raw'][1]), [fp.normalize(v) for v in c['raw'][2]]]
        on_curve = lambda c: [
            Val(cv.g1_on_curve_check(c['p'][0], c['p'][1]), 0),
            Val(cv.g1_on_curve_check(c['p'][2], c['p'][3]), 0),
        ]
        kb = lambda v: v if v.hi <= KB else fp.normalize(v)
        steps = (
            [('let', ['z', 'r', 'p'], norm, ['raw']), ('check', on_curve)]
            + [('push', [n for n, _ in L], layer(L)) for L in layers]
            + [
                ('push', ['zeta', 't1', 't2'], lambda c: [lc([(c['z6'], 1), (one(), -9)]), t_at(1, c), t_at(2, c)]),
                (
                    'push',
                    ['acz', 't3', 't1s', 't2s'],
                    lambda c: [
                        self.eval_at(c['ac'], c['z2']),
                        fp.mul_const(c['t1'], poly.FROB_W[2][0][1]),  # t3 = g t1
                        rd([(c['t1'], c['t1'])]),
                        rd([(c['t2'], c['t2'])]),
                    ],
                ),
                (
                    'push',
                    ['x1z', 'x2z', 'z3zeta', 'cp', 'cm', 't3s', 'A1', 'A2'],
                    lambda c: [
                        rd([(c['p'][0], c['z'])]),
                        rd([(c['p'][2], c['z'])]),
                        rd([(c['z3'], c['zeta'])]),
                        kb(fp.add(c['acz'], c['z'])),  # E(c) = cp / cm at z
                        kb(fp.sub(c['acz'], c['z'])),
                        rd([(c['t3'], c['t3'])]),
                        self.eval_at(c['ac'], c['t1s']),
                        self.eval_at(c['ac'], c['t2s']),
                    ],
                ),
            ]
        )
        end_hi: list[int] = []

        def final(c, checks):
            vals = {nm: c[z(int(nm[1:]))] for nm in self.run if nm[0] == 'z' and nm[1:].isdigit()}  # the powers of z
            vals.update({nm: c[nm] for nm in ('z3zeta', 'x1z', 'x2z', 'r', 'cp', 'cm')})
            vals.update(
                x1zz=rd([(c['x1z'], c['zeta'])]),
                x2zz=rd([(c['x2z'], c['zeta'])]),
                y1=c['p'][1],
                y2=c['p'][3],
                m2z=fp.mul_const(c['z'], -2),
            )
            run = [kb(vals[nm]) for nm in self.run]
            for nm, v in zip(self.run, run):
                ensure(v.hi <= KB, f'run value bound: {nm}')
            start = [c['cm'], c['cp'], fp.const(0)]  # u = E(c^-1) = cm / cp, and the empty sum
            for nm, v in zip(STATE, start, strict=True):
                ensure(v.hi <= self.b[nm], f'initial bound: {nm}')
            # the last relation N pn - D pd: pi(c'^-1) pi^2(c') pi^3(c'^-1) / tau, numerator and denominator
            tau = be.consts(256, self.tau_const) if is_sym(be) else self.tau_const
            A3, At = self.eval_at(c['ac'], c['t3s']), self.eval_at(tau, c['z2'])
            prod = lambda vs: rd([(rd([(rd([(vs[0], vs[1])]), vs[2])]), vs[3])])
            pn = prod([fp.sub(c['A1'], c['t1']), fp.add(c['A2'], c['t2']), fp.sub(A3, c['t3']), fp.sub(At, c['z'])])
            pd = prod([fp.add(c['A1'], c['t1']), fp.sub(c['A2'], c['t2']), fp.add(A3, c['t3']), fp.add(At, c['z'])])
            ev = {nm: kb(c[nm]) for nm in END[2:]}
            for nm, v in ev.items():
                ensure(v.hi <= KB, f'end value bound: {nm}')
            end = [pn, fp.mul_const(pd, -1), *ev.values()]
            end_hi.extend(v.hi for v in end)
            n_any, n_step = len(RUN_ANY), len(RUN_STEP)
            packed = [[start[:2], start[2]], [[run[:n_any], run[n_any:n_step]], run[n_step:]]]
            return be.seq(be.checks([ch.e for ch in checks]), be.pack([fp.pack(packed), fp.pack(end)]))

        out = chain(fp, ctx, steps, final)
        self.end_hi = end_hi
        h = self.sha_add(self.sha_init(), [pts, ac[0], ac[1]])
        return be.seq(self.top2_6(ac), self._with_h(out, h))

    def _with_h(self, out: Any, h: Any) -> Any:
        """((start, run), end) and h -> ((start, h, run), end)"""
        be = self.be
        if not is_sym(be):
            (start, run), end = out
            return [[[start, h], run], end]
        shape = [
            [[self.core_shape(), [self.run_shape(), words(len(RUN_REST))]], words(len(END))],
            E('', SHA_CTX_W, 0),
        ]
        return be.with_env(
            be.pair(out, h),
            shape,
            lambda a: be.pack([[[be.subtree(a[0][0][0]), a[1]], be.subtree(a[0][0][1])], be.subtree(a[0][1])]),
        )

    # after the loop
    def final(self, state: Any, end: Any, q: Any, rz: Any) -> Term:
        """The last relation, S(z) = z Q'(z^2) M(z), and r, z against the two hashes."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one = self.rd, self.one
        (st, h), run = state
        run = {nm: Val(w, KB) for nm, w in zip(self.run, flat(run))}
        run.update({nm: Val(w, KB) for nm, w in zip(END, end) if nm in ('z12', 'z14', 'z16')})
        ensure(len(PC.blocks(N_Q)) == len(q), 'the blocks of Q')
        c = {nm: Val(w, self.b[nm]) for nm, w in zip(STATE, flat(st), strict=True)}
        c['qz'] = Val(self.q_value(q, run), self.b['qz'])
        c.update({nm: Val(w, hi) for nm, w, hi in zip(END, end, self.end_hi, strict=True)})
        c.update({nm: run[nm] for nm in ('r', 'z1', 'z6')})
        # S(z) - z Q'(z^2) M(z): the sum with the last relation, and -z M(z) = z (-z^12 + 18 z^6 - 82)
        nzm = rd([(c['z1'], fp.lin_const([(c['z12'], -1), (c['z6'], 18), (one(), -82)]))])
        identity = cv.zero_check(rd([(c['so'], c['r']), (c['N'], c['pn']), (c['D'], c['npd']), (c['qz'], nzm)])).e
        hashes = self.challenges(h, q, rz)
        return be.checks([identity, *hashes]) if is_sym(be) else 0

    def program(self, pts: Any, ac: Any, rz: Any, leaves: Any = None, q: Any = None) -> Term:
        """The whole check.  pts, ac, rz as in witness_shape().  Sym: a unit-typed E over the environment,
        which reads the committed values and Q from witness nodes of their own (witness_nodes); Num: runs
        the checks, on the committed values and Q given."""
        be = self.be
        s0 = self.setup(pts, ac, rz)
        if not is_sym(be):
            st0, end = s0
            return self.final(self.loop(st0, leaves), end, q, rz)
        qshape = [words(k) for k in PC.blocks(N_Q)]
        parts: dict[str, int] = {}

        def body(a):
            (st0, end), rza = a
            st = self.loop(be.subtree(st0), None)
            qa = be.witness(Q_NAME, PC.q_type(N_Q), 256 * N_Q)
            out = be.with_env(
                be.pack([st, be.subtree(end), qa, be.subtree(rza)]),
                [self.state_shape(), words(len(END)), qshape, words(2)],
                lambda a: self.final(*a),
            )
            parts.update(loop=st.c, final=out.c - st.c)
            return out

        out = be.with_env(be.pack([s0, be.subtree(rz)]), [[self.state_shape(), words(len(END))], words(2)], body)
        self.parts = {'setup': s0.c, **parts}
        return out


_BOUNDS: dict[str, int] | None = None


def bounds() -> dict[str, int]:
    """The bounds of the loop state (they depend on the structure only), computed once."""
    global _BOUNDS
    if _BOUNDS is None:
        G = bn254.G2_GEN
        # any points, and any constant outside F_p6: the step functions' arguments are bounded alike
        _BOUNDS = FixedCheck(Fp(Num()), G, G, bn254.Fp12(bn254.Fp6(1), bn254.Fp6(1))).b
    return _BOUNDS


# ---------------------------------------------------------------------------------------------------
# The witness of the check: ((points, a_c), (r, z)) in the program's witness, and witness nodes of their
# own for each committed value and for Q, in hashing blocks.  a_c and a committed value: 4 + 2 words.  The
# numeric backend takes all of it as one value (witness_num).
LEAF_WORDS = 6
LEAF_NAMES = {k: f'wl{k}' for k in range(N_STEPS) if COMMIT[k]}
Q_NAME = 'wq'
_T = PC._T


def leaf_shape() -> Shape:
    """A committed value: 4 + 2 words."""
    return [words(4), words(2)]


def leaf_type() -> str:
    return Tbalanced([_T(4), _T(2)])


def witness_shape() -> Shape:
    """The check's part of w_in: ((points, a_c), (r, z))."""
    return [[words(4), [words(4), words(2)]], words(2)]


def witness_type() -> str:
    return f'(({_T(4)} * ({_T(4)} * {_T(2)})) * {_T(2)})'


def witness_bits() -> int:
    return 256 * (4 + 6 + 2)


def _split(w: dict[str, Any]) -> tuple[Any, Any, Any, Any]:
    qs, i = [], 0
    for k in PC.blocks(len(w['q'])):
        qs.append(w['q'][i : i + k])
        i += k
    return w['points'], [w['ac'][:4], w['ac'][4:]], [[lf[:4], lf[4:]] for lf in w['leaves']], qs


def witness_num(w: dict[str, Any]) -> list[Any]:
    """The witness as the nested value the numeric backend takes: ((points, a_c), ((r, z), (committed
    values, Q)))."""
    pts, ac, leaves, qs = _split(w)
    return [[pts, ac], [[w['r'], w['z']], [leaves, qs]]]


def witness_value(w: dict[str, Any]) -> WSpec:
    """The part of the program's witness as a harness value spec (tools/harness)."""
    pts, ac, _, _ = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    return wpair(wpair(W(pts), wpair(W(ac[0]), W(ac[1]))), W([w['r'], w['z']]))


def witness_nodes(w: dict[str, Any]) -> dict[str, WSpec]:
    """The values of the witness nodes of their own, by name."""
    _, _, leaves, qs = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    out = {nm: wpair(W(lf[0]), W(lf[1])) for nm, lf in zip(LEAF_NAMES.values(), leaves, strict=True)}
    out[Q_NAME] = wbalanced([W(x) for x in qs])
    return out
