"""The pairing check e(-A, B) e(L, gamma) e(C, delta) e(alpha, beta) = 1 as one polynomial identity.

F_p12 is F_p[w] / M(w), M = w^12 - 18 w^6 + 82 (poly.py), so every product the check needs, in F_p12 and
in the F_p2 arithmetic of B's points, is a polynomial product modulo M.  The prover writes the Miller
value after some of the steps (COMMIT) into the witness, and each step becomes a few relations
R(w) = 0 (mod M):

    doubling     f^2 l_B l_gamma l_delta - f',      lambda y - 3/2 x^2
    addition     f g l_B l_gamma l_delta - f',      lambda (xQ - x) - (yQ - y),     (xQ - x) d - 1
    at the end   x - x(-psi^3(B)),   y - y(-psi^3(B)),   f pi(c^-1) pi^2(c) pi^3(c^-1) - T_s,   c c^-1 - 1

f, f' are the Miller values, g = c^-1 or c (the residue witness, as in Novakovic and Eagen),
l the lines at P = -A, L, C.  Only B's slopes lambda are committed: x' = lambda^2 - 2x and
y' = lambda (x - x') - y are polynomials in them.  A slope that satisfies its relation is the true one
(y is never 0, and d, the inverse of xQ - x, proves xQ != x), so every step is the group law.  The last
three relations are the G2 membership of B and the residue check; T_s = (W27^s e(alpha, beta))^-1.
After a step whose value is not committed, f' is the product itself, so the next relation carries a
polynomial of higher degree; the first relation of a step is dropped then.

The prover combines the relations with powers of a challenge r, S = sum r^k R_k, and supplies the
quotient Q = S / M.  The program evaluates everything at one point z and checks S(z) = Q(z) M(z).  It
multiplies only in F_p: an F_p12 product becomes one product of two evaluations.

Soundness.  r is the SHA-256 of the public inputs, the proof and everything committed, and z the
SHA-256 of r and Q.  If some R_k is not 0 modulo M, S is not 0 modulo M except for at most 150 values of
r; then S - Q M is a nonzero polynomial of degree at most 211, which vanishes at z with probability at
most 211 / p.  The program gets r and z as witness words and compares them with the two hashes at the
end.

`relations` is written once over an abstract ring: the prover runs it on polynomials to get S and Q,
the tests run it on numbers to compare with the program.
"""
import hashlib
from . import bn254, poly
from .curve import Curve, chain
from .dsl import ensure, balanced, Tbalanced, wv, wbit, wpair, wbalanced
from .fp import Fp, Val, P, WORD_MAX, to_mont, from_mont
from .sym import E, Num, words, is_sym, flat, SHA_CTX_W

F_HI = 2**254 - 1 # bound of a committed word: the program checks that its top two bits are 0
KB = 130 * P // 100 # bound of every run value (z^k, r, ...) carried through the loop
THREE_HALVES = 3 * pow(2, -1, P) % P


# ---------------------------------------------------------------------------------------------------
# The loop: 88 steps along the NAF of 6x + 2
def loop_steps():
    """'D' doubling, 'A+' / 'A-' addition of +-Q, then the Frobenius additions 'F1' (pi(Q)), 'F2' (-pi^2(Q))."""
    digits = bn254.ATE_NAF
    steps = []
    for i in range(len(digits) - 2, -1, -1):
        steps.append('D')
        if digits[i]:
            steps.append('A+' if digits[i] > 0 else 'A-')
    return steps + ['F1', 'F2']


STEPS = loop_steps() # 65 doublings, 8 + 13 additions, 2 Frobenius additions
N_STEPS = len(STEPS)
ADDS = ('A+', 'A-', 'F1', 'F2')


def step_points(Q):
    """The point added at each kind of step, for the G2 point Q."""
    Q1 = bn254.g2_frobenius(Q)
    return {'D': None, 'A+': Q, 'A-': bn254.g2_neg(Q), 'F1': Q1, 'F2': bn254.g2_neg(bn254.g2_frobenius(Q1))}


def slopes(Q):
    """(lambda, (c3, c4)) of every step of the G2 point Q, as in bn254.multi_miller_loop_affine."""
    pts, T, out = step_points(Q), Q, []
    for kind in STEPS:
        Qk = pts[kind]
        lam = bn254.affine_double_slope(T) if Qk is None else bn254.affine_add_slope(T, Qk)
        T, coeffs = bn254.affine_step(T, lam, Qk)
        out.append((lam, coeffs))
    return out


def fixed_lines(Q):
    """The line coefficients (c3, c4) = (-lambda, lambda xT - yT) of every step of a fixed point."""
    return [coeffs for _, coeffs in slopes(Q)]


# ---------------------------------------------------------------------------------------------------
# The relations, over a ring
class PolyRing:
    """Polynomials over F_p."""
    X = poly.X
    add, sub, mul = staticmethod(poly.add), staticmethod(poly.sub), staticmethod(poly.mul)
    k = staticmethod(poly.const)
    elem = staticmethod(poly.trim)


class NumRing:
    """F_p, the variable set to z."""
    def __init__(self, z):
        self.X = z % P

    add = staticmethod(lambda a, b: (a + b) % P)
    sub = staticmethod(lambda a, b: (a - b) % P)
    mul = staticmethod(lambda a, b: a * b % P)
    k = staticmethod(lambda c: c % P)

    def elem(self, coeffs):
        return poly.evaluate(coeffs, self.X)


class DegRing:
    """Degrees: the shape of S, hence the size of Q."""
    X = 1
    add = sub = staticmethod(max)
    mul = staticmethod(lambda a, b: a + b)
    k = staticmethod(lambda c: 0)
    elem = staticmethod(lambda coeffs: 11)


def relations(R, v, lines, table, commit=None):
    """The relations R_k in order, over the ring R.  v: the values (Prover.witness); lines: fixed_lines of
    gamma and delta; table: T_s for s = 0, 1, 2 (direct coefficients); commit: the steps whose Miller
    value is committed (COMMIT).  After any other step, f' is the product itself, a polynomial of
    higher degree."""
    commit = COMMIT if commit is None else commit
    X = R.X
    X3 = R.mul(R.mul(X, X), X)
    U = R.sub(R.mul(X3, X3), R.k(9)) # u = w^6 - 9

    def phi(a): # an F_p2 element as a polynomial
        a = bn254._fp2(a)
        return R.add(R.k(a.c0), R.mul(R.k(a.c1), U))

    def line(Pt, c3, c4): # yP + c3 xP w + c4 w^3: the tower line c0 + c3 w + c4 v w
        return R.add(R.add(R.k(Pt[1]), R.mul(R.mul(R.k(Pt[0]), X), c3)), R.mul(X3, c4))

    xb, yb = v['B']
    c, ci = R.elem(v['c']), R.elem(v['ci'])
    rels = [R.sub(R.mul(c, ci), R.k(1))]
    pts = step_points(v['B'])
    x, y, f = phi(xb), phi(yb), ci
    for i, kind in enumerate(STEPS):
        lam = phi(v['lam'][i])
        if kind == 'D':
            rels.append(R.sub(R.mul(lam, y), R.mul(R.k(THREE_HALVES), R.mul(x, x))))
            x2 = R.sub(R.mul(lam, lam), R.mul(R.k(2), x))
            f2 = R.mul(f, f)
        else:
            xq, yq = phi(pts[kind][0]), phi(pts[kind][1])
            dx = R.sub(xq, x)
            rels.append(R.sub(R.mul(lam, dx), R.sub(yq, y)))
            rels.append(R.sub(R.mul(dx, phi(v['d'][i])), R.k(1)))
            x2 = R.sub(R.sub(R.mul(lam, lam), x), xq)
            f2 = R.mul(f, ci) if kind == 'A+' else R.mul(f, c) if kind == 'A-' else f
        m = R.sub(R.mul(lam, x), y) # lambda x - y, the c4 of B's line
        lB = line(v['P'], R.sub(R.k(0), lam), m)
        lg = line(v['L'], phi(lines[0][i][0]), phi(lines[0][i][1]))
        ld = line(v['C'], phi(lines[1][i][0]), phi(lines[1][i][1]))
        f_next = R.mul(R.mul(R.mul(f2, lB), lg), ld)
        if commit[i]:
            rels.append(R.sub(f_next, R.elem(v['f'][i])))
            f_next = R.elem(v['f'][i])
        x, y, f = x2, R.sub(m, R.mul(lam, x2)), f_next
    rels.append(R.sub(x, phi(xb.conj() * bn254.FROB3[2])))
    rels.append(R.sub(y, phi(yb.conj() * -bn254.FROB3[3])))
    pis = R.mul(R.mul(R.elem(frob(v['ci'], 1)), R.elem(frob(v['c'], 2))), R.elem(frob(v['ci'], 3)))
    rels.append(R.sub(R.mul(f, pis), R.elem(table[v['s']])))
    return rels


def frob(coeffs, n):
    """pi^n of an element given by its 12 coefficients."""
    out = [0] * 12
    for j, a in enumerate(coeffs):
        for k, g in enumerate(poly.FROB[n][j]):
            out[k] = (out[k] + a * g) % P
    return out


def horner(R, rels, r):
    """sum r^(n-1-k) R_k, the combination the program accumulates."""
    acc = R.k(0)
    for rel in rels:
        acc = R.add(R.mul(acc, R.k(r)), rel)
    return acc


def _shape(commit):
    """The number of relations and the degree of S (DegRing reads only the structure)."""
    z = bn254.Fp2(0)
    v = dict(P=(0, 0), B=bn254.G2_GEN, C=(0, 0), L=(0, 0), c=[0] * 12, ci=[0] * 12, s=0,
             lam=[z] * N_STEPS, f=[[0] * 12] * N_STEPS, d={i: z for i in range(N_STEPS)})
    rels = relations(DegRing, v, [[(z, z)] * N_STEPS] * 2, [[0] * 12] * 3, commit)
    return len(rels), max(rels)


def schedule(cap):
    """The steps whose Miller value is committed: left to right, a step is skipped whenever S stays
    within the degree cap.  A committed value costs 12 words of witness, a degree of S one word of Q."""
    commit = [True] * N_STEPS
    for i in range(N_STEPS):
        commit[i] = False
        if _shape(commit)[1] > cap:
            commit[i] = True
    return commit


DEG_CAP = 211 # the cap with the fewest committed words: 36 Miller values, Q of 200 words (vs 88 and 50)
COMMIT = schedule(DEG_CAP)
N_RELS, DEG_S = _shape(COMMIT) # 150 relations, degree 211
N_Q = DEG_S - 11 # coefficients of Q


# ---------------------------------------------------------------------------------------------------
# The transcript: r = SHA-256(inputs, points, s, c, c^-1, leaves), z = SHA-256(r, Q), all words big-endian
def wbytes(ws):
    return b''.join(w.to_bytes(32, 'big') for w in ws)


def s_byte(s):
    return bytes([(s >> 1) << 7 | (s & 1) << 6])


def blocks(n):
    """The hashing blocks of n words: blocks of 16, then powers of two."""
    out = []
    for k in (16, 8, 4, 2, 1):
        while n >= k:
            out.append(k)
            n -= k
            if k < 16:
                break
    return out


def leaf_words(kind, commit):
    """lambda (2 words), f' (12) if committed, d (2) for an addition."""
    return 2 + 12 * commit + 2 * (kind in ADDS)


class Prover:
    """The witness for the pairs (-A, B), (L, gamma), (C, delta); const is the Miller value of
    (alpha, beta)."""

    def __init__(self, gamma, delta, const):
        self.lines = [fixed_lines(gamma), fixed_lines(delta)]
        self.table = [poly.from_tower((bn254.W27 ** s * const).inv()) for s in range(3)]
        self.const = const

    def witness(self, pairs, inputs, residue=None, check=True):
        """The witness, or None if the product of the pairings is not 1.  Tests may give the residue
        witness (c, s) and seal without checking the relations (seal)."""
        (nA, B), (L, _), (C, _) = pairs
        res = residue or bn254.residue_witness(bn254.multi_miller_loop_affine(pairs) * self.const)
        if res is None:
            return None
        c, s = res
        ci = c.inv()
        lams = [lam for lam, _ in slopes(B)]
        lines = [[bn254.affine_line(cf, Pt) for _, cf in slopes(Q)] for Pt, Q in pairs]
        pts, T, f, fs, ds = step_points(B), B, ci, [], {}
        for i, kind in enumerate(STEPS): # the program's loop, from f = c^-1
            if kind == 'D':
                f = f.square()
            else:
                ds[i] = (pts[kind][0] - T[0]).inv()
                f = f * ci if kind == 'A+' else f * c if kind == 'A-' else f
            T, _ = bn254.affine_step(T, lams[i], pts[kind])
            for k in range(3):
                f = f.mul_by_034(*lines[k][i])
            fs.append(poly.from_tower(f) if COMMIT[i] else None)
        v = dict(P=nA, B=B, C=C, L=L, c=poly.from_tower(c), ci=poly.from_tower(ci), s=s, lam=lams, f=fs, d=ds)
        return self.seal(v, inputs, check)

    def seal(self, v, inputs, check=True):
        """The witness words of the values v: the committed words, then r, Q and z.  check=False lets a
        test seal values whose relations do not hold (Q is then S / M without its remainder)."""
        mont = lambda xs: [to_mont(x % P) for x in xs]
        fp2 = lambda a: mont([a.c0, a.c1])
        nA, B, C = v['P'], v['B'], v['C']
        w = dict(points=mont([nA[0], nA[1], B[0].c0, B[0].c1, B[1].c0, B[1].c1, C[0], C[1]]), c=mont(v['c']), ci=mont(v['ci']), s=v['s'],
                 leaves=[fp2(v['lam'][i]) + (mont(v['f'][i]) if COMMIT[i] else []) + (fp2(v['d'][i]) if i in v['d'] else [])
                         for i in range(N_STEPS)])
        t = wbytes(inputs) + wbytes(w['points']) + s_byte(v['s']) + wbytes(w['c'] + w['ci']) + b''.join(map(wbytes, w['leaves']))
        w['r'] = int.from_bytes(hashlib.sha256(t).digest(), 'big')
        q, rem = poly.divmod_m(horner(PolyRing, relations(PolyRing, v, self.lines, self.table), from_mont(w['r'])))
        ensure(not check or rem == [0] * 12, 'the relations do not hold')
        w['q'] = mont(q + [0] * (N_Q - len(q)))
        w['z'] = int.from_bytes(hashlib.sha256(wbytes([w['r']] + w['q'])).digest(), 'big')
        w['values'] = v
        return w


# ---------------------------------------------------------------------------------------------------
# The program
#
# The loop state is ((e, acc, x, y), h, run): e = f(z), acc the Horner sum of the relations so far,
# (x, y) = B's point at z, h the SHA-256 context of the transcript, and the run values below, computed
# once from z, r and the points.  zeta = z^6 - 9 is u at z; X, Y are the x, y of a point at zeta.
RUN = ([f'z{k}' for k in range(1, 12)] +
       ['zeta', 'z3zeta', 'nxpz', 'yp', 'xlz', 'xlzz', 'yl', 'xcz', 'xczz', 'yc', 'r', 'r2', 'r3', 'cz', 'ciz',
        'XB', 'YB', 'nYB', 'X1', 'Y1', 'X2', 'Y2'])
END = ['X3', 'Y3', 'pis', 'ts'] # computed in the setup, used at the end only
Q_KEYS = {'A+': ('XB', 'YB', 'ciz'), 'A-': ('XB', 'nYB', 'cz'), 'F1': ('X1', 'Y1'), 'F2': ('X2', 'Y2')}


class PairingCheck:
    """Generator of the check over a backend.  gamma, delta: the fixed G2 points; const: the Miller value
    of (alpha, beta); b: the bounds of the loop state (bounds())."""

    def __init__(self, fp, gamma, delta, const, b=None):
        self.fp, self.be, self.cv = fp, fp.be, Curve(fp)
        self.prover = Prover(gamma, delta, const)
        # per step, the line constants of gamma and delta: c3 and c4, two Montgomery words each
        self.data = [[to_mont(a % P) for k in (0, 1) for cf in self.prover.lines[k][i] for a in (cf.c0, cf.c1)]
                     for i in range(N_STEPS)]
        self.b = dict(b) if b is not None else {}
        if not self.b:
            ensure(not is_sym(self.be), 'the bounds are computed with the numeric backend')
            self.sample_bounds()
        be = self.be
        st = self.state_shape()
        self.steps = {}
        for kind, args in (('D', None), ('A', words(3)), ('F', words(2))):
            for commit in sorted({COMMIT[k] for k in range(N_STEPS) if STEPS[k][0] == kind}):
                shape = [[st, leaf_shape({'D': 'D', 'A': 'A+', 'F': 'F1'}[kind], commit)], words(8) if args is None else [args, words(8)]]
                name = f'STEP_{kind}' + ('' if commit else '_')
                self.steps[(kind, commit)] = be.function(name, shape, self.step_body(kind, commit))
        self.QCHUNK = be.function('QCHUNK', [[words(2), words(7)], words(8)], self.qchunk_body)
        if is_sym(be):
            self.costs = {fn.t: fn.c for fn in list(self.steps.values()) + [self.QCHUNK]}

    def one(self): return self.fp.const(1)
    def m1(self): return self.fp.const(P - 1)
    def rd(self, pairs): return self.fp.reduce_dot(pairs)

    # hashing and the committed words
    def top2_zero(self, w):
        """The word is below 2^254: its two top bits are 0.  Committed words are multiplied in long dot
        products, whose CRT bound a full 256-bit word would exceed."""
        be = self.be
        if not is_sym(be):
            ensure(w >> 254 == 0, 'committed word above 2^254')
            return 0
        return be.verify(be.not1(be.jet('or_1', be.sub(w, 'OOOOOOO', 2), 1)))

    def sha_init(self):
        be = self.be
        return be.jet('sha_256_ctx_8_init', be.unit(), SHA_CTX_W) if is_sym(be) else b''

    def sha_add(self, h, parts):
        """Absorb projections of 1, 2, 4, 8 or 16 words."""
        be = self.be
        if not is_sym(be):
            return h + b''.join(wbytes(flat(x)) for x in parts)
        for x in parts:
            x = be.subtree(x) if isinstance(x, list) else x
            h = be.jet(f'sha_256_ctx_8_add_{x.w // 8}', be.pair(h, x), SHA_CTX_W)
        return h

    def sha_byte(self, h, sel):
        """Absorb the byte (s1, s0, 0, 0, 0, 0, 0, 0)."""
        be = self.be
        if not is_sym(be):
            return h + s_byte(2 * sel[0] + sel[1])
        byte = be.pair(be.pair(be.pair(sel[0], sel[1]), be.const(2, 0)), be.const(4, 0))
        return be.jet('sha_256_ctx_8_add_1', be.pair(h, byte), SHA_CTX_W)

    def sha_final(self, h):
        be = self.be
        return be.jet('sha_256_ctx_8_finalize', h, 256) if is_sym(be) else int.from_bytes(hashlib.sha256(h).digest(), 'big')

    # one step
    def state_shape(self):
        return [words(4), E('', SHA_CTX_W, 0), words(len(RUN))]

    def step_body(self, kind, commit):
        """Body of a step function: ((state, leaf), args) -> state.  Evaluates lambda and the lines at z,
        and f' (a committed value at z, or the product), and adds the step's relations to acc in the
        order of `relations`; absorbs the leaf into h."""
        fp, be, b = self.fp, self.be, self.b
        rd, one, m1 = self.rd, self.one, self.m1
        add = kind != 'D'

        def body(accs):
            (st, leaf), args = accs
            (e, acc, x, y), h, run = st
            fw = flat(leaf[1]) if commit else []
            data = args if kind == 'D' else args[1]
            run = dict(zip(RUN, run))
            c = {'e': Val(e, b['e']), 'acc': Val(acc, b['acc']), 'x': Val(x, b['x']), 'y': Val(y, b['y']),
                 'l': [Val(w, WORD_MAX) for w in leaf[0]],
                 'dg': [Val(w, P - 1) for w in data[:4]], 'dd': [Val(w, P - 1) for w in data[4:]]}
            if commit:
                c['f'] = [Val(w, F_HI) for w in fw]
                c['zp'] = [Val(run[f'z{k}'], KB) for k in range(1, 12)]
            for nm in ('z3', 'zeta', 'z3zeta', 'nxpz', 'yp', 'xlz', 'xlzz', 'yl', 'xcz', 'xczz', 'yc', 'r') + (('r2',) if add or commit else ()) + (('r3',) if add and commit else ()):
                c[nm] = Val(run[nm], KB)
            if add:
                c['xq'], c['yq'] = Val(args[0][0], KB), Val(args[0][1], KB)
                c['d'] = [Val(w, WORD_MAX) for w in leaf[-1]]
                if kind == 'A':
                    c['g'] = Val(args[0][2], KB)
            at_zeta = lambda c, a: rd([(a[1], c['zeta']), (a[0], one())]) # a0 + a1 zeta

            def first(c):
                out = [at_zeta(c, c['l'])]
                if commit:
                    f = c['f']
                    out.append(fp.normalize(rd([(f[0], one())] + [(f[k], c['zp'][k - 1]) for k in range(1, 12)])))
                return out + ([at_zeta(c, c['d']), fp.sub(c['xq'], c['x'])] if add else [])
            minus_x3 = (lambda c: [(c['x'], m1()), (c['xq'], m1())]) if add else (lambda c: [(c['x'], fp.const(P - 2))])
            steps = [('let', ['lam'] + (['e2'] if commit else []) + (['dz', 'dx'] if add else []), first),
                     ('drop', ['l'] + (['f', 'zp'] if commit else []) + (['d'] if add else [])),
                     ('let', ['x2', 'm'], lambda c: [rd([(c['lam'], c['lam'])] + minus_x3(c)), rd([(c['lam'], c['x']), (c['y'], m1())])])]

            def final(c, _):
                lam, m, x2 = c['lam'], c['m'], c['x2']
                y2 = rd([(m, one()), (lam, fp.neg(x2))])
                lB = rd([(c['nxpz'], lam), (c['z3'], m), (c['yp'], one())])
                lg = rd([(c['yl'], one()), (c['xlz'], c['dg'][0]), (c['xlzz'], c['dg'][1]), (c['z3'], c['dg'][2]), (c['z3zeta'], c['dg'][3])])
                ld = rd([(c['yc'], one()), (c['xcz'], c['dd'][0]), (c['xczz'], c['dd'][1]), (c['z3'], c['dd'][2]), (c['z3zeta'], c['dd'][3])])
                if kind == 'D':
                    f2 = rd([(c['e'], c['e'])])
                    rels = [rd([(lam, c['y']), (c['x'], fp.mul_const(c['x'], -THREE_HALVES))])]
                else:
                    f2 = rd([(c['e'], c['g'])]) if kind == 'A' else c['e']
                    rels = [rd([(lam, c['dx']), (c['yq'], m1()), (c['y'], one())]), rd([(c['dx'], c['dz']), (one(), m1())])]
                prod = rd([(rd([(f2, lB)]), lg)]) # times l_delta below
                # Horner: acc r^n + the step's relations, the last one with weight 1
                r_pow = lambda j: one() if j == 0 else c['r' if j == 1 else f'r{j}']
                n = len(rels) + commit
                terms = [(c['acc'], r_pow(n))] + [(v, r_pow(n - 1 - k)) for k, v in enumerate(rels)]
                if commit:
                    acc2 = rd(terms + [(prod, ld), (c['e2'], m1())])
                    e2 = c['e2']
                else:
                    acc2 = rd(terms)
                    e2 = rd([(prod, ld)])
                outs = [e2, acc2, x2, y2]
                for nm, v in zip(('e', 'acc', 'x', 'y'), outs):
                    b[nm + '_out'] = max(b.get(nm + '_out', 0), v.hi)
                return fp.pack(outs)
            new = chain(fp, c, steps, final)
            h2 = self.sha_add(h, [leaf[0]] + ([leaf[1][0], leaf[1][1]] if commit else []) + ([leaf[-1]] if add else []))
            out = be.pack([new, h2, be.subtree(list(run.values()))])
            return be.seq(be.checks([self.top2_zero(w) for w in fw]), out) if commit else out
        return body

    def qchunk_body(self, accs):
        """Body of QCHUNK: ((qz, z^8), (z .. z^7)), 8 coefficients of Q -> qz z^8 + their polynomial at z.
        Q(z) is this step from the top chunk down; the coefficients are checked below 2^254."""
        ((qz, z8), zp), q = accs
        one, b = self.one(), self.b
        out = self.rd([(Val(qz, b['qz']), Val(z8, KB)), (Val(q[0], F_HI), one)] +
                      [(Val(q[k], F_HI), Val(zp[k - 1], KB)) for k in range(1, 8)])
        b['qz_out'] = max(b.get('qz_out', 0), out.hi)
        return self.be.seq(self.be.checks([self.top2_zero(w) for w in q]), out.e)

    def sample_bounds(self):
        """The bounds of the loop state: a fixed point of the step bodies, found on the numeric backend by
        widening the inputs (1% slack) until the outputs fit."""
        b = self.b
        b.update(e=KB, acc=KB, x=KB, y=KB, qz=KB)
        st = [[0] * 4, b'', [0] * len(RUN)]
        for _ in range(30):
            for nm in ('e', 'acc', 'x', 'y', 'qz'):
                b[nm + '_out'] = 0
            for kind, n_args in (('D', 0), ('A', 3), ('F', 2)):
                for commit in (False, True):
                    leaf = [[0, 0]] + ([[[0] * 8, [0] * 4]] if commit else []) + ([[0, 0]] if n_args else [])
                    self.step_body(kind, commit)([[st, leaf], [[0] * n_args, [0] * 8] if n_args else [0] * 8])
            self.qchunk_body([[[0, 0], [0] * 7], [0] * 8])
            names = ('e', 'acc', 'x', 'y', 'qz')
            if all(b[nm + '_out'] <= b[nm] for nm in names):
                return
            for nm in names:
                b[nm] = max(b[nm], b[nm + '_out'] * 101 // 100)
        raise RuntimeError('no fixed point for the loop bounds')

    # the loop
    def step_value(self, k, st, env):
        be = self.be
        kind = STEPS[k]
        data = [be.word(v) for v in self.data[k]]
        fn = self.steps[(kind[0], COMMIT[k])]
        if kind == 'D':
            return be.call(fn, [env, data])
        run = dict(zip(RUN, st[2]))
        args = [be.subtree(run[nm]) if is_sym(be) else run[nm] for nm in Q_KEYS[kind]]
        return be.call(fn, [env, [args, data]])

    def loop(self, state0, leaves):
        be = self.be
        if not is_sym(be):
            for k, leaf in enumerate(leaves):
                state0 = self.step_value(k, state0, [state0, leaf])
            return state0
        widths = [256 * leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS)]
        return be.comp(be.pair(state0, leaves), fold_leaves(be, self.state_shape(), widths,
                                                          lambda k: lambda accs: self.step_value(k, accs[0], be.iden())))

    # before the loop
    def setup(self, inputs, pts, c, ci, sel, rz):
        """((e, acc, x, y), h, run) and the END values.  Checks A, B, C on their curves and the words of
        c and c^-1, computes the run values, e = c^-1(z), acc = c c^-1 - 1 at z, and starts h with the
        public inputs, the points, s, c and c^-1."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, m1, lc = self.rd, self.one, self.m1, fp.lin_const
        p = [fp.normalize(Val(w, WORD_MAX)) for w in flat(pts)]
        z = lambda k: 'z' if k == 1 else f'z{k}'
        ctx = {'z': fp.normalize(Val(rz[1], WORD_MAX)), 'r': fp.normalize(Val(rz[0], WORD_MAX)), 'p': p,
               'xl': fp.normalize(inputs['L'][0]), 'yl': fp.normalize(inputs['L'][1]),
               'c': [Val(w, F_HI) for w in flat(c)], 'ci': [Val(w, F_HI) for w in flat(ci)], 'sel': [Val(s, 0) for s in sel]}

        def at_zeta_conj(c, a0, a1, g):
            """conj(a) g at zeta: a0 (g0 + g1 zeta) + a1 (g1 - g0 zeta)"""
            return rd([(a0, lc([(one(), g.c0), (c['zeta'], g.c1)])), (a1, lc([(one(), g.c1), (c['zeta'], -g.c0)]))])

        def at_z(coeffs, c):
            return rd([(coeffs[0], one())] + [(coeffs[k], c[z(k)]) for k in range(1, 12)])

        def frob_at_z(coeffs, n, c):
            """pi^n(a)(z) = sum_j a_j pi^n(w^j)(z); pi^n(w^j) has one or two terms"""
            return rd([(a, lc([((one() if k == 0 else c[z(k)]), g) for k, g in enumerate(poly.FROB[n][j]) if g]))
                       for j, a in enumerate(coeffs)])
        sq = lambda a: lambda c: rd([(c[a], c[a])])
        mu = lambda a, b: lambda c: rd([(c[a], c[b])])
        layers = [[('z2', sq('z'))], [('z3', mu('z2', 'z')), ('z4', sq('z2'))],
                  [('z5', mu('z4', 'z')), ('z6', sq('z3')), ('z7', mu('z4', 'z3')), ('z8', sq('z4'))],
                  [('z9', mu('z8', 'z')), ('z10', sq('z5')), ('z11', mu('z8', 'z3'))]]
        steps = [('let', [n for n, _ in L], (lambda L: lambda c: [f(c) for _, f in L])(L)) for L in layers] + [
            ('let', ['zeta', 'nz'], lambda c: [lc([(c['z6'], 1), (one(), -9)]), fp.mul_const(c['z'], -1)]),
            ('let', ['cz', 'ciz', 'r2'], lambda c: [fp.normalize(at_z(c['c'], c)), fp.normalize(at_z(c['ci'], c)), rd([(c['r'], c['r'])])]),
            ('let', ['xlz', 'xcz', 'XB', 'YB', 'r3', 'z3zeta'], lambda c: [
                rd([(c['xl'], c['z'])]), rd([(c['p'][6], c['z'])]), rd([(c['p'][2], one()), (c['p'][3], c['zeta'])]),
                rd([(c['p'][4], one()), (c['p'][5], c['zeta'])]), rd([(c['r2'], c['r'])]), rd([(c['z3'], c['zeta'])])])]
        end_hi = []

        def final(c, _):
            g1, g2, g3 = bn254.FROB1, bn254.FROB2, bn254.FROB3
            vals = {f'z{k}': c[z(k)] for k in range(1, 12)}
            vals.update({nm: c[nm] for nm in ('zeta', 'z3zeta', 'xlz', 'yl', 'xcz', 'r', 'r2', 'r3', 'cz', 'ciz', 'XB', 'YB')})
            vals.update(nxpz=rd([(c['p'][0], c['nz'])]), yp=c['p'][1], xlzz=rd([(c['xlz'], c['zeta'])]),
                        xczz=rd([(c['xcz'], c['zeta'])]), yc=c['p'][7], nYB=fp.mul_const(c['YB'], -1),
                        X1=at_zeta_conj(c, c['p'][2], c['p'][3], g1[2]), Y1=at_zeta_conj(c, c['p'][4], c['p'][5], g1[3]),
                        X2=fp.mul_const(c['XB'], g2[2].c0), Y2=fp.mul_const(c['YB'], -g2[3].c0))
            run = []
            for nm in RUN:
                v = vals[nm] if vals[nm].hi <= KB else fp.normalize(vals[nm])
                ensure(v.hi <= KB, f'run value bound: {nm}')
                run.append(v)
            start = [vals['ciz'], rd([(c['cz'], c['ciz']), (one(), m1())]), vals['XB'], vals['YB']]
            for nm, v in zip(('e', 'acc', 'x', 'y'), start):
                ensure(v.hi <= self.b[nm], f'initial bound: {nm}')
            pis = rd([(rd([(frob_at_z(c['ci'], 1, c), frob_at_z(c['c'], 2, c))]), frob_at_z(c['ci'], 3, c))])
            end = [at_zeta_conj(c, c['p'][2], c['p'][3], g3[2]), at_zeta_conj(c, c['p'][4], c['p'][5], -g3[3]),
                   pis, self.table_at_z([s.e for s in c['sel']], c)]
            end_hi.extend(v.hi for v in end)
            return be.pack([fp.pack([start, run]), fp.pack(end)])
        out = chain(fp, ctx, steps, final)
        self.end_hi = end_hi
        n = lambda w: fp.normalize(Val(w, WORD_MAX))
        pw = flat(pts)
        checks = [cv.g1_on_curve_check(n(pw[0]), n(pw[1])), cv.g2_on_curve_check((n(pw[2]), n(pw[3])), (n(pw[4]), n(pw[5]))),
                  cv.g1_on_curve_check(n(pw[6]), n(pw[7]))] + [self.top2_zero(w) for w in flat(c) + flat(ci)]
        h = self.sha_add(self.sha_init(), list(inputs['words']) + [pts])
        h = self.sha_add(self.sha_byte(h, sel), [c[0], c[1], ci[0], ci[1]])
        return be.seq(be.checks(checks), self._with_h(out, h))

    def _with_h(self, out, h):
        """((start, run), end) and h -> ((start, h, run), end)"""
        be = self.be
        if not is_sym(be):
            (start, run), end = out
            return [[start, h, run], end]
        shape = [[[words(4), words(len(RUN))], words(len(END))], E('', SHA_CTX_W, 0)]
        return be.with_env(be.pair(out, h), shape, lambda a: be.pack(
            [[be.subtree(a[0][0][0]), a[1], be.subtree(a[0][0][1])], be.subtree(a[0][1])]))

    def table_at_z(self, sel, c):
        """T_s(z): the row of constants selected by a case tree on the bits of s (s = 3 is rejected),
        times the powers of z."""
        be = self.be
        rows = [[to_mont(v) for v in row] for row in self.prover.table]
        zs = [c['z'] if k == 1 else c[f'z{k}'] for k in range(1, 12)]
        dot = lambda row, zz: self.rd([(row[0], self.one())] + [(row[k], zz[k - 1]) for k in range(1, 12)])
        if not is_sym(be):
            s = 2 * sel[0] + sel[1]
            ensure(s < 3, 'selector')
            return dot([Val(v, P - 1) for v in rows[s]], zs)
        leaf = lambda s: be.consts(256, rows[min(s, 2)])
        row = be.comp(be.pair(sel[0], be.pair(sel[1], be.unit())),
                      be.case(be.drop(be.case(leaf(0), leaf(1))), be.drop(be.case(leaf(2), leaf(3)))))
        row = be.seq(be.verify(be.not1(be.and1(sel[0], sel[1]))), row)
        hi = []

        def body(a):
            v = dot([Val(w, P - 1) for w in be.split(a[0], words(12))], [Val(w, KB) for w in a[1]])
            hi.append(v.hi)
            return v.e
        e = be.scope([row, [v.e for v in zs]], body)
        return Val(e, hi[0])

    # after the loop
    def final(self, state, end, q, rz):
        """The last three relations, S(z) = Q(z) M(z), and r, z against the two hashes."""
        fp, be, cv = self.fp, self.be, self.cv
        rd, one, m1 = self.rd, self.one, self.m1
        (e, acc, x, y), h, run = state
        run = {nm: Val(w, KB) for nm, w in zip(RUN, run)}
        b = self.b
        chunks = [half for blk in q for half in ([blk] if len(blk) == 8 else [blk[:8], blk[8:]])]
        ensure(len(blocks(N_Q)) == len(q) and all(len(ch) == 8 for ch in chunks), 'Q is read in chunks of 8 words')
        qz = be.word(0)
        for ch in reversed(chunks):
            zs = [run[f'z{k}'].e for k in range(1, 8)]
            qz = be.call(self.QCHUNK, [[[qz, run['z8'].e], zs], be.subtree(ch) if is_sym(be) else ch])
        c = {'e': Val(e, b['e']), 'acc': Val(acc, b['acc']), 'x': Val(x, b['x']), 'y': Val(y, b['y']), 'qz': Val(qz, b['qz'])}
        c.update({nm: Val(w, hi) for nm, w, hi in zip(END, end, self.end_hi)})
        c.update({nm: run[nm] for nm in ('r', 'r2', 'r3', 'z6')})

        def horner_end(c):
            g2 = rd([(c['x'], c['r2']), (c['X3'], fp.mul_const(c['r2'], -1)), (c['y'], c['r']), (c['Y3'], fp.mul_const(c['r'], -1))])
            return rd([(c['acc'], c['r3']), (g2, one()), (c['e'], c['pis']), (c['ts'], m1())])

        steps = [('let', ['s', 'z12'], lambda c: [horner_end(c), rd([(c['z6'], c['z6'])])]),
                 ('drop', ['acc', 'x', 'y', 'e', 'r', 'r2', 'r3'] + END)]

        def check(c, _):
            minus_m = fp.lin_const([(c['z12'], -1), (c['z6'], 18), (one(), -82)])
            return cv.zero_check(rd([(c['s'], one()), (c['qz'], minus_m)])).e
        identity = chain(fp, c, steps, check)
        r_hash = self.sha_final(h)
        z_hash = self.sha_final(self.sha_add(self.sha_add(self.sha_init(), [rz[0]]), list(q)))
        if not is_sym(be):
            ensure(r_hash == rz[0] and z_hash == rz[1], 'challenge')
            return 0
        return be.checks([identity, be.verify(be.eq256(r_hash, rz[0])), be.verify(be.eq256(z_hash, rz[1]))])

    def program(self, inputs, pts, c, ci, sel, rz, leaves, q):
        """The whole check.  inputs: {'L': (x, y) Vals, 'words': the public input accessors}; the rest as
        in witness_shape().  Sym: a unit-typed E over the environment; Num: runs the checks."""
        be = self.be
        s0 = self.setup(inputs, pts, c, ci, sel, rz)
        if not is_sym(be):
            st0, end = s0
            return self.final(self.loop(st0, leaves), end, q, rz)
        lw = sum(256 * leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS))
        qshape = [words(n) for n in blocks(N_Q)]
        parts = {}

        def body(a):
            (st0, end), (lv, (qa, rza)) = a
            st = self.loop(be.subtree(st0), lv)
            out = be.with_env(be.pack([st, be.subtree(end), be.subtree(qa), be.subtree(rza)]),
                              [self.state_shape(), words(len(END)), qshape, words(2)], lambda a: self.final(*a))
            parts.update(loop=st.c, final=out.c - st.c)
            return out
        out = be.with_env(be.pack([s0, [be.subtree(leaves), [be.subtree(q), be.subtree(rz)]]]),
                          [[self.state_shape(), words(len(END))], [E('', lw, 0), [qshape, words(2)]]], body)
        self.parts = {'setup': s0.c, **parts}
        return out


def fold_leaves(be, state_shape, widths, step):
    """Fold a state over the leaves of a balanced tree, of the given widths (as curve.fold_tree)."""
    state_w = sum(e.w for e in flat(state_shape))

    def go(lo, hi):
        if hi - lo == 1:
            be._push_env(state_w + widths[lo])
            try:
                return step(lo)((be._unpack('O', state_shape), be.proj('IH', widths[lo])))
            finally:
                be._pop_env()
        mid = lo + (hi - lo + 1) // 2
        inner = be.comp(be.pair(be.proj('OH', state_w), be.proj('IOH', sum(widths[lo:mid]))), go(lo, mid))
        return be.comp(be.pair(inner, be.proj('IIH', sum(widths[mid:hi]))), go(mid, hi))
    return go(0, len(widths))


_BOUNDS = None


def bounds():
    """The bounds of the loop state (they depend on the structure only), computed once."""
    global _BOUNDS
    if _BOUNDS is None:
        G = bn254.G2_GEN
        _BOUNDS = PairingCheck(Fp(Num()), G, G, bn254.Fp12.one()).b
    return _BOUNDS


# ---------------------------------------------------------------------------------------------------
# The witness of the check: ((points, (c, c^-1)), ((s, (r, z)), (leaves, Q))).  c, c^-1: 8 + 4 words;
# a leaf: (lambda, (f' 8 + 4 words)) or ((lambda, f'), d); Q in hashing blocks.
def leaf_shape(kind, commit):
    """(lambda, f', d): f' (8 + 4 words) if committed, d for an addition."""
    return [words(2)] + ([[words(8), words(4)]] if commit else []) + ([words(2)] if kind in ADDS else [])


def witness_shape():
    bit = lambda: E('', 1, 0)
    c = lambda: [words(8), words(4)]
    leaves = [leaf_shape(kind, COMMIT[k]) for k, kind in enumerate(STEPS)]
    return [[words(8), [c(), c()]], [[[bit(), bit()], words(2)], [leaves, [words(n) for n in blocks(N_Q)]]]]


def witness_type():
    T = lambda n: Tbalanced(['2^256'] * n)
    c = f'({T(8)} * {T(4)})'
    leaf = lambda kind, commit: Tbalanced([T(2)] + ([c] if commit else []) + ([T(2)] if kind in ADDS else []))
    leaves = Tbalanced([leaf(kind, COMMIT[k]) for k, kind in enumerate(STEPS)])
    return f'(({T(8)} * ({c} * {c})) * (((2 * 2) * {T(2)}) * ({leaves} * {Tbalanced([T(n) for n in blocks(N_Q)])})))'


def witness_bits():
    return 256 * (8 + 24 + 2 + N_Q + sum(leaf_words(kind, COMMIT[k]) for k, kind in enumerate(STEPS))) + 2


def _split(w):
    def leaf(k, lf):
        parts = [lf[:2]]
        if COMMIT[k]:
            parts.append([lf[2:10], lf[10:14]])
        return parts + ([lf[-2:]] if STEPS[k] in ADDS else [])
    qs, i = [], 0
    for n in blocks(N_Q):
        qs.append(w['q'][i:i + n])
        i += n
    return w['points'], [w['c'][:8], w['c'][8:]], [w['ci'][:8], w['ci'][8:]], [leaf(k, lf) for k, lf in enumerate(w['leaves'])], qs


def witness_num(w):
    """The witness as the nested value the numeric backend takes."""
    pts, c, ci, leaves, qs = _split(w)
    return [[pts, [c, ci]], [[[w['s'] >> 1, w['s'] & 1], [w['r'], w['z']]], [leaves, qs]]]


def witness_value(w):
    """The witness as a harness value spec (tools/harness)."""
    pts, c, ci, leaves, qs = _split(w)
    W = lambda ws: wbalanced([wv(256, x) for x in ws])
    pair2 = lambda a: wpair(W(a[0]), W(a[1]))
    leaf = lambda lf: balanced([W(lf[0])] + [pair2(x) if len(x) == 2 and isinstance(x[0], list) else W(x) for x in lf[1:]], wpair)
    return wpair(wpair(W(pts), wpair(pair2(c), pair2(ci))),
                 wpair(wpair(wpair(wbit(w['s'] >> 1), wbit(w['s'] & 1)), W([w['r'], w['z']])),
                       wpair(wbalanced([leaf(lf) for lf in leaves]), wbalanced([W(x) for x in qs]))))
