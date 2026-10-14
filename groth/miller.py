"""The Miller loop of the three pairs (A, B), (L, gamma), (C, delta).

The loop runs along the NAF of 6x + 2, then does the two Frobenius additions; the three pairs advance in
lockstep, so f is squared once per iteration.  B is the only variable G2 point: its steps use hinted
slopes (curve.py) and its lines are computed.  gamma and delta are fixed, so their slopes and line
coefficients are constants of the program, passed to each iteration as data.

An iteration multiplies f^2 (or f) by three lines yP + (-lambda xP) w + (lambda xT - yT) v w, each given
as the 13 words the tower product needs (c0, and the variants of c3 and c4).  B's line comes out of the
B step; for a fixed pair the c3 variants are -xP times data constants and the c4 variants are data words.
The lines are multiplied in the order B, gamma, delta, so that the loosest one (B's) meets the smallest
f, and f is normalised once per iteration.

The loop folds the state (f, T, K) over the balanced tree of hints (one leaf per step: a slope, two
words).  Every iteration is a call of a shared function, built from shared functions for the squaring,
the line products and the B step; each body appears once in the program.  K holds the per-proof words
(-xA, yA, -xL, yL, -xC, yC, B, -yB, normalised).

With residue=True the loop also raises the residue witness c to the power -(6x + 2): f starts as c^-1,
and each addition step multiplies it by c^-1 (digit +1) or c (digit -1).  The final check (pairing.py)
then needs no exponentiation.  c and c^-1 are checked once (c c^-1 = 1) and carried in K.
"""
from . import bn254
from .dsl import ensure
from .fp import Fp, Val, P, P_SECP, N_SECP, C1, C3, C23, to_mont, WORD_MAX
from .sym import Num, words, is_sym
from .tower import Tower, let_masked
from .curve import Curve, chain, fold_tree


def loop_steps():
    """The steps along the NAF of 6x + 2: 'D' doubling, 'A+' / 'A-' addition of +-Q, then the Frobenius
    additions 'F1' (pi(Q)) and 'F2' (-pi^2(Q))."""
    digits = bn254.ATE_NAF
    steps = []
    for i in range(len(digits) - 2, -1, -1):
        steps.append('D')
        if digits[i]:
            steps.append('A+' if digits[i] > 0 else 'A-')
    return steps + ['F1', 'F2']


STEPS = loop_steps() # 88 steps: 65 doublings, 8 + 13 additions, 2 Frobenius additions
N_STEPS = len(STEPS)

# the 12 variant words of a line after c0, as (variant, basis index)
LINE_KEYS = [('1', 6), ('1', 7), ('neg', 7), ('xi', 6), ('xi', 7), ('xineg', 7),
             ('1', 8), ('1', 9), ('neg', 9), ('xi', 8), ('xi', 9), ('xineg', 9)]


# generation time and prover side: plain Python on bn254 points
def step_points(Q):
    """The point added at each kind of step, for the G2 point Q."""
    Q1 = bn254.g2_frobenius(Q)
    return {'D': None, 'A+': Q, 'A-': bn254.g2_neg(Q), 'F1': Q1, 'F2': bn254.g2_neg(bn254.g2_frobenius(Q1))}


def slopes(Q):
    """(lambda, (c3, c4)) of every step for the G2 point Q: the hints of B, or the constants of a fixed
    pair.  Same order as bn254.multi_miller_loop_affine."""
    pts = step_points(Q)
    T = Q
    out = []
    for kind in STEPS:
        Qk = pts[kind]
        lam = bn254.affine_double_slope(T) if Qk is None else bn254.affine_add_slope(T, Qk)
        T, coeffs = bn254.affine_step(T, lam, Qk)
        out.append((lam, coeffs))
    return out


def folded(k):
    """The two words that fold the field constant k into a reduction, as fp.mul_const does, but read
    from the environment: ([k] C1 mod p_s, [k] C3 mod n_s) with [k] the Montgomery form."""
    c = to_mont(k % P)
    return [c * C1 % P_SECP, c * C3 % N_SECP]


def line_data(lam, c4):
    """The 18 data words of a fixed line with slope lam and c4 = lam xT - yT: 12 folded constants that
    make the c3 variants from -xP, then the 6 Montgomery words of the c4 variants."""
    xl, xc = lam.mul_by_xi(), c4.mul_by_xi()
    words = []
    for k in (lam.c0, lam.c1, -lam.c1, xl.c0, xl.c1, -xl.c1):
        words += folded(k)
    return words + [to_mont(v % P) for v in (c4.c0, c4.c1, -c4.c1, xc.c0, xc.c1, -xc.c1)]


def fixed_line_data(Q):
    """The data words of each step's line, for the fixed G2 point Q."""
    return [line_data(lam, c4) for lam, (c3, c4) in slopes(Q)]


def hint_words(Q):
    """B's hints: per step, the slope as two Montgomery words."""
    return [[to_mont(lam.c0), to_mont(lam.c1)] for lam, _ in slopes(Q)]


# generator helpers
def line_variants(c0, words):
    """The variant lists of a line (the right operand) from c0 and its 12 variant words."""
    out = {k: [None] * 12 for k in ('1', 'neg', 'xi', 'xineg')}
    out['1'][0] = c0
    for (k, j), v in zip(LINE_KEYS, words):
        out[k][j] = v
    return out


def mul_data_hi(a_hi, c_hi=P - 1):
    return (a_hi * c_hi + (P_SECP - 1) * P) // P_SECP


def mul_data(fp, a, w, c_hi=P - 1):
    """fp.mul_const with the constant read from the environment as its folded words w (see `folded`);
    the constant's Montgomery word is below c_hi."""
    be = fp.be
    hi = mul_data_hi(a.hi, c_hi)
    ensure(hi < N_SECP, 'reduced bound exceeds n_s')

    def body(v):
        m = be.fe_mul(v[0].e, w[0])
        return be.sc_add(be.sc_mul(v[0].e, w[1]), be.sc_mul(m, be.word(C23)))
    return Val(be.check(fp.once([a], body), hi), hi)


def normalize_hi(hi):
    """The bound of fp.normalize on a value bounded by hi."""
    return (hi * to_mont(1) + (P_SECP - 1) * P) // P_SECP


K_HI = normalize_hi(normalize_hi(WORD_MAX)) # bound of the per-proof words (normalised twice)


class Miller:
    """Generator of the loop over a backend; gamma, delta are the fixed G2 points.  The static bounds of
    the shared functions (self.b) are found once with the numeric backend (`bounds()`) and checked by
    the symbolic build."""

    def __init__(self, fp, gamma, delta, b=None, n_steps=N_STEPS, residue=False):
        self.fp, self.be = fp, fp.be
        self.tw, self.cv = Tower(fp), Curve(fp)
        self.fixed = [fixed_line_data(gamma), fixed_line_data(delta)]
        self.n_steps = n_steps # a prefix of the loop, for tests
        self.residue = residue
        self.k_shape = [words(12), words(12), words(12)] if residue else words(12) # K: the point words, then c, c^-1
        self.costs = {}
        self.b = dict(b) if b is not None else {}
        if not self.b:
            ensure(not is_sym(self.be), 'the bounds are computed with the numeric backend')
            self.sample_bounds()
        self.build()

    def g2_steps(self, add):
        """The B step as chain steps.  ctx: 'x', 'y' (T), 'lam' (the hint), 'nxa' (-xA), and for an
        addition 'qx', 'qy'.  Results: 'x2', 'y2', 'c3' = lambda (-xA), 'c4' = lambda xT - yT
        (normalised), their xi-copies 'c3xi', 'c4xi', and 'lam' (normalised).  As in the MSM, plain terms
        are products with the Montgomery constants [-1] and [1]."""
        fp, cv = self.fp, self.cv
        m1 = lambda: fp.const(P - 1)
        one = lambda: fp.const(1)
        steps = [('let', ['lam'], lambda c: [cv.norm2(c['lam'])])]
        if add:
            steps += [
                # lambda (xQ - xT) = yQ - yT as two zero dots, with xQ != xT
                ('let', ['nly', 'dx'], lambda c: [fp.mul_const(c['lam'][1], -1), cv.sub2(c['qx'], c['x'])]),
                ('check', lambda c: cv.neq2_check(c['qx'], c['x'])),
                ('check', lambda c: [cv.zero_check(fp.reduce_dot([(c['lam'][0], c['dx'][0]), (c['nly'], c['dx'][1]), (c['qy'][0], m1()), (c['y'][0], one())])),
                                     cv.zero_check(fp.reduce_dot([(c['lam'][0], c['dx'][1]), (c['lam'][1], c['dx'][0]), (c['qy'][1], m1()), (c['y'][1], one())]))]),
                ('drop', ['dx', 'qy']),
            ]
            x3 = lambda c: c['qx'] # the third x of x2 = lambda^2 - xT - xQ
        else:
            steps += [
                # lambda yT = (3/2) xT^2 as two zero dots: lambda_x y_x - lambda_y y_y - (3/2)(x_x^2 - x_y^2),
                # lambda_x y_y + lambda_y y_x - 3 x_x x_y
                ('let', ['nly', 'mxx', 'hxy'], lambda c: [fp.mul_const(c['lam'][1], -1), fp.mul_const(c['x'][0], -3 * pow(2, -1, P)), fp.mul_const(c['x'][1], 3 * pow(2, -1, P))]),
                ('check', lambda c: [cv.zero_check(fp.reduce_dot([(c['lam'][0], c['y'][0]), (c['nly'], c['y'][1]), (c['mxx'], c['x'][0]), (c['hxy'], c['x'][1])])),
                                     cv.zero_check(fp.reduce_dot([(c['lam'][0], c['y'][1]), (c['lam'][1], c['y'][0]), (c['mxx'], fp.double(c['x'][1]))]))]),
                ('drop', ['mxx', 'hxy']),
            ]
            x3 = lambda c: c['x']
        steps += [
            # x2 = lambda^2 - xT - x3, c4 = lambda xT - yT (normalised: it is a line coefficient)
            ('let', ['x2', 'c4'], lambda c: [
                (fp.reduce_dot([(c['lam'][0], c['lam'][0]), (c['lam'][1], c['nly']), (c['x'][0], m1()), (x3(c)[0], m1())]),
                 fp.reduce_dot([(fp.double(c['lam'][0]), c['lam'][1]), (c['x'][1], m1()), (x3(c)[1], m1())])),
                (fp.normalize(fp.reduce_dot([(c['lam'][0], c['x'][0]), (c['nly'], c['x'][1]), (c['y'][0], m1())])),
                 fp.normalize(fp.reduce_dot([(c['lam'][0], c['x'][1]), (c['lam'][1], c['x'][0]), (c['y'][1], m1())])))]),
            ('drop', ['x', 'y', 'nly'] + (['qx'] if add else [])),
            # y2 = c4 - lambda x2, c3 = lambda (-xA)
            ('let', ['y2', 'c3'], lambda c: [
                (fp.reduce_dot([(c['c4'][0], one()), (c['lam'][1], c['x2'][1]), (c['lam'][0], fp.neg(c['x2'][0]))]),
                 fp.reduce_dot([(c['c4'][1], one()), (c['lam'][0], fp.neg(c['x2'][1])), (c['lam'][1], fp.neg(c['x2'][0]))])),
                (fp.reduce_dot([(c['lam'][0], c['nxa'])]), fp.reduce_dot([(c['lam'][1], c['nxa'])]))]),
            ('drop', ['lam', 'nxa']),
            ('let', ['c3xi', 'c4xi'], lambda c: [self.tw.xi_copy(*c['c3']), self.tw.xi_copy(*c['c4'])]),
        ]
        return steps

    def bstep_body(self, add):
        """Body of BSTEP_DBL / BSTEP_ADD: (T, lambda, -xA[, Q]) -> (T', the 12 line words), checks
        executed.  Records the bounds of T' and of the line words in self.b."""
        fp, be, b = self.fp, self.be, self.b

        def body(accs):
            T, lam, nxa = accs[:3]
            ctx = {'x': (Val(T[0], b['tx']), Val(T[1], b['tx'])), 'y': (Val(T[2], b['ty']), Val(T[3], b['ty'])),
                   'lam': (Val(lam[0], WORD_MAX), Val(lam[1], WORD_MAX)), 'nxa': Val(nxa, K_HI)}
            if add:
                Q = accs[3]
                ctx['qx'], ctx['qy'] = (Val(Q[0], b['q']), Val(Q[1], b['q'])), (Val(Q[2], b['q']), Val(Q[3], b['q']))

            def final(c, checks):
                c3, c4, c3xi, c4xi = c['c3'], c['c4'], c['c3xi'], c['c4xi']
                line = [c3[0], c3[1], fp.mul_const(c3[1], -1), c3xi[0], c3xi[1], fp.mul_const(c3xi[1], -1),
                        c4[0], c4[1], fp.mul_const(c4[1], -1), c4xi[0], c4xi[1], fp.mul_const(c4xi[1], -1)]
                x2, y2 = c['x2'], c['y2']
                b['tx_out'] = max(b.get('tx_out', 0), x2[0].hi, x2[1].hi)
                b['ty_out'] = max(b.get('ty_out', 0), y2[0].hi, y2[1].hi)
                b['line'] = [max(h, v.hi) for h, v in zip(b.get('line', [0] * 12), line)]
                return be.seq(be.checks([v.e for v in checks]), fp.pack([[x2[0], x2[1], y2[0], y2[1]], line]))
            return chain(fp, ctx, self.g2_steps(add), final)
        return body

    def sqrn_body(self, accs):
        """Body of SQRN: f -> normalised f^2.  The variants of f are bound in two layers (the negated
        xi-copies need the xi-copies), so nothing is computed twice."""
        fp, tw, b = self.fp, self.tw, self.b
        f = [Val(a, b['f']) for a in accs]
        need = tw.needed(f, f, symmetric=True)
        nb = need['B']
        dbl = [fp.double(f[j]) if j in need['A']['2'] else None for j in range(12)]
        neg = [fp.mul_const(f[j], -1) if j in nb['neg'] else None for j in range(12)]
        xi = [None] * 12
        for j in sorted(nb['xi'] | nb['xineg']):
            j0 = j - j % 2
            if xi[j0] is None:
                xi[j0], xi[j0 + 1] = tw.xi_copy(f[j0], f[j0 + 1])
        xi = [xi[j] if (j in nb['xi'] or j in nb['xineg']) else None for j in range(12)]

        def inner(v, lift):
            dbl2, neg2, xi2 = v
            f2 = [lift(x) for x in f]
            xineg = [fp.mul_const(x, -1) if (x is not None and j in nb['xineg']) else None for j, x in enumerate(xi2)]

            def inner2(v2, lift2):
                lift_all = lambda l: [lift2(x) if x is not None else None for x in l]
                A = {'1': lift_all(f2), '2': lift_all(dbl2), 'neg': lift_all(neg2), 'xi': lift_all(xi2), 'xineg': v2[0]}
                C = [fp.normalize(c) for c in tw.mul(A, A, symmetric=True)]
                b['sqrn'] = [c.hi for c in C]
                return fp.pack(C)
            return let_masked(fp, [xineg], inner2)
        return let_masked(fp, [dbl, neg, xi], inner)

    def dmuln_body(self, accs):
        """Body of DMULN: (g, f) -> normalised g f, for a per-proof g (left operand) and the accumulator f
        (right operand, whose variants are bound in two layers)."""
        fp, tw, b = self.fp, self.tw, self.b
        g_accs, f_accs = accs
        g = [Val(a, b['dm_g']) for a in g_accs]
        f = [Val(a, b['f']) for a in f_accs]
        nb = tw.needed(g, f)['B']
        neg = [fp.mul_const(f[j], -1) if j in nb['neg'] else None for j in range(12)]
        xi = [None] * 12
        for j in sorted(nb['xi'] | nb['xineg']):
            j0 = j - j % 2
            if xi[j0] is None:
                xi[j0], xi[j0 + 1] = tw.xi_copy(f[j0], f[j0 + 1])
        xi = [xi[j] if (j in nb['xi'] or j in nb['xineg']) else None for j in range(12)]

        def inner(v, lift):
            neg2, xi2 = v
            g2, f2 = [lift(x) for x in g], [lift(x) for x in f]
            xineg = [fp.mul_const(x, -1) if (x is not None and j in nb['xineg']) else None for j, x in enumerate(xi2)]

            def inner2(v2, lift2):
                lift_all = lambda l: [lift2(x) if x is not None else None for x in l]
                B = {'1': lift_all(f2), 'neg': lift_all(neg2), 'xi': lift_all(xi2), 'xineg': v2[0]}
                C = [fp.normalize(c) for c in tw.mul({'1': lift_all(g2)}, B)]
                b['dmuln'] = [c.hi for c in C]
                return fp.pack(C)
            return let_masked(fp, [xineg], inner2)
        return let_masked(fp, [neg, xi], inner)

    def lm_body(self, name, f_hi, line_hi, normalize):
        """Body of a line product: (f, (c0, 12 line words)) -> f * line, normalised if asked.  Records the
        output bounds under `name`."""
        fp, tw, b = self.fp, self.tw, self.b

        def body(accs):
            f_accs, (c0, ws) = accs
            f = [Val(a, h) for a, h in zip(f_accs, f_hi)]
            line = line_variants(Val(c0, line_hi[0]), [Val(w, h) for w, h in zip(ws, line_hi[1:])])
            C = tw.mul({'1': f}, line)
            if normalize:
                C = [fp.normalize(c) for c in C]
            b[name] = [c.hi for c in C]
            return fp.pack(C)
        return body

    def iter_body(self, kind):
        """Body of an iteration, (state, leaf) and the step's inputs -> state.  kind: 'D' squaring and
        doubling; 'D0' doubling without squaring (f = 1); 'F' addition of Q; 'A' addition of Q, after
        the product with g = c or c^-1."""
        be = self.be

        def body(accs):
            (st, leaf), rest = accs
            f, T, K = st
            Kp = K[0] if self.residue else K # the point words of K
            Q, g, data = rest if kind == 'A' else (rest[0], None, rest[1]) if kind == 'F' else (None, None, rest)
            s1 = be.call(self.BSTEP_DBL, [T, leaf, Kp[0]]) if kind in ('D', 'D0') else be.call(self.BSTEP_ADD, [T, leaf, Kp[0], Q])
            fin = be.call(self.DMULN, [be.subtree(g), be.subtree(f)]) if kind == 'A' else be.subtree(f)

            def stage2(v):
                s1v, fv, Kv, dv = v
                T2, line12 = be.sub(s1v, 'O', 4 * 256), be.sub(s1v, 'I', 12 * 256)
                f0 = be.call(self.SQRN, [fv]) if kind == 'D' else fv
                Kw = be.split(Kv, self.k_shape)
                Kw = Kw[0] if self.residue else Kw
                f1 = be.call(self.LM1, [f0, [Kw[1], line12]])
                f2 = be.call(self.LM2, [f1, self.fixed_line(Kw[2], Kw[3], be.split(be.sub(dv, 'O', 18 * 256), words(18)))])
                f3 = be.call(self.LMN, [f2, self.fixed_line(Kw[4], Kw[5], be.split(be.sub(dv, 'I', 18 * 256), words(18)))])
                return be.pack([f3, T2, Kv])
            return be.scope([s1, fin, be.subtree(K), be.subtree(data)], stage2)
        return body

    def fixed_line(self, nxp, yp, d):
        """The 13-word line of a fixed pair from -xP, yP and the 18 data words."""
        a = Val(nxp, K_HI)
        return [yp, [mul_data(self.fp, a, (d[2 * i], d[2 * i + 1])).e for i in range(6)] + list(d[12:])]

    def sample_bounds(self):
        """Find the static bounds by running the bodies on sample inputs with the numeric backend.  The
        bounds of T and f are fixed points of one step / one iteration."""
        b = self.b
        G = bn254.G2_GEN
        G2 = bn254.g2_add(G, G)
        w = lambda pt: [to_mont(pt[0].c0), to_mont(pt[0].c1), to_mont(pt[1].c0), to_mont(pt[1].c1)]
        w2 = lambda v: [to_mont(v.c0), to_mont(v.c1)]
        K = [to_mont(1)] * 12
        b['q'] = K_HI
        for kind in ('F1', 'F2'):
            b['q'] = max([b['q']] + [v.hi for v in self._step_point_vals(kind, K)])
        # approach the fixed points from below, with 1% slack so that a few rounds suffice
        b['tx'] = b['ty'] = K_HI
        for _ in range(20):
            b['tx_out'] = b['ty_out'] = 0
            b['line'] = [0] * 12
            self.bstep_body(False)([w(G), w2(bn254.affine_double_slope(G)), to_mont(1)])
            self.bstep_body(True)([w(G), w2(bn254.affine_add_slope(G, G2)), to_mont(1), w(G2)])
            if b['tx_out'] <= b['tx'] and b['ty_out'] <= b['ty']:
                break
            b['tx'], b['ty'] = max(b['tx'], b['tx_out'] * 101 // 100), max(b['ty'], b['ty_out'] * 101 // 100)
        else:
            raise RuntimeError('no fixed point for the bounds of T')
        # the left operand of DMULN: a K word or its Frobenius image
        fr = self.tw.frobenius([Val(0, K_HI)] * 12, 1, tight_neg=True)
        b['dm_g'] = max([K_HI, mul_data_hi(K_HI)] + [normalize_hi(v.hi) for v in fr])
        b['f'] = to_mont(1)
        fixed_hi = [K_HI] + [mul_data_hi(K_HI)] * 6 + [P - 1] * 6
        for _ in range(20):
            self.sqrn_body([0] * 12)
            self.dmuln_body([[0] * 12, [0] * 12])
            b['lm1_in'] = [max(x, y) for x, y in zip(b['sqrn'], b['dmuln'])]
            self.lm_body('lm1', b['lm1_in'], [K_HI] + b['line'], False)([[0] * 12, [0, [0] * 12]])
            self.lm_body('lm2', b['lm1'], fixed_hi, False)([[0] * 12, [0, [0] * 12]])
            self.lm_body('lmn', b['lm2'], fixed_hi, True)([[0] * 12, [0, [0] * 12]])
            out = max(b['lmn'])
            if out <= b['f']:
                break
            b['f'] = out * 101 // 100
        else:
            raise RuntimeError('no fixed point for the bound of f')

    def build(self):
        """Define the shared functions."""
        be, b = self.be, self.b
        W = lambda: words(1)[0]
        self.BSTEP_DBL = be.function('BSTEP_DBL', [words(4), words(2), W()], self.bstep_body(False))
        self.BSTEP_ADD = be.function('BSTEP_ADD', [words(4), words(2), W(), words(4)], self.bstep_body(True))
        self.SQRN = be.function('SQRN', words(12), self.sqrn_body)
        self.DMULN = be.function('DMULN', [words(12), words(12)], self.dmuln_body) if self.residue else None
        fixed_hi = [K_HI] + [mul_data_hi(K_HI)] * 6 + [P - 1] * 6
        self.LM1 = be.function('LM1', [words(12), [W(), words(12)]], self.lm_body('lm1', b['lm1_in'], [K_HI] + b['line'], False))
        self.LM2 = be.function('LM2', [words(12), [W(), words(12)]], self.lm_body('lm2', b['lm1'], fixed_hi, False))
        self.LMN = be.function('LMN', [words(12), [W(), words(12)]], self.lm_body('lmn', b['lm2'], fixed_hi, True))
        if is_sym(be):
            ensure(b['tx_out'] <= b['tx'] and b['ty_out'] <= b['ty'] and max(b['lmn']) <= b['f'] and max(b['sqrn']) <= b['f'],
                   'the loop bounds are not a fixed point')
            ensure(not self.residue or max(b['dmuln']) <= b['f'], 'the loop bounds are not a fixed point')
        state = [words(12), words(4), self.k_shape]
        leaf = words(2)
        data = [words(18), words(18)]
        self.ITER_D = be.function('ITER_D', [[state, leaf], data], self.iter_body('D'))
        self.ITER_F = be.function('ITER_F', [[state, leaf], [words(4), data]], self.iter_body('F'))
        if self.residue:
            self.ITER_A = be.function('ITER_A', [[state, leaf], [words(4), words(12), data]], self.iter_body('A'))
            fns = (self.BSTEP_DBL, self.BSTEP_ADD, self.SQRN, self.DMULN, self.LM1, self.LM2, self.LMN, self.ITER_D, self.ITER_F, self.ITER_A)
        else:
            self.ITER_D0 = be.function('ITER_D0', [[state, leaf], data], self.iter_body('D0'))
            fns = (self.BSTEP_DBL, self.BSTEP_ADD, self.SQRN, self.LM1, self.LM2, self.LMN, self.ITER_D0, self.ITER_D, self.ITER_F)
        if is_sym(be):
            for fn in fns:
                self.costs[fn.t] = fn.c

    # the loop
    def _step_point_vals(self, kind, K):
        """The point added at a step, from the K accessors: +-B, pi(B) or -pi^2(B) (normalised)."""
        fp, tw = self.fp, self.tw
        xB, yB = (Val(K[6], K_HI), Val(K[7], K_HI)), (Val(K[8], K_HI), Val(K[9], K_HI))
        if kind == 'A+':
            return [Val(K[i], K_HI) for i in (6, 7, 8, 9)]
        if kind == 'A-':
            return [Val(K[i], K_HI) for i in (6, 7, 10, 11)]
        if kind == 'F1':
            g2, g3 = bn254.FROB1[2], bn254.FROB1[3]
            return [fp.normalize(v) for v in tw.mul_fp2_const(xB[0], fp.mul_const(xB[1], -1), g2.c0, g2.c1)
                    + tw.mul_fp2_const(yB[0], fp.mul_const(yB[1], -1), g3.c0, g3.c1)]
        g2, g3 = bn254.FROB2[2].c0, bn254.FROB2[3].c0 # -pi^2(B) = (gamma_{2,2} xB, -gamma_{2,3} yB)
        return [fp.normalize(fp.mul_const(v, k)) for v, k in ((xB[0], g2), (xB[1], g2), (yB[0], -g3), (yB[1], -g3))]

    def g2_check(self, T, Kp):
        """B is in G2.  After the loop, T = [6x+2]B + psi(B) - psi^2(B).  Since 6x+2 + p - p^2 + p^3 = 0
        (mod r), T = -psi^3(B) on G2; for any point of the twist outside G2 the two differ (the kernel of
        [6x+2] + psi - psi^2 + psi^3 on E'(Fp2) is exactly G2).  T: the 4 accessors of the final T,
        Kp: the point words of K."""
        fp, b = self.fp, self.b

        def conj_mul(v, g): # conj(v) g for a constant g
            return (fp.lin_const([(v[0], g.c0), (v[1], g.c1)]), fp.lin_const([(v[0], g.c1), (v[1], -g.c0)]))
        x3 = conj_mul((Val(Kp[6], K_HI), Val(Kp[7], K_HI)), bn254.FROB3[2])
        y3 = conj_mul((Val(Kp[8], K_HI), Val(Kp[9], K_HI)), -bn254.FROB3[3])
        tx = (Val(T[0], b['tx']), Val(T[1], b['tx']))
        ty = (Val(T[2], b['ty']), Val(T[3], b['ty']))
        return self.be.checks([v.e for v in self.cv.eq2_check(tx, x3) + self.cv.eq2_check(ty, y3)])

    def step_point(self, kind, K):
        pt = self._step_point_vals(kind, K)
        for v in pt:
            ensure(v.hi <= self.b['q'], 'step point bound')
        return [v.e for v in pt]

    def step_value(self, k, st, leaf, env):
        """The state after step k: a call of the iteration function on (env = (state, leaf), data)."""
        be = self.be
        kind = STEPS[k]
        K = st[2]
        Kp = K[0] if self.residue else K
        data = [[be.word(v) for v in self.fixed[0][k]], [be.word(v) for v in self.fixed[1][k]]]
        if kind == 'D':
            return be.call(self.ITER_D if (k or self.residue) else self.ITER_D0, [env, data])
        if self.residue and kind in ('A+', 'A-'):
            g = be.subtree(K[2] if kind == 'A+' else K[1]) # c^-1 for a digit +1, c for a digit -1
            return be.call(self.ITER_A, [env, [self.step_point(kind, Kp), g, data]])
        return be.call(self.ITER_F, [env, [self.step_point(kind, Kp), data]])

    def initial_state(self, A, B, C, L, c=None, cinv=None):
        """Check A, B, C on their curves (and c c^-1 = 1), normalise every word twice and pack the state
        (f = 1 or c^-1, T = B, K).  A, C, L are (x, y); B is (xx, xy, yx, yy); c, c^-1 are 12 words."""
        fp, be, cv = self.fp, self.be, self.cv
        ws = [A[0], A[1], B[0], B[1], B[2], B[3], C[0], C[1], L[0], L[1]] + (list(c) + list(cinv) if self.residue else [])

        def body1(v):
            xA, yA, xBx, xBy, yBx, yBy, xC, yC, xL, yL = v[:10]
            checks = [cv.g1_on_curve_check(xA, yA), cv.g2_on_curve_check((xBx, xBy), (yBx, yBy)), cv.g1_on_curve_check(xC, yC)]
            n, m = fp.normalize, lambda x: fp.normalize(fp.mul_const(x, -1))
            K = [m(xA), n(yA), m(xL), n(yL), m(xC), n(yC), n(xBx), n(xBy), n(yBx), n(yBy), m(yBx), m(yBy)] + [n(x) for x in v[10:]]
            for x in K:
                ensure(x.hi <= K_HI, 'K bound')

            def body2(Kv):
                if not self.residue:
                    f0 = [fp.const(1)] + [fp.const(0)] * 11
                    return be.pack([[x.e for x in f0], [x.e for x in Kv[6:10]], [x.e for x in Kv]])
                f0 = Kv[24:36] # c^-1
                prod = be.call(self.DMULN, [[x.e for x in Kv[12:24]], [x.e for x in f0]]) # c c^-1 = 1
                chk = be.with_env(prod, words(12), lambda accs: be.checks(
                    [fp.assert_eq_const(Val(a, h), 1 if i == 0 else 0) for i, (a, h) in enumerate(zip(accs, self.b['dmuln']))]))
                state = be.pack([[x.e for x in f0], [x.e for x in Kv[6:10]], [[x.e for x in Kv[:12]], [x.e for x in Kv[12:24]], [x.e for x in f0]]])
                return be.seq(chk, state)
            return be.seq(be.checks(checks), fp.scope(K, body2))
        return fp.scope([fp.normalize(w) for w in ws], body1)

    def loop(self, state0, hints):
        """The final state (f, T, K).  Sym: state0 and hints (the balanced tree of slopes) are E's.  Num:
        state0 is the nested list and hints the list of slopes."""
        be = self.be
        if is_sym(be):
            shape = [words(12), words(4), self.k_shape]

            def step(k):
                return lambda accs: self.step_value(k, accs[0], accs[1], be.iden())
            return be.comp(be.pair(state0, hints), fold_tree(be, shape, self.n_steps, step, leaf_w=512))
        state = state0
        for k, leaf in enumerate(hints[:self.n_steps]):
            state = self.step_value(k, state, leaf, [state, leaf])
        return state


_BOUNDS = None


def bounds():
    """The static bounds of the shared functions, computed once."""
    global _BOUNDS
    if _BOUNDS is None:
        _BOUNDS = Miller(Fp(Num()), bn254.G2_GEN, bn254.G2_GEN).b
    return _BOUNDS
