"""The fflonk verifier of snarkjs 0.7.6 in Simplicity, with snarkjs's Keccak-256 transcript or a SHA-256 one.

The program checks what snarkjs's fflonkVerify checks (fflonk_ref.py is its plain-Python port):

  inputs      the public inputs, the 15 evaluations and the challenges' words are below r, the
              coordinates of C1, C2, W1 below p, and the points on the curve
  transcript  each challenge is the digest of its transcript, reduced mod r.  The prover gives each
              challenge as a canonical word (below r); the program hashes the transcript (Keccak-256, or
              SHA-256 with the `sha_256_ctx_8` jets) and checks digest = word (mod r).  The words are
              what the next transcript absorbs, as snarkjs absorbs the reduced challenges.
  opening     the evaluations of r0, r1, r2 at y, the quotients q1, q2 and e = r0 + q1 r1 + q2 r2, in
              F_r (frprog.py: straight-line code; an inverse is a hint checked by a product)
  MSM         A1 - C0 = q1 C1 + q2 C2 - t W1 + y W2 - e G1 (msm.py: GLV columns with runtime tables for
              the four proof points, windows of constant tables for G1).  The prover gives the column
              words and the canonical v = -e; the program checks them against the scalars in F_r.
  pairing     e(-A1, [1]_2) e(W2, [x]_2) = 1 by pairing.py's polynomial identity, with
              e(-C0, [1]_2) moved into its constant: the pairs are (-(A1 - C0), [1]_2) and (W2, [x]_2).
              The identity's first G2 point is a witness slot for a variable point (Groth16's B), here
              checked equal to [1]_2; the program checks the G1 slots against the MSM's result and W2.

The opening is written once over an abstract field (`opening`), so the prover computes the hints with
the same code the program is generated from.  Its formulas are snarkjs's, simplified: the products over
the roots are y^8 - xi, y^4 - xi and (y^3 - xi)(y^3 - xi w) (h0^8 = h1^4 = xi), the roots are h0, h1,
h2 = powers of xiSeed times constants, and every inverse of a power of xiSeed comes from one hint.

Binding (bind=True): the first two public inputs are the sighash of the spending transaction, two
128-bit limbs (high, low), compared with the sig_all_hash jet.  circuits/multiplier_fflonk.circom
follows this convention.

Witness: w_in holds the public inputs, C1 C2 W1, the evaluations, the 5 challenge words, the inverse
hints, the 8 column words, v, then the pairing check's part (pairing.witness_shape: its G1 slots hold
-(A1 - C0) and W2, in Montgomery form).  The MSM's operation hints and the pairing check's leaves and Q
are witness nodes of their own.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Any

from . import bn254 as B
from . import fflonk_ref as ref
from . import msm as M
from . import pairing
from .curve import Curve
from .dsl import CheckFailed, Tbalanced, WSpec, ensure, wbalanced, wpair, wv
from .fp import FR, WORD_MAX, Fp, Val
from .frprog import FrDag, FrInts
from .groth16 import Groth16
from .keccak import Keccak
from .merkle import sighash_limbs
from .pairing import KB, PairingCheck
from .sym import SHA_CTX_W, E, Sym, words

P, R = B.P, B.R
EVALS = ref.EVALS
CHALLENGES = ['beta', 'gamma', 'xiSeed', 'alpha', 'y']
VAR_POINTS = ['C1', 'C2', 'W1', 'W2']  # the variable-base points, in column order
LAM = M.GLV_LAMBDA


# ---------------------------------------------------------------------------------------------------
# The opening, over an abstract field (frprog.FrInts on integers, frprog.FrDag for the program)
def opening(X: Any, vk: dict[str, Any], ev: dict[str, Any], pub: Sequence[Any], ch: dict[str, Any]) -> dict[str, Any]:
    """q1, q2, e = r0 + q1 r1 + q2 r2, num0 = y^8 - xi (snarkjs's `temp`), and y, from the evaluations,
    the public inputs and the challenges."""
    r = R
    w, w3, w4, w8, wr = (vk[k] for k in ('w', 'w3', 'w4', 'w8', 'wr'))
    n = 1 << vk['power']
    beta, gamma, s, alpha, y = (ch[k] for k in CHALLENGES)
    # the roots: h0 = s^3, h1 = s^6, h2 = s^8, h3 = h2 wr, xi = s^24
    s2 = X.sqr(s)
    h0 = X.mul(s2, s)
    h1 = X.sqr(h0)
    h2 = X.mul(h1, s2)
    h2s = X.sqr(h2)
    xi = X.mul(h2s, h2)
    xin = xi
    for _ in range(vk['power']):
        xin = X.sqr(xin)
    zh = X.lin([(xin, 1)], -1)
    invzh = X.inv(zh)
    # 1/s and its powers: 1/h0^7 = is^21, 1/h1^3 = is^18, 1/h2^2 = is^16, 1/xi = is^24
    is1 = X.inv(s)
    is2 = X.sqr(is1)
    is3 = X.mul(is2, is1)
    is4 = X.sqr(is2)
    is8 = X.sqr(is4)
    is16 = X.sqr(is8)
    is18 = X.mul(is16, is2)
    is21 = X.mul(is18, is3)
    is24 = X.mul(is16, is8)
    # Lagrange: L_i = w^i zh / (n (xi - w^i)), and PI = -sum pub_i L_(i+1)
    lag = []
    for i in range(max(1, vk['nPublic'])):
        wi = pow(w, i, r)
        lag.append(X.mul(X.mulc(zh, wi), X.inv(X.lin([(xi, n)], -n * wi % r))))
    pin = X.dot([(x, lag[i]) for i, x in enumerate(pub)]) if pub else None
    # y's powers, and the products over the roots
    y2 = X.sqr(y)
    y3 = X.mul(y2, y)
    y4 = X.sqr(y2)
    num0 = X.lin([(X.sqr(y4), 1), (xi, -1)])  # y^8 - xi
    num1 = X.lin([(y4, 1), (xi, -1)])  # y^4 - xi
    num2 = X.dot([(y3, X.lin([(y3, 1), (xi, -(1 + w) % r)])), (xi, X.mulc(xi, w))])  # (y^3 - xi)(y^3 - xi w)
    # r0 = (y^8 - xi) / (8 h0^7) sum_i c0_i w8^i / (y - h0 w8^i), c0_i = sum_j e_j h0^j w8^(ij)
    hp = [None, h0, X.sqr(h0)]
    hp.append(X.mul(hp[2], h0))
    hp.append(X.sqr(hp[2]))
    hp.append(X.mul(hp[4], h0))
    hp.append(X.sqr(hp[3]))
    hp.append(X.mul(hp[6], h0))
    e0 = [ev[k] for k in ('ql', 'qr', 'qo', 'qm', 'qc', 's1', 's2', 's3')]
    g0 = [e0[0]] + [X.mul(e0[j], hp[j]) for j in range(1, 8)]
    terms = []
    for i in range(8):
        c0 = X.lin([(g0[j], pow(w8, i * j, r)) for j in range(8)])
        u = X.inv(X.lin([(y, 1), (h0, -pow(w8, i, r) % r)]))
        terms.append((c0, X.mulc(u, pow(w8, i, r))))
    r0 = X.mulc(X.mul(X.dot(terms), X.mul(num0, is21)), pow(8, -1, r))
    # t0 = (ql a + qr b + qm a b + qo c + qc + PI) / zh
    ab = X.mul(ev['a'], ev['b'])
    t0n = [(ev['ql'], ev['a']), (ev['qr'], ev['b']), (ev['qm'], ab), (ev['qo'], ev['c'])]
    t0 = X.mul(X.lin([(X.dot(t0n), 1), (ev['qc'], 1)] + ([(pin, -1)] if pin is not None else [])), invzh)
    # r1 = (y^4 - xi) / (4 h1^3) sum_i c1_i w4^i / (y - h1 w4^i), c1_i = a + h1 b w4^i + h1^2 c w4^2i + h1^3 t0 w4^3i
    h1s = X.sqr(h1)
    g1 = [ev['a'], X.mul(ev['b'], h1), X.mul(ev['c'], h1s), X.mul(t0, X.mul(h1s, h1))]
    terms = []
    for i in range(4):
        c1 = X.lin([(g1[j], pow(w4, i * j, r)) for j in range(4)])
        u = X.inv(X.lin([(y, 1), (h1, -pow(w4, i, r) % r)]))
        terms.append((c1, X.mulc(u, pow(w4, i, r))))
    r1 = X.mulc(X.mul(X.dot(terms), X.mul(num1, is18)), pow(4, -1, r))
    # t1 = (z - 1) L_1 / zh, t2 = (t21 - t22) / zh
    z, zw = ev['z'], ev['zw']
    t1 = X.mul(X.mul(X.lin([(z, 1)], -1), lag[0]), invzh)
    bxi = X.mul(beta, xi)
    f1 = X.lin([(ev['a'], 1), (bxi, 1), (gamma, 1)])
    f2 = X.lin([(ev['b'], 1), (bxi, vk['k1']), (gamma, 1)])
    f3 = X.lin([(ev['c'], 1), (bxi, vk['k2']), (gamma, 1)])
    g1_ = X.add(ev['a'], X.add(X.mul(beta, ev['s1']), gamma))
    g2_ = X.add(ev['b'], X.add(X.mul(beta, ev['s2']), gamma))
    g3_ = X.add(ev['c'], X.add(X.mul(beta, ev['s3']), gamma))
    t21 = X.mul(X.mul(f1, f2), X.mul(f3, z))
    t22 = X.mul(X.mul(g1_, g2_), X.mul(g3_, zw))
    t2 = X.mul(X.sub(t21, t22), invzh)
    # r2 = (y^3 - xi)(y^3 - xi w) / (3 (xi - xi w)) (A / h2^2 - B / h3^2), h3 = h2 wr,
    # A = sum_i c2_i w3^i / (y - h2 w3^i), c2_i = z + h2 t1 w3^i + h2^2 t2 w3^2i, B the same at h3
    h3 = X.mulc(h2, wr)
    ga = [z, X.mul(h2, t1), X.mul(h2s, t2)]
    gb = [zw, X.mul(h3, ev['t1w']), X.mul(X.mulc(h2s, wr * wr % r), ev['t2w'])]
    sums = []
    for gg, h in ((ga, h2), (gb, h3)):
        terms = []
        for i in range(3):
            c2 = X.lin([(gg[j], pow(w3, i * j, r)) for j in range(3)])
            u = X.inv(X.lin([(y, 1), (h, -pow(w3, i, r) % r)]))
            terms.append((c2, X.mulc(u, pow(w3, i, r))))
        sums.append(X.dot(terms))
    inner = X.dot([(sums[0], is16), (sums[1], X.mulc(is16, -pow(wr * wr, -1, r) % r))])
    r2 = X.mulc(X.mul(X.mul(num2, is24), inner), pow(3 * (1 - w), -1, r))
    # the quotients and e
    q1 = X.mul(X.mul(alpha, num0), X.inv(num1))
    q2 = X.mul(X.mul(X.sqr(alpha), num0), X.inv(num2))
    e = X.lin([(X.dot([(q1, r1), (q2, r2)]), 1), (r0, 1)])
    return {'q1': q1, 'q2': q2, 'num0': num0, 'y': y, 'e': e}


def scalar_checks(X: Any, o: dict[str, Any], cols: Sequence[Any], v: Any) -> None:
    """The column words against the scalars: k = n1 + lambda n2 with n = 2 C - (2^128 - 1); and v = -e."""
    ks = [o['q1'], o['q2'], X.mulc(o['num0'], -1), o['y']]
    c0 = (2**M.HALF_BITS - 1) * (1 + LAM) % R
    for i, k in enumerate(ks):
        X.check_zero(f'glv {VAR_POINTS[i]}', [(k, 1), (cols[2 * i], -2), (cols[2 * i + 1], -2 * LAM % R)], c0)
    X.check_zero('fixed scalar', [(o['e'], 1), (v, 1)])


# ---------------------------------------------------------------------------------------------------
# The prover's side
def witness(vk: dict[str, Any], proof: dict[str, Any], pub: Sequence[int], mode: str) -> dict[str, Any] | None:
    """Everything the program needs, or None if the proof does not verify."""
    v = ref.verify(mode, vk, proof, pub)
    if not v['ok']:
        return None
    X = FrInts(R)
    ch = {k: v[k] for k in CHALLENGES}
    o = opening(X, vk, {k: proof[k] for k in EVALS}, list(pub), ch)
    ensure(o['q1'] == v['quotient1'] and o['q2'] == v['quotient2'] and o['e'] == v['e'], 'opening disagrees')
    pts = [proof[k] for k in VAR_POINTS]
    scal = [o['q1'], o['q2'], (-o['num0']) % R, o['y']]
    var = M.var_witness(pts, scal)
    vfix = (-o['e']) % R
    fix = M.fixed_witness(B.G1_GEN, vfix, M.var_offset())
    s, final = M.add_hint(var['result'], fix['result'])
    ensure(B.g1_add(s, vk['C0']) == v['A1'], 'A1')
    scalar_checks(X, o, var['cols'], vfix)
    return {
        'pub': list(pub),
        'pts': [proof[k] for k in ('C1', 'C2', 'W1')],
        'ev': [proof[k] for k in EVALS],
        'ch': [ch[k] for k in CHALLENGES],
        'inv': X.hints,
        'cols': var['cols'],
        'v': vfix,
        'var': var,
        'fix': fix,
        'final': final,
        'S': s,
        'W2': proof['W2'],
        'ref': v,
    }


# ---------------------------------------------------------------------------------------------------
# The program
N_INV_FIXED = 22  # inverse hints besides the Lagrange denominators (one per public input, at least one)


def _T(n: int) -> str:
    return Tbalanced(['2^256'] * n)


def _W(ws: Sequence[int]) -> WSpec:
    return wbalanced([wv(256, x) for x in ws])


class Fflonk:
    """Generator of the verifier of a snarkjs fflonk key (fflonk_ref.load_vk), for the transcript `mode`
    ('keccak' or 'sha256').  bind: the first two public inputs are the sighash (see the module's
    docstring).  b: pairing.bounds()."""

    def __init__(
        self, fp: Fp, vk: dict[str, Any], mode: str = 'keccak', bind: bool = False, b: dict[str, int] | None = None
    ) -> None:
        ensure(mode in ref.MODES, f'mode {mode}')
        self.fp, self.be = fp, fp.be
        self.fr = Fp(fp.be, FR)
        self.cv, self.cvr = Curve(fp), Curve(self.fr)
        self.vk, self.mode, self.bind = vk, mode, bind
        self.n = vk['nPublic']
        ensure(self.n >= (2 if bind else 1), 'public inputs: at least 1, and 2 for the binding')
        self.n_inv = N_INV_FIXED + max(1, self.n)
        const = B.multi_miller_loop_affine([(B.g1_neg(vk['C0']), B.G2_GEN)])
        self.pc = PairingCheck(fp, vk['X_2'], const, [B.Fp12.one()], b)
        self.g1 = M.G1(fp)
        self.var = M.VarMsm(fp, prefix='wv')
        self.fixed = M.FixedMsm(fp, prefix='wf', extra=M.var_offset())
        self.parts: dict[str, int] = {}

    # the witness
    def shape(self) -> list[Any]:
        """(public inputs, C1 C2 W1, evaluations, challenges, inverses, columns, v, the pairing's part)"""
        return [
            words(self.n),
            [words(2) for _ in range(3)],
            words(len(EVALS)),
            words(len(CHALLENGES)),
            words(self.n_inv),
            words(8),
            E('', 256, 0),
            pairing.witness_shape(),
        ]

    def witness_type(self) -> str:
        pts = Tbalanced([_T(2)] * 3)
        parts = [_T(self.n), pts, _T(len(EVALS)), _T(len(CHALLENGES)), _T(self.n_inv), _T(8), '2^256']
        return Tbalanced(parts + [pairing.witness_type()])

    def witness_bits(self) -> int:
        return 256 * (self.n + 6 + len(EVALS) + len(CHALLENGES) + self.n_inv + 8 + 1) + pairing.witness_bits()

    def witness(self, proof: dict[str, Any], pub: Sequence[int], sighash: bytes | int | None = None) -> dict[str, Any]:
        """The witness of a proof (fflonk_ref.load_proof) for the public inputs, or CheckFailed.  With a
        binding, the sighash must be the first two public inputs."""
        w = witness(self.vk, proof, pub, self.mode)
        if w is None:
            raise CheckFailed('the proof does not verify')
        if self.bind:
            ensure(sighash is not None, 'the sighash')
            assert sighash is not None
            ensure(list(pub[:2]) == sighash_limbs(sighash), 'the first two public inputs are not the sighash')
        p_slot = M.neg(w['S'])
        w['pairing'] = self.pc.prover.witness([(p_slot, B.G2_GEN), (w['W2'], self.vk['X_2'])], [])
        ensure(w['pairing'] is not None, 'pairing witness')
        return w

    def cost(self, estimate: int, pad: int) -> int:
        """The cost of a spend with `pad` blocks of padding: compile's estimate counts every group."""
        return estimate - self.padding.saved(pad)

    def pad_for(self, estimate: int, program_bytes: int, witness_bytes: int, slack: int = 64) -> int:
        """The fewest blocks of padding whose budget covers the cost, given the pruned program's and the
        witness's bytes without padding (hand reports them).  The budget is counted low, as for Groth16
        (Groth16.budget_ok): 1,000 mWU per byte of the program, the witness, the control block and 9 bytes of
        length prefixes, plus 50,000.  The sizes must be lower bounds: a group taken adds its code to the
        pruned program, which only raises the budget.  `slack` bytes are taken off besides."""
        for blocks in range(2**PAD_GROUPS):
            if Groth16.budget_ok(
                self.cost(estimate, blocks), program_bytes - slack, witness_bytes + PAD_BLOCK * blocks
            ):
                return blocks
        raise CheckFailed('the padding cannot cover the cost')

    def witness_value(self, w: dict[str, Any], pad: int = 0) -> dict[str, WSpec]:
        """The witness as harness value specs, by witness node, with `pad` blocks of padding."""
        main = [
            _W(w['pub']),
            wbalanced([_W(list(pt)) for pt in w['pts']]),
            _W(w['ev']),
            _W(w['ch']),
            _W([FR.to_mont(x) for x in w['inv']]),
            _W(w['cols']),
            wv(256, w['v']),
            pairing.witness_value(w['pairing']),
        ]
        nodes = {'w_in': wbalanced(main), **pairing.witness_nodes(w['pairing'])}
        nodes.update(var_nodes(w['var']))
        for j, h in enumerate(w['fix']['hints']):
            nodes[f'wf{j}'] = _W(M.mont(h))
        nodes['wz'] = _W(M.mont(w['final']))
        nodes.update(Padding.value(pad))
        return nodes

    # the program
    def program(self) -> E:
        """Sym: the unit-typed E of the whole verifier over the witness environment."""
        be = self.be
        be.env[0] = self.witness_bits()
        pub, pts, ev, ch, inv, cols, v, pw = be._unpack('', self.shape())
        parts = {
            'ranges': self.ranges(pub, pts, ev, ch, v),
            'transcript': self.transcript(pub, pts, ev, ch),
            'opening': self.opening(pub, ev, ch, inv, cols, v),
            'msm': self.msm(pts, cols, v, pw[0][0]),
            'pairing': self.pairing(pw),
        }
        if self.bind:
            parts['binding'] = self.binding(pub)
        self.padding = Padding(be)
        parts['padding'] = self.padding.program()
        self.parts = {k: e.c for k, e in parts.items()}
        return be.checks(list(parts.values()))

    def ranges(self, pub: Any, pts: Any, ev: Any, ch: Any, v: Any) -> E:
        """The words below r, the coordinates below p."""
        lt = self.cv.lt_const_check
        out = [lt(Val(w, 0), R).e for w in list(pub) + list(ev) + list(ch) + [v]]
        out += [lt(Val(w, 0), P).e for pt in pts for w in pt]
        return self.be.checks(out)

    def transcript_items(self, pub: Any, pts: Any, ev: Any, ch: Any) -> list[list[Any]]:
        """The words each challenge hashes, in snarkjs's order (ints: constants)."""
        c0 = self.vk['C0']
        return [
            [c0[0], c0[1]] + list(pub) + list(pts[0]),
            [ch[0]],
            [ch[1]] + list(pts[1]),
            [ch[2]] + list(ev),
            [ch[3]] + list(pts[2]),
        ]

    def digest(self, items: Sequence[Any]) -> E:
        be = self.be
        if self.mode == 'keccak':
            return Keccak(be).hash_words(items)
        h = be.jet('sha_256_ctx_8_init', be.unit(), SHA_CTX_W)
        for x in items:
            arg = be.const(256, x) if isinstance(x, int) else x
            h = be.jet('sha_256_ctx_8_add_32', be.pair(h, arg), SHA_CTX_W)
        return be.jet('sha_256_ctx_8_finalize', h, 256)

    def transcript(self, pub: Any, pts: Any, ev: Any, ch: Any) -> E:
        """Each challenge word is its digest mod r."""
        fr, cvr = self.fr, self.cvr
        out = []
        for items, c in zip(self.transcript_items(pub, pts, ev, ch), ch):
            h = fr.to_mont(Val(self.digest(items), WORD_MAX))
            out.append(cvr.eq_check(h, fr.to_mont(Val(c, R - 1))).e)
        return self.be.checks(out)

    def opening(self, pub: Any, ev: Any, ch: Any, inv: Any, cols: Any, v: Any) -> E:
        """The opening in F_r and the checks of the scalars' words."""
        fr, be = self.fr, self.be
        tm = lambda w, hi: fr.to_mont(Val(w, hi))
        names = [f'pub{i}' for i in range(self.n)] + EVALS + CHALLENGES + [f'col{i}' for i in range(8)] + ['v']
        vals = (
            [tm(w, R - 1) for w in pub]
            + [tm(w, R - 1) for w in ev]
            + [tm(w, R - 1) for w in ch]
            + [tm(w, 2**M.HALF_BITS - 1) for w in cols]
            + [tm(v, R - 1)]
        )
        hints = [Val(w, pairing.F_HI) for w in inv]
        top2 = [self.g1.top2(w) for w in inv]

        def body(a):
            ins = dict(zip(names, a[: len(names)]))
            dag = FrDag(ins, a[len(names) :])
            o = opening(
                dag,
                self.vk,
                {k: dag[k] for k in EVALS},
                [dag[f'pub{i}'] for i in range(self.n)],
                {k: dag[k] for k in CHALLENGES},
            )
            scalar_checks(dag, o, [dag[f'col{i}'] for i in range(8)], dag['v'])
            ensure(dag.n_hints == self.n_inv, 'inverse hints')
            return dag.run(fr, [], lambda c, checks, outs: be.checks([chk.e for chk in checks]))

        return be.checks(top2 + [fr.scope(vals + hints, body)])

    def msm(self, pts: Any, cols: Any, v: Any, slots: Any) -> E:
        """A1 - C0 from the points and the words, against the pairing's first G1 slot (its negation); the
        proof's points on the curve; the slot B = [1]_2."""
        fp, be, cv = self.fp, self.be, self.cv
        g2 = [B.G2_GEN[0].c0, B.G2_GEN[0].c1, B.G2_GEN[1].c0, B.G2_GEN[1].c1]
        b_slot = [be.verify(be.eq256(w, be.word(M.to_mont(x)))) for w, x in zip(slots[2:6], g2)]
        mont = lambda w: fp.to_mont(Val(w, P - 1))
        norm = lambda w: fp.normalize(Val(w, WORD_MAX))
        vals = [
            [[mont(x), mont(y)] for x, y in pts],
            [norm(slots[6]), norm(slots[7])],  # W2
            [norm(slots[0]), norm(slots[1])],  # the slot -(A1 - C0)
            [Val(w, WORD_MAX) for w in cols],
            Val(v, WORD_MAX),
        ]

        def body(a):
            p3, w2, ps, cw, vw = a
            on_curve = [cv.g1_on_curve_check(x, y) for x, y in p3]
            points = [[x.e, y.e] for x, y in p3] + [[w2[0].e, w2[1].e]]
            t, col_checks = self.var.program(points, [c.e for c in cw])
            s = self.g1.add(t, self.fixed.program(vw.e), be.witness('wz', _T(2), 512))

            def cmp(acc, lift):
                sx, sy = be.split(acc[0], words(2))
                px, py = (Val(lift(x.e), x.hi) for x in ps)
                return be.checks([cv.eq_check(Val(sx, KB), px).e, cv.zero_check(fp.add(Val(sy, KB), py)).e])

            return be.checks(on_curve + col_checks + [be.let([s], cmp)])

        return be.checks(b_slot + [fp.scope(vals, body)])

    def pairing(self, pw: Any) -> E:
        (pts, ac), rz = pw
        return self.pc.program({'x': [], 'words': []}, pts, ac, rz)

    def binding(self, pub: Any) -> E:
        """The first two public inputs are the high and low halves of the sig_all_hash jet's sighash."""
        be = self.be
        h = be.jet('sig_all_hash', be.unit(), 256)

        def body(acc, lift):
            hv = acc[0]
            out = []
            for k, half in enumerate(('O', 'I')):
                x = lift(pub[k])
                for pth in ('OO', 'OI'):  # the top half of the input is 0
                    out.append(be.verify(be.jet('eq_64', be.pair(be.sub(x, pth, 64), be.const(64, 0)), 1)))
                for pth in ('O', 'I'):  # its low half is the sighash's half
                    out.append(
                        be.verify(be.jet('eq_64', be.pair(be.sub(x, 'I' + pth, 64), be.sub(hv, half + pth, 64)), 1))
                    )
            return be.checks(out)

        return be.let([h], body)

    @classmethod
    def compile(
        cls, vk: dict[str, Any], mode: str = 'keccak', bind: bool = False, b: dict[str, int] | None = None
    ) -> tuple[str, Fflonk, int]:
        """The verifier of a key: (program text, its generator, cost bound in mWU)."""
        be = Sym(0)
        g = cls(Fp(be), vk, mode, bind, b or pairing.bounds())
        body = g.program()
        be.em.define('w_in', 'witness', f'_ -> {g.witness_type()}')
        be.em.define('main', f'comp w_in ({body.t})')
        # each witness node is read once: a spender may unshare a node and give each copy its own value
        uses = be.em.tree_uses()
        nodes = [name for name, expr, _ in be.em.defs if expr == 'witness']
        ensure(all(uses.get(name) == 1 for name in nodes), 'a witness node is read more than once')
        return be.em.text(), g, 2 * (100 + g.witness_bits()) + body.c


def var_nodes(w: dict[str, Any], prefix: str = 'wv') -> dict[str, WSpec]:
    """The witness nodes of msm.var_witness's hints, as VarMsm reads them."""
    nodes = {}
    for g, hs in enumerate(w['tables']):
        for j, h in enumerate(hs):
            nodes[f'{prefix}t{g}_{j}'] = _W(M.mont(h))
    bits = len(w['steps'])
    for si, hs in enumerate(w['steps']):
        j = bits - 1 - si
        it = iter(hs)
        if si:
            nodes[f'{prefix}s{j}d'] = _W(M.mont(next(it)))
        for g in range(len(w['tables'])):
            nodes[f'{prefix}s{j}a{g}'] = _W(M.mont(next(it)))
    return nodes


# ---------------------------------------------------------------------------------------------------
# Padding.  The input's budget is 1,000 mWU per byte of its witness stack, and the verifier costs more
# than its program and witness weigh, so a spend adds zero blocks to the witness.  How many depends on
# the pruned program's size, known at spend time, so the program offers groups of 1, 2, 4, ... 256
# blocks of 512 bytes, each behind a case on a bit of the witness word `wpsel`: a group not taken is
# pruned, and leaves only its commitment.  A block is 16 words checked to be 0, which also fixes the
# block's type (a witness value whose type nothing constrains would not survive decoding).  wpsel's 16
# bits are all read: bits 0 .. 8 select the groups, bits 9 .. 15 must be 0.
PAD_GROUPS = 9
PAD_BLOCK = 512  # bytes


def pad_bits(blocks: int) -> list[int]:
    ensure(0 <= blocks < 2**PAD_GROUPS, f'padding: at most {2**PAD_GROUPS - 1} blocks')
    return [(blocks >> k) & 1 for k in range(PAD_GROUPS)]


def pad_type(k: int) -> str:
    t = _T(16)
    for _ in range(k):
        t = f'({t} * {t})'
    return t


def pad_value(k: int) -> WSpec:
    v = _W([0] * 16)
    for _ in range(k):
        v = wpair(v, v)
    return v


class Padding:
    """The padding's code (Sym) and the cost each group adds when taken (`group_cost`)."""

    def __init__(self, be: Any) -> None:
        self.be = be

        def halves(prev: E) -> Any:
            return lambda a: be.checks([be.call(prev, [be.subtree(a[0])]), be.call(prev, [be.subtree(a[1])])])

        fns = [be.function('PAD0', words(16), lambda a: be.checks([be.verify(be.eq256(w, be.word(0))) for w in a]))]
        shape: Any = words(16)
        for k in range(1, PAD_GROUPS):
            shape = [shape, shape]
            fns.append(be.function(f'PAD{k}', shape, halves(fns[-1])))
        self.fns = fns
        self.group_cost: list[int] = []

    def program(self) -> E:
        be = self.be
        sel = be.witness('wpsel', '2^16', 16)

        def body(acc):
            (w,) = acc
            out = []
            for k in range(16):
                bit = be.sub(w, ''.join('I' if (15 - k) >> (3 - i) & 1 else 'O' for i in range(4)), 1)
                if k >= PAD_GROUPS:
                    out.append(be.verify(be.not1(bit)))
                    continue
                taken = be.comp(be.witness(f'wpad{k}', pad_type(k), 256 * 16 * 2**k), self.fns[k])
                skip = be.unit()
                self.group_cost.append(taken.c - skip.c)
                out.append(be.comp(be.pair(bit, be.unit()), be.case(be.drop(skip), be.drop(taken))))
            return be.checks(out)

        return be.with_env(sel, [E('', 16, 0)], body)

    @staticmethod
    def value(blocks: int) -> dict[str, WSpec]:
        """The selector, and every group's blocks: `deploy` encodes the unpruned program, which needs a value
        for each witness node; pruning drops the groups not taken, with their values."""
        pad_bits(blocks)
        out = {'wpsel': {'w': f'{blocks:04x}'}}
        for k in range(PAD_GROUPS):
            out[f'wpad{k}'] = pad_value(k)
        return out

    def saved(self, blocks: int) -> int:
        """The cost of the groups not taken, which the pruned program does not pay."""
        return sum(c for c, b in zip(self.group_cost, pad_bits(blocks)) if not b)
