"""The fflonk verifier of snarkjs 0.7.6 in plain Python, with its Keccak-256 transcript or a SHA-256 one.

A line-by-line port of snarkjs's src/fflonk_verify.js (the names follow it), so that the program
(verifier.py) and its witness can be checked against every intermediate value.  `verify` returns those
values; `ok` says whether the proof verifies.

The transcript: snarkjs absorbs points uncompressed (x then y, 32-byte big-endian words) and scalars as
32-byte big-endian words, hashes with Keccak-256 and reduces the digest mod r.  mode 'sha256' is the same
transcript with SHA-256 (tools/snarkjs_sha256.mjs is the matching prover).

The pairing check is e(-A1, [1]_2) e(W2, [x]_2) = 1 with

    A1 = C0 + q1 C1 + q2 C2 - e G1 - t W1 + y W2,

q1, q2 the quotients, e = r0 + q1 r1 + q2 r2, t = (y - h0)(y - h0 w8) ... (y - h0 w8^7) (`temp`).
"""

from __future__ import annotations

import hashlib
from collections.abc import Sequence
from typing import Any

from ..core import bn254 as B
from ..core.keccak import keccak256
from ..core.snarkjs import FFLONK_EVALS as EVALS
from ..core.snarkjs import FFLONK_POINTS as POINTS

R = B.R
G1Point = tuple[int, int]
MODES = ('keccak', 'sha256')


# ---------------------------------------------------------------------------------------------------
# The transcript
def point_bytes(pt: G1Point) -> bytes:
    return pt[0].to_bytes(32, 'big') + pt[1].to_bytes(32, 'big')


def scalar_bytes(x: int) -> bytes:
    return (x % R).to_bytes(32, 'big')


def digest(mode: str, data: bytes) -> int:
    """The transcript's hash of the absorbed bytes, as a big-endian integer (not reduced)."""
    assert mode in MODES, mode
    h = keccak256(data) if mode == 'keccak' else hashlib.sha256(data).digest()
    return int.from_bytes(h, 'big')


def challenges(mode: str, vk: dict[str, Any], proof: dict[str, Any], pub: Sequence[int]) -> dict[str, Any]:
    """beta, gamma, xiSeed, alpha, y: each the digest of its transcript mod r; also the digests (h_*) and
    the bytes hashed (m_*)."""
    out: dict[str, Any] = {}

    def ch(name: str, data: bytes) -> int:
        h = digest(mode, data)
        out['m_' + name], out['h_' + name], out[name] = data, h, h % R
        return h % R

    beta = ch('beta', point_bytes(vk['C0']) + b''.join(scalar_bytes(x) for x in pub) + point_bytes(proof['C1']))
    gamma = ch('gamma', scalar_bytes(beta))
    xiseed = ch('xiSeed', scalar_bytes(gamma) + point_bytes(proof['C2']))
    alpha = ch('alpha', scalar_bytes(xiseed) + b''.join(scalar_bytes(proof[k]) for k in EVALS))
    ch('y', scalar_bytes(alpha) + point_bytes(proof['W1']))
    return out


# ---------------------------------------------------------------------------------------------------
# The verifier
def inv(x: int) -> int:
    assert x % R, 'inverse of 0'
    return pow(x, -1, R)


def lagrange_si(roots: Sequence[int], x: int, xi: int) -> list[int]:
    """computeLagrangeLiSi"""
    n = len(roots)
    num = (pow(x, n, R) - xi) % R
    den1 = n * pow(roots[0], n - 2, R) % R
    return [num * inv(den1 * roots[((n - 1) * i) % n] * (x - roots[i])) % R for i in range(n)]


def lagrange_s2(roots: Sequence[Sequence[int]], value: int, xi0: int, xi1: int) -> list[int]:
    """computeLagrangeLiS2"""
    n = len(roots[0])
    num = (pow(value, 2 * n, R) - (xi0 + xi1) * pow(value, n, R) + xi0 * xi1) % R
    out = []
    for k, (a, b) in enumerate(((xi0, xi1), (xi1, xi0))):
        den1 = n * roots[k][0] * (a - b) % R
        out += [num * inv(den1 * roots[k][(n - 1) * i % n] * (value - roots[k][i])) % R for i in range(n)]
    return out


def verify(mode: str, vk: dict[str, Any], proof: dict[str, Any], pub: Sequence[int]) -> dict[str, Any]:
    """Every value of snarkjs's fflonkVerify, and v['ok']."""
    v: dict[str, Any] = {'ok': False}
    ev = proof
    if len(pub) != vk['nPublic'] or not all(0 <= x < R for x in pub):
        return v
    if not all(B.g1_on_curve(*proof[k]) for k in POINTS) or not B.g1_on_curve(*vk['C0']):
        return v
    v.update(challenges(mode, vk, proof, pub))
    beta, gamma, xiseed, alpha, y = (v[k] for k in ('beta', 'gamma', 'xiSeed', 'alpha', 'y'))
    w8 = [pow(vk['w8'], i, R) for i in range(8)]
    w4 = [pow(vk['w4'], i, R) for i in range(4)]
    w3 = [pow(vk['w3'], i, R) for i in range(3)]
    h0 = xiseed * xiseed % R * xiseed % R
    h0w8 = [h0 * w8[i] % R for i in range(8)]
    h1 = h0 * h0 % R
    h1w4 = [h1 * w4[i] % R for i in range(4)]
    h2 = h1 * xiseed % R * xiseed % R
    h2w3 = [h2 * w3[i] % R for i in range(3)]
    h3 = h2 * vk['wr'] % R
    h3w3 = [h3 * w3[i] % R for i in range(3)]
    xi = h2 * h2 % R * h2 % R
    xiw = xi * vk['w'] % R
    n = 1 << vk['power']
    xin = pow(xi, n, R)
    zh = (xin - 1) % R
    invzh = inv(zh)
    # Lagrange evaluations L_1 .. L_max(1, nPublic) and PI(xi)
    lag, w = [], 1
    for _ in range(max(1, vk['nPublic'])):
        lag.append(w * zh % R * inv(n * (xi - w)) % R)
        w = w * vk['w'] % R
    pi = -sum(x * lag[i] for i, x in enumerate(pub)) % R
    # r0
    li = lagrange_si(h0w8, y, xi)
    r0 = 0
    for i in range(8):
        h = h0w8[i]
        c0 = sum(ev[k] * pow(h, j, R) for j, k in enumerate(['ql', 'qr', 'qo', 'qm', 'qc', 's1', 's2', 's3']))
        r0 = (r0 + c0 * li[i]) % R
    # r1
    li = lagrange_si(h1w4, y, xi)
    t0 = (
        ev['ql'] * ev['a'] + ev['qr'] * ev['b'] + ev['qm'] * ev['a'] * ev['b'] + ev['qo'] * ev['c'] + ev['qc'] + pi
    ) % R
    t0 = t0 * invzh % R
    r1 = 0
    for i in range(4):
        h = h1w4[i]
        c1 = (ev['a'] + h * ev['b'] + h * h * ev['c'] + h * h * h * t0) % R
        r1 = (r1 + c1 * li[i]) % R
    # r2
    li = lagrange_s2([h2w3, h3w3], y, xi, xiw)
    t1 = (ev['z'] - 1) * lag[0] % R * invzh % R
    betaxi = beta * xi % R
    t21 = (ev['a'] + betaxi + gamma) * (ev['b'] + betaxi * vk['k1'] + gamma) * (ev['c'] + betaxi * vk['k2'] + gamma)
    t21 = t21 * ev['z'] % R
    t22 = (
        (ev['a'] + beta * ev['s1'] + gamma) * (ev['b'] + beta * ev['s2'] + gamma) * (ev['c'] + beta * ev['s3'] + gamma)
    )
    t22 = t22 * ev['zw'] % R
    t2 = (t21 - t22) * invzh % R
    r2 = 0
    for i in range(3):
        c2 = (ev['z'] + h2w3[i] * t1 + h2w3[i] * h2w3[i] * t2) % R
        r2 = (r2 + c2 * li[i]) % R
    for i in range(3):
        c2 = (ev['zw'] + h3w3[i] * ev['t1w'] + h3w3[i] * h3w3[i] * ev['t2w']) % R
        r2 = (r2 + c2 * li[i + 3]) % R
    # F, E, J and the pairing
    mul_h0 = 1
    for h in h0w8:
        mul_h0 = mul_h0 * (y - h) % R
    mul_h1 = 1
    for h in h1w4:
        mul_h1 = mul_h1 * (y - h) % R
    mul_h2 = 1
    for h in h2w3 + h3w3:
        mul_h2 = mul_h2 * (y - h) % R
    q1 = alpha * mul_h0 % R * inv(mul_h1) % R
    q2 = alpha * alpha % R * mul_h0 % R * inv(mul_h2) % R
    e = (r0 + q1 * r1 + q2 * r2) % R
    v.update(
        h0=h0,
        h1=h1,
        h2=h2,
        h3=h3,
        h0w8=h0w8,
        h1w4=h1w4,
        h2w3=h2w3,
        h3w3=h3w3,
        xi=xi,
        xiw=xiw,
        xin=xin,
        zh=zh,
        lagrange=lag,
        pi=pi,
        r0=r0,
        r1=r1,
        r2=r2,
        t0=t0,
        t1=t1,
        t2=t2,
        temp=mul_h0,
        quotient1=q1,
        quotient2=q2,
        e=e,
    )
    # the MSM: A1 = C0 + q1 C1 + q2 C2 - e G1 - temp W1 + y W2
    v['scalars'] = {'C1': q1, 'C2': q2, 'W1': (-mul_h0) % R, 'W2': y, 'G1': (-e) % R}
    a1 = vk['C0']
    for k, s in v['scalars'].items():
        a1 = B.g1_add(a1, B.g1_mul(B.G1_GEN if k == 'G1' else proof[k], s))
    v['A1'] = a1
    if a1 is None:
        return v
    v['ok'] = B.multi_pairing([(B.g1_neg(a1), B.G2_GEN), (proof['W2'], vk['X_2'])]).is_one()
    return v
