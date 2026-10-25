"""snarkjs's JSON files (0.7.6, bn128) as numbers and points, for both verifiers' tools.

Every point is checked: coordinates below p, not at infinity, on the curve (G1) or the twist and in the
order-r subgroup (G2).  The checks raise CheckFailed (dsl.ensure), not AssertionError, so python -O keeps
them; the tools turn them into refusals.  The keys are compiled into the programs, so they are trusted as
the deployer's: these checks catch a corrupted or substituted file, not a malicious setup.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from typing import Any

from . import bn254 as B
from .dsl import ensure

G1Point = tuple[int, int]
# the fflonk proof's points and the evaluations its verifier reads (snarkjs also writes `inv`, unread)
FFLONK_POINTS = ['C1', 'C2', 'W1', 'W2']
FFLONK_EVALS = ['ql', 'qr', 'qm', 'qo', 'qc', 's1', 's2', 's3', 'a', 'b', 'c', 'z', 'zw', 't1w', 't2w']


def load(path: str) -> Any:
    with open(path) as f:
        return json.load(f)


def g1(pt: Sequence[Any]) -> G1Point:
    """A snarkjs G1 point (projective, decimal strings), affine."""
    x, y, z = (int(v) for v in pt)
    ensure(min(x, y, z) >= 0 and max(x, y, z) < B.P and z != 0, 'a G1 point: coordinates below p, not at infinity')
    if z != 1:
        zi = pow(z, -1, B.P)
        x, y = x * zi % B.P, y * zi % B.P
    ensure(B.g1_on_curve(x, y), 'G1 point not on the curve')
    return (x, y)


def g2(pt: Sequence[Any]) -> B.G2Point:
    """A snarkjs G2 point, affine."""
    ensure(all(0 <= int(c) < B.P for v in pt for c in v), 'a G2 point: coordinates below p')
    x, y, z = (B.Fp2(int(v[0]), int(v[1])) for v in pt)
    ensure(not z.is_zero(), 'a G2 point at infinity')
    if z != B.Fp2(1):
        zi = z.inv()
        x, y = x * zi, y * zi
    ensure(B.g2_on_curve(x, y), 'G2 point not on the twist')
    ensure(B.g2_in_subgroup((x, y)), 'G2 point not in the order-r subgroup')
    return (x, y)


def public_signals(j: Sequence[Any]) -> list[int]:
    """public.json: the public signals, each below r."""
    out = [int(v) for v in j]
    ensure(all(0 <= v < B.R for v in out), 'a public signal is not below r')
    return out


# Groth16
def groth16_key(j: dict[str, Any]) -> dict[str, Any]:
    """verification_key.json: alpha, beta, gamma, delta and the IC points."""
    ensure(j.get('protocol') == 'groth16' and j.get('curve') in ('bn128', 'bn254'), 'not a snarkjs groth16/bn128 key')
    vk = {
        'alpha': g1(j['vk_alpha_1']),
        'beta': g2(j['vk_beta_2']),
        'gamma': g2(j['vk_gamma_2']),
        'delta': g2(j['vk_delta_2']),
        'ic': [g1(p) for p in j['IC']],
    }
    ensure(len(vk['ic']) == j.get('nPublic', -1) + 1, 'the key has IC points for a different number of public signals')
    return vk


def groth16_proof(j: dict[str, Any]) -> tuple[G1Point, B.G2Point, G1Point]:
    """proof.json: (A, B, C)."""
    ensure(j.get('protocol') == 'groth16' and j.get('curve') in ('bn128', 'bn254'), 'not a snarkjs groth16/bn128 proof')
    return (g1(j['pi_a']), g2(j['pi_b']), g1(j['pi_c']))


# fflonk
def fflonk_key(j: dict[str, Any]) -> dict[str, Any]:
    """verification_key.json: the domain's constants, C0 and [x]_2."""
    ensure(j.get('protocol') == 'fflonk' and j.get('curve') in ('bn128', 'bn254'), 'a snarkjs fflonk/bn128 key')
    vk: dict[str, Any] = {k: int(j[k]) for k in ('nPublic', 'power', 'k1', 'k2', 'w', 'w3', 'w4', 'w8', 'wr')}
    vk['C0'] = g1(j['C0'])
    vk['X_2'] = g2(j['X_2'])
    return vk


def fflonk_proof(j: dict[str, Any]) -> dict[str, Any]:
    """proof.json: the 4 points and the 15 evaluations, reduced mod r as snarkjs reads them."""
    ensure(j.get('protocol') == 'fflonk', 'a snarkjs fflonk proof')
    out: dict[str, Any] = {k: g1(j['polynomials'][k]) for k in FFLONK_POINTS}
    out.update({k: int(j['evaluations'][k]) for k in FFLONK_EVALS})
    return out
