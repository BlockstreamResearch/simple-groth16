#!/usr/bin/env python3
"""F_p12 as F_p[w] / (w^12 - 18 w^6 + 82) (groth/poly.py) against the tower of bn254.py: the map between
them is a ring isomorphism, F_p2 embeds through phi, the lines embed, and pi, pi^2, pi^3 are the sparse
linear maps the program uses.  (tests/test_bn254_ref.py also checks the map against py_ecc, whose FQ12 is
this field.)

    python3 tests/test_poly.py
"""
import os, random, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from groth import bn254 as B, poly

P = B.P


def main():
    rng = random.Random(1)
    fp2 = lambda: B.Fp2(rng.randrange(P), rng.randrange(P))
    fp12 = lambda: B.Fp12(B.Fp6(fp2(), fp2(), fp2()), B.Fp6(fp2(), fp2(), fp2()))
    for _ in range(20):
        a, b = fp12(), fp12()
        da, db = poly.from_tower(a), poly.from_tower(b)
        assert poly.to_tower(da) == a
        prod = poly.mul(da, db)
        assert poly.reduce(prod) == poly.from_tower(a * b)
        q, r = poly.divmod_m(prod)
        assert poly.add(poly.mul(q, poly.M), r) == prod and len(r) == 12
        z = rng.randrange(P)
        assert poly.evaluate(prod, z) == poly.evaluate(da, z) * poly.evaluate(db, z) % P
        # F_p2 through phi: a ring map into F_p[w] / M
        x, y = fp2(), fp2()
        assert poly.reduce(poly.mul(poly.phi(x), poly.phi(y))) == poly.reduce(poly.phi(x * y))
        assert poly.reduce(poly.phi(x)) == poly.from_tower(B.Fp12(B.Fp6(x)))
        # the line c0 + c3 w + c4 v w is yP + c3(w) xP w + c4(w) w^3
        yp, xp = rng.randrange(P), rng.randrange(P)
        tower = B.Fp12.one().mul_by_034(B.Fp2(yp), x * xp, y)
        direct = poly.add(poly.add(poly.const(yp), poly.scale(poly.mul(poly.phi(x), poly.X), xp)), poly.mul(poly.phi(y), [0, 0, 0, 1]))
        assert poly.reduce(direct) == poly.from_tower(tower)
        # Frobenius maps
        for n in (1, 2, 3):
            image = [0] * 12
            for j, cj in enumerate(da):
                for k, g in enumerate(poly.FROB[n][j]):
                    image[k] = (image[k] + cj * g) % P
            assert image == poly.from_tower(a.frobenius(n)), n
    terms = {n: max(sum(1 for g in row if g) for row in poly.FROB[n]) for n in (1, 2, 3)}
    assert terms == {1: 2, 2: 1, 3: 2}, terms
    print('direct extension ok: the tower map is a ring isomorphism; pi^n(w^j) has at most', terms, 'terms')


if __name__ == '__main__':
    main()
