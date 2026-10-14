# Design

This document explains how the verifier checks a Groth16 proof inside a Simplicity program, and why that program is produced by a designated Python generator instead of being written in SimplicityHL.

## Simplicity in brief

A Simplicity program is one large expression. Each expression takes an input value, called its environment, and produces an output value. Expressions are combined with a few combinators: `comp` runs one expression and feeds its output to the next, `pair` runs two expressions on the same input, `take` and `drop` select the left or right half of a value, and `case` branches on a bit. There are no loops and no variables. A computation that repeats is written out in full, and a value needed twice has to be kept in the environment and read twice.

Jets are built-in primitives with a fixed cost: SHA-256, 64-bit arithmetic, and arithmetic modulo the secp256k1 field prime and the secp256k1 group order. The verifier does all of its arithmetic with these secp256k1 jets.

Before a program runs, the node computes a static bound on its cost in milliweight units. Two properties of that cost model shape everything below:

- Cost counts every execution. An expression that appears once in the program text but is used twice costs twice; sharing text saves bytes, not cost.
- Moving data costs its size. Copying the environment, or passing a value from one expression to the next with `comp`, costs about 1 mWU per bit moved.

The cost must fit a budget of 1,000 mWU per byte of the spending input's witness, plus 50,000. The transaction must also stay below 400,000 weight units to be relayed.

## Python generator

The Groth16 verifier performs about 4,500 multiplications in the BN254 field, each made of several 256-bit jet calls, plus the data movement between them. At this scale the cost is decided by how values are laid out and moved, and the program has to control that precisely to fit the budget. That control is what the generator provides.

### Why not SimplicityHL

[SimplicityHL](https://github.com/BlockstreamResearch/SimplicityHL) was the obvious first choice. Its output, however, moves more data than this verifier can afford:

- Every `let` binding copies the whole environment, and the environment grows with every binding in scope.
- Every jet call passes its arguments through a `comp`, so the 512 bits of an operand pair are moved for each jet that reads them.

The generator avoids both. It narrows the environment to the values a step needs, and for a sum of products it packs all operand pairs into one tree once, then applies the multiplication jets in place, where the operands already lie:

```
SimplicityHL:  comp (pair a b) jet_fe_multiply     the operands are copied into a pair and passed on
generator:     take (drop (jet_fe_multiply))       the jet reads the pair where it already is
```

We measured the same arithmetic both ways, with SimplicityHL 0.8.0 and the same inputs:

| | this generator | SimplicityHL, idiomatic | SimplicityHL, hand-tuned |
|---|---:|---:|---:|
| one F_p product | 16,116 mWU | 32,492 (2.0x) | 18,440 (1.14x) |
| 12-term dot product, one reduction | 116,744 mWU | 472,888 (4.1x) | 141,332 (1.21x) |

Almost all of the verifier's work has the shape of the second row. Idiomatic SimplicityHL would make the verifier about four times as expensive, far beyond what its bytes pay for; hand-tuned SimplicityHL would add about 20%.

The verifier also needs three things that a general compiler does not provide:

- Static bounds for soundness. The emulated field arithmetic is correct only while every intermediate value stays below a limit. The generator tracks an upper bound for every value and refuses to build a program that could overflow.
- One program per key. The verifying key's points become constants of the program (precomputed lines, lookup tables), so the program has to be generated for each key anyway.
- A model to test against. The same code that writes the program can compute its results on integers.

SimplicityHL remains a good fit for the contract around the verifier, for example a second taproot leaf with a timeout path.

### How the generator works

The generator is a Python library, `groth/`, that writes the program as text in Simplicity's human-readable encoding; rust-simplicity parses that text (`deploy compile`). It follows four principles.

1. **One description, two backends.** Each building block (a field product, an on-curve check, a step of the Miller loop) is written once against a small backend interface. The `Sym` backend (`sym.py`) turns the calls into Simplicity expressions and computes their exact cost. The `Num` backend runs the same calls on Python integers. The tests run both and check that the program computes exactly the model's numbers and costs exactly what the generator predicted.
2. **Explicit environments.** Values are bound with `let`, which adds them to the environment, or `scope`, which replaces the environment with just those values. Long computations are folded over balanced trees, so each step reads only its own data.
3. **Static bounds.** Every field value carries an upper bound. Each operation computes the bound of its result and checks it against the limit of the arithmetic. When a sum would overflow, its operands are normalised first; if a bound still cannot be met, the build stops with an error.
4. **Shared functions.** Repeated parts, such as a step of the Miller loop, are defined once as named functions and called with their data. This does not reduce cost, since every call executes, but it keeps the program at about 60 kB.

| module | what it builds |
|---|---|
| `dsl.py` | Simplicity text, balanced trees, witness files |
| `sym.py` | the two backends and the cost model |
| `fp.py` | BN254 field arithmetic |
| `poly.py` | F_p12 as polynomials modulo w^12 - 18w^6 + 82 |
| `curve.py` | on-curve checks, the multi-scalar multiplication |
| `pairing.py` | the pairing check as one polynomial identity |
| `groth16.py` | the whole verifier, transaction binding, padding |
| `merkle.py` | the public-signal convention |
| `bn254.py` | the plain-Python reference everything is tested against |

The rest of this document follows the layers from the bottom up.

## Field arithmetic (fp.py)

Every number in the verifier lives in the BN254 base field, modulo a 254-bit prime p, but Simplicity only has jets modulo two other primes: the secp256k1 field prime p_s and the secp256k1 group order n_s, both just below 2^256. The generator therefore emulates arithmetic modulo p with them.

An element x is stored as a 256-bit word X with X = x·R mod p, where R = p_s: the Montgomery form of x. X is not reduced below p; instead the generator knows an upper bound for it.

To multiply two elements A and B, the program needs their exact product S = A·B, which has up to 512 bits. One jet gives S mod p_s (`fe_multiply`) and another gives S mod n_s (`scalar_multiply`); these two residues are all the reduction needs. Montgomery reduction turns them into a word for A·B·R⁻¹ mod p, the Montgomery form of the product, without any division modulo p:

```
m = (S mod p_s) * (-p^(-1) mod p_s)  mod p_s
Q = (S + m * p) / p_s                         an exact division: S + m * p is a multiple of p_s
  = (S mod n_s + m·p) * p_s^(-1)  mod n_s     exact while Q < n_s
```

The result Q is computed modulo n_s, so it is the true value only if it is below n_s. That condition is what the static bounds guarantee: the generator checks the bound of every product and sum before it emits the code. A wrong bound would let a value wrap around, and a dishonest prover could exploit that.

A sum of products is accumulated in both residues and reduced once, so a dot product of 12 terms costs one reduction. Subtraction adds a multiple of p first, so values never go negative. This is the two-modulus case of RNS Montgomery multiplication ([Bajard, Didier and Kornerup, 1998](https://doi.org/10.1109/12.709376)); here its usual conversions between the two moduli are free, because the jets read any 256-bit word.

Words taken straight from the witness can be any 256-bit value. The jets reduce their inputs, so this is safe, and the program normalises such a word (multiplies it by the constant 1) before using it, which brings it below 1.3 p.

Because words are not reduced, the program tests whether a value is zero by comparing it with the few multiples of p its bound allows.

A product costs about 13 k mWU, and a reduction about 7.8 k.

## F_p12 as polynomials (poly.py)

Pairings take values in F_p12. Its textbook construction is a tower of extensions: F_p2 = F_p[u]/(u^2 + 1), F_p6 = F_p2[v]/(v^3 - (9 + u)), F_p12 = F_p6[w]/(w^2 - v). The verifier uses the same field in a flat form. Since w^6 = v^3 = 9 + u, the element u is w^6 - 9, and u^2 = -1 becomes

```
M(w) = w^12 - 18 w^6 + 82 = 0
```

So F_p12 = F_p[w]/M(w): an element is a polynomial of degree at most 11 with coefficients in F_p, and a product is the polynomial product reduced modulo M. F_p2 sits inside as the polynomials a0 + a1 (w^6 - 9). This is the representation py_ecc uses, and the tests check the map from the tower against it.

The flat form matters because a polynomial identity can be checked at a single point. If A B = C in F_p12, then A(w) B(w) = C(w) + Q(w) M(w) for a quotient polynomial Q, and at any number z this becomes one equation in F_p: A(z) B(z) = C(z) + Q(z) M(z). An F_p12 product, which costs about 1.6 M mWU when computed coefficient by coefficient, becomes one F_p product of two evaluations. The Frobenius maps π, π^2, π^3 are linear maps on the coefficients with one or two terms each.

## The pairing check (pairing.py)

The Groth16 equation e(A, B) = e(α, β) e(L, γ) e(C, δ) holds if and only if the product f of four Miller functions satisfies f^h = 1, h = (p^12 - 1)/r. The prover runs the Miller loop off-chain and writes every intermediate value into the witness. The program does not recompute the loop; it checks that every step of it holds, all at once, at one random point.

### The steps as relations

The Miller loop runs along the signed-binary (NAF) digits of 6x + 2, the loop length of BN254's optimal ate pairing, and ends with two additions by Frobenius images of each G2 point: 88 steps, 65 doublings and 23 additions. The three pairs (-A, B), (L, γ) and (C, δ) advance in lockstep, so the accumulator f is squared once per step for all of them. The fourth pair, (α, β), belongs to the verifying key; its Miller value is a constant of the program.

Each step multiplies f (squared, for a doubling) by three lines, one per pair, each of the form `yP + c3 xP w + c4 w^3` with c3 = -λ and c4 = λ xT - yT, where T is the pair's running G2 point and λ the slope of the step. When the prover writes the new value f' into the witness, the step becomes a relation between polynomials:

```
f^2 l_B l_γ l_δ - f' = 0   (mod M)
```

The prover does not commit after every step. Without a commitment, f' is the product itself, a polynomial of higher degree that the next relation carries along, and that next relation checks two steps at once. A committed value costs 12 witness words; a higher degree costs words of the quotient (below). The generator skips a commitment whenever the identity's degree stays within 211, the cap with the fewest words in total: 35 of the 88 Miller values are committed.

γ and δ belong to the key, so their slopes and lines are computed when the program is generated: each step receives c3 and c4 for both, four words each. B comes from the proof. The prover writes only B's slopes; B's points are never written down. The new point of a doubling is x' = λ^2 - 2x, y' = λ (x - x') - y, a polynomial in the slopes, and the program checks each slope instead:

```
doubling:  λ y - 3/2 x^2 = 0
addition:  λ (xQ - x) - (yQ - y) = 0
```

Each slope equation has exactly one solution, so a slope that passes is the true one and every step is the group law: the prover has no freedom. For a doubling this is because y is never 0 (the twist has no points of order 2). For an addition it needs xQ != x, and that holds at every addition of the loop, for every point B of the twist, so the program does not check it. The twist's group of points is cyclic, of order r h with h = 10069 · 5864401 · 1875725156269 · (a 177-bit prime). At an addition, T = [k] B and Q = [q] B, with q = ±1 for the additions of ±B. For the Frobenius additions of ψ(B) and -ψ^2(B), q = μ and -μ^2, where μ is the eigenvalue by which ψ acts on each prime part of the group. T = Q needs an order of B that divides k - q, so some prime of r h that divides k - q, and tests/test_g2_check.py finds none for any of the 23 additions. (T = -Q makes the slope equation 0 = 2 yQ, which fails.) An earlier version had the prover supply an inverse d with (xQ - x) d - 1 = 0: 23 words of F_p2 and 23 relations, which this argument makes unnecessary. All of this F_p2 arithmetic is polynomial arithmetic modulo M too, since F_p2 sits inside F_p12, so these relations join the same identity.

### No final exponentiation

Computing f^h directly would take about 200 F_p12 squarings and products. The verifier uses a residue witness instead ([Novakovic and Eagen, 2024](https://eprint.iacr.org/2024/640)): the prover supplies c in F_p12 and a 27th root of unity w with

```
f w = c^λ,   λ = 6x + 2 + p - p^2 + p^3
```

Since r divides λ and 27 divides h, this equation implies f^h = 1. The loop starts with f = c^(-1) and multiplies f by c or c^(-1) at each addition step, so that its squarings raise c to -(6x + 2). After the loop, one more relation checks f π(c^(-1)) π^2(c) π^3(c^(-1)) against (w e(α, β))^(-1), one of three constants selected by two witness bits, and another checks c c^(-1) = 1.

### B is in G2

The loop also proves that B is in G2. Its last point is T = [6x+2]B + ψ(B) - ψ^2(B), where ψ is the Frobenius map carried over to the twist. On G2, ψ acts as multiplication by p, and 6x + 2 + p - p^2 + p^3 is a multiple of the group order, so there T = -ψ^3(B). Off G2 the two differ: the rest of the twist is a cyclic group of square-free order, and the map [6x+2] + ψ - ψ^2 + ψ^3 sends none of its points except the identity to the identity (tests/test_g2_check.py checks one point of each prime order). Two relations compare T with -ψ^3(B).

### One identity, checked at one point

That makes 127 relations R_k, each a polynomial in w of degree at most 211. The prover combines them with the powers of a challenge r into S = Σ r^k R_k, divides S by M, and writes the quotient Q (200 coefficients) into the witness. The program then picks a point z, evaluates every polynomial at z, and checks

```
S(z) = Q(z) M(z)
```

This is randomized extension-field arithmetic: [Garaga](https://hackmd.io/@feltroidprime/B1eyHHXNT) checks each F_p12 product with its own quotient, and Novakovic and Eagen (section 6) combine all relations into one quotient, as here. Two things are specific to this verifier: the challenges come from SHA-256 inside the program, and B's F_p2 arithmetic is part of the same identity, so B's points never enter the witness.

The program never multiplies in F_p12. A committed value f' becomes the number f'(z), a 12-term dot product with the powers of z; a line becomes a number; a step's relation becomes a few F_p products, added to a running Horner sum of S(z). A doubling step costs 0.39 M mWU, or 0.61 M with a commitment, against 3.6 M for computing it in the tower. Q(z) is evaluated eight coefficients at a time by one shared function, so its code is in the program once.

r and z come from SHA-256 (Fiat-Shamir): r hashes the public inputs, the proof, c, c^(-1), s and everything the loop committed, and z hashes r and Q. The program gets r and z as witness words, uses them throughout, and at the end compares them with the two hashes it has computed along the way. If some relation does not hold, S is nonzero modulo M except for at most 127 values of r, and then S - Q M is a nonzero polynomial of degree at most 211, which vanishes at z with probability at most 211/p. A cheating prover must find a hash output in a set of relative size about 2^-245.

The committed words are checked to be below 2^254 (their two top bits are zero), so that the 12-term dot products fit the bound of the field arithmetic; every canonical word passes. The program normalises the challenges, whose words are arbitrary 256-bit hashes.

The witness is 28 kB: the committed Miller values (13 kB), the quotient (6 kB), B's slopes (6 kB) and the rest of the proof. The program is 60 kB; the line data of γ and δ, four words per pair and step, is 22 kB of it.

## Public input and transaction binding (curve.py, merkle.py, groth16.py)

The point L = IC_0 + Σ a_i·IC_i combines the key's IC points with the public inputs a_i. The IC points are fixed, so the program uses precomputed tables: for every 5-bit digit d at position j of an input, it selects the point [(d + 1)·2^(5j)]·IC_i from a table with a case tree on the digit's bits, and adds it with a slope from the prover. The +1 keeps the point at infinity out of the tables, and a constant offset added to IC₀ cancels it. The inputs are checked to be below the group order. When the program is pruned for a spend, the table entries that were not selected disappear, so the tables cost nothing on chain. One public input costs 8.7 M mWU.

To need only one, a circuit for this verifier exposes a single public signal: the SHA-256 Merkle root of its public values, with the sighash of the spending transaction as leaf 0 and the top three bits cleared so that it fits the field (circuits/public_merkle.circom, merkle.py). The witness carries the sibling hashes of leaf 0, and the program recomputes the root from its `sig_all_hash` jet, which hashes the transaction it runs in. A proof is therefore valid for exactly one transaction: it cannot be replayed or redirected, and no signature is needed. This costs the program about 15 k mWU and the circuit about 59 k constraints per hashed node.

## Budget and padding (groth16.py)

The program costs 66.7 M mWU. Its budget is 1,000 mWU per byte of the input's witness stack, so the 60 kB program and the 28 kB witness already earn about 88 M mWU, and no padding is needed: the transaction weighs about 89 kWU.

Programs that cost more than their bytes earn can still be padded. Elements does not relay transactions with an annex, the field rust-simplicity would use for padding, so the blocks of 512 zero bytes go into the Simplicity witness. A witness value the program never reads would get the wrong type, so each block is hashed into a throwaway SHA-256 context, which costs 25.5 k mWU per block. `Groth16.padding` sizes the padding from the program's cost, and `deploy spend` reports whether the budget is covered.

## Spending (tools/harness)

The coins sit in a taproot output with one Simplicity leaf (leaf version 0xbe, whose script is the program's commitment, the CMR), and by default an internal key nobody can sign with. `deploy compile` parses the program text once per key, which takes minutes, and stores the unpruned program. `deploy spend` prunes it against the actual transaction, executes it, and builds the spend in seconds. The input's witness stack holds the Simplicity witness, the pruned program, the CMR and the control block.
