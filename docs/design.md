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

The Groth16 verifier performs about 25,000 multiplications in the BN254 field, each made of several 256-bit jet calls, plus the data movement between them. At this scale the cost is decided by how values are laid out and moved, and the program has to control that precisely to fit the budget. That control is what the generator provides.

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

Almost all of the verifier's work has the shape of the second row. Hand-tuned SimplicityHL would bring the verifier to about 440 M mWU, beyond the 400 kWU limit, and idiomatic SimplicityHL to several times the budget.

The verifier also needs three things that a general compiler does not provide:

- Static bounds for soundness. The emulated field arithmetic is correct only while every intermediate value stays below a limit. The generator tracks an upper bound for every value and refuses to build a program that could overflow.
- One program per key. The verifying key's points become constants of the program (precomputed lines, lookup tables), so the program has to be generated for each key anyway.
- A model to test against. The same code that writes the program can compute its results on integers.

SimplicityHL remains a good fit for the contract around the verifier, for example a second taproot leaf with a timeout path.

### How the generator works

The generator is a Python library, `groth/`, that writes the program as text in Simplicity's human-readable encoding; rust-simplicity parses that text (`deploy compile`). It follows four principles.

1. **One description, two backends.** Each building block (a field product, a curve step, a step of the Miller loop) is written once against a small backend interface. The `Sym` backend (`sym.py`) turns the calls into Simplicity expressions and computes their exact cost. The `Num` backend runs the same calls on Python integers. The tests run both and check that the program computes exactly the model's numbers and costs exactly what the generator predicted.
2. **Explicit environments.** Values are bound with `let`, which adds them to the environment, or `scope`, which replaces the environment with just those values. Long computations are folded over balanced trees, so each step reads only its own data.
3. **Static bounds.** Every field value carries an upper bound. Each operation computes the bound of its result and checks it against the limit of the arithmetic. When a sum would overflow, its operands are normalised first; if a bound still cannot be met, the build stops with an error.
4. **Shared functions.** Repeated parts, such as a step of the Miller loop, are defined once as named functions and called with their data. This does not reduce cost, since every call executes, but it keeps the program at about 160 kB.

| module | what it builds |
|---|---|
| `dsl.py` | Simplicity text, balanced trees, witness files |
| `sym.py` | the two backends and the cost model |
| `fp.py` | BN254 field arithmetic |
| `tower.py` | the extension fields F_p2, F_p6, F_p12 |
| `curve.py` | curve steps, on-curve checks, the multi-scalar multiplication |
| `miller.py` | the Miller loop and the G2 membership check |
| `pairing.py` | the final check, without exponentiation |
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

A product costs about 13 k mWU, and a reduction about 7.8 k.

## Extension fields (tower.py)

Pairings work in F_p12, built in the usual tower: F_p2 = F_p[u]/(u² + 1), F_p6 = F_p2[v]/(v³ - (9 + u)), F_p12 = F_p6[w]/(w² - v). An element of F_p12 is a list of 12 F_p words.

The main design choice is one reduction per output coefficient, the minimum. A product of two F_p12 elements is a sum of F_p products, each landing in one of the 12 output coefficients, sometimes negated and sometimes multiplied by 9 + u. The generator writes each output coefficient as one dot product with a single reduction. To keep every term a plain product, it prepares variants of the right operand in advance: negated coefficients, and coefficients already multiplied by 9 + u. Squarings merge the symmetric terms.

Karatsuba multiplication was measured and rejected: it saves products but needs more reductions and negations than it saves.

## Curve arithmetic (curve.py)

Points are in affine coordinates, and the prover supplies the slope of every addition and doubling. Computing a slope normally needs a field inversion, which is expensive; checking a given slope needs only a multiplication:

```
addition:  λ * (x2 - x1) = y2 - y1,  with x1 != x2
doubling:  λ * 2y = 3x^2
```

With x1 != x2 checked, each equation has exactly one solution, so a slope that passes is the true one and every step is the group law: the prover has no freedom. Without the x1 != x2 check, adding a point to itself would let any slope pass.

Because words are not reduced, the program tests equality by checking that the difference of two words is one of the few multiples of p allowed by its bound.

## Miller loop (miller.py)

The Miller loop computes the product of the Miller functions of three pairs, (-A, B), (L, γ) and (C, δ). It runs along the signed-binary (NAF) digits of 6x + 2, the loop length of BN254's optimal ate pairing, and ends with two extra additions by Frobenius images of each G2 point. That is 88 steps: 65 doublings and 23 additions. The three pairs advance in lockstep, so the accumulator f is squared once per step for all of them.

Only B comes from the proof. Its steps use the prover's slopes, and the program computes its lines. γ and δ belong to the verifying key, so their slopes and lines are known when the program is generated and become constants: each step receives 36 data words for them.

Each line is used in affine form, `yP + (-λ * xP)·w + (λ * xT - yT) * v * w`. It differs from the textbook projective line by a factor in F_p2, which the final exponentiation would remove, so it gives the same pairing. The lines are multiplied in the order B, γ, δ, so that the line with the loosest bound meets the accumulator when its bound is smallest, and f is normalised once per step. The bounds that hold between steps are fixed points of one iteration; the generator finds them once with the numeric backend and checks them when it builds the program.

The loop also proves that B is in G2. Its last point is T = [6x+2]B + ψ(B) - ψ^2(B), where ψ is the Frobenius map carried over to the twist. On G2, ψ acts as multiplication by p, and 6x + 2 + p - p^2 + p^3 is a multiple of the group order, so there T = -ψ^3(B). Off G2 the two differ: the rest of the twist is a cyclic group of square-free order, and the map [6x+2] + ψ - ψ^2 + ψ^3 sends none of its points except the identity to the identity (tests/test_g2_check.py checks one point of each prime order). Comparing T with -ψ^3(B) costs about 0.15 M mWU.

A doubling step costs 3.6 M mWU, two thirds of it in its 261 field products. Alternatives that were measured and rejected: merging the lines before multiplying them in, a wider NAF (its extra Miller functions do not cancel), a loop along x instead of 6x + 2, and normalising B's coordinates.

## Final check without exponentiation (pairing.py)

The Groth16 equation holds if and only if the product of the Miller values, f, satisfies f^h = 1 with h = (p^12 - 1)/r. Computing that power, the final exponentiation, needs about 200 F_p12 squarings and products even with the usual shortcuts. The verifier avoids it with a residue witness ([Novakovic and Eagen, 2024](https://eprint.iacr.org/2024/640)). The prover supplies c in F_p12 and a 27th root of unity w with

```
f * w = c^λ,   λ = 6x + 2 + p - p^2 + p^3
```

Since r divides λ and 27 divides h, this equation implies f^h = 1, so checking it is enough.

The check is cheap because its expensive part rides on the Miller loop. The loop starts with f = c^(-1) instead of 1 and multiplies f by c or c^(-1) at each addition step, so that the squarings it does anyway raise c to -(6x + 2). After the loop the program multiplies in π(c^(-1)), π^2(c) and π^3(c^(-1)); the Frobenius maps π are cheap. It then compares the result with (w * e(α, β))^(-1), where w is one of three constants selected by two witness bits and `e(α, β)` stands for the Miller value of the key's fixed pair, so that pair costs nothing. c and c⁻¹ both come from the witness, and the program checks that c * c^(-1) = 1.

In total the residue witness adds about 51 M mWU: 42 M inside the loop (21 full F_p12 products) and 9 M before and after it.

## Public input and transaction binding (curve.py, merkle.py, groth16.py)

The point L = IC_0 + Σ a_i·IC_i combines the key's IC points with the public inputs a_i. The IC points are fixed, so the program uses precomputed tables: for every 5-bit digit d at position j of an input, it selects the point [(d + 1)·2^(5j)]·IC_i from a table with a case tree on the digit's bits, and adds it with a slope from the prover. The +1 keeps the point at infinity out of the tables, and a constant offset added to IC₀ cancels it. The inputs are checked to be below the group order. When the program is pruned for a spend, the table entries that were not selected disappear, so the tables cost nothing on chain. One public input costs 8.7 M mWU.

To need only one, a circuit for this verifier exposes a single public signal: the SHA-256 Merkle root of its public values, with the sighash of the spending transaction as leaf 0 and the top three bits cleared so that it fits the field (circuits/public_merkle.circom, merkle.py). The witness carries the sibling hashes of leaf 0, and the program recomputes the root from its `sig_all_hash` jet, which hashes the transaction it runs in. A proof is therefore valid for exactly one transaction: it cannot be replayed or redirected, and no signature is needed. This costs the program about 15 k mWU and the circuit about 59 k constraints per hashed node.

## Budget and padding (groth16.py)

The program costs far more than its own bytes and the proof earn in budget, so the witness carries padding: blocks of 512 zero bytes, each earning 512 k mWU. Elements does not relay transactions with an annex, the field rust-simplicity would use for padding, so the blocks go into the Simplicity witness. A witness value the program never reads would get the wrong type, so each block is hashed into a throwaway SHA-256 context, which costs 25.5 k mWU per block. `Groth16.padding` sizes the padding from the program's cost, and `deploy spend` reports whether the budget is covered.

The result is a transaction of about 382 kWU, under the 400 kWU limit. Execution needs at most 3.5 M cells of Bit Machine memory, under the 5.2 M consensus cap.

## Spending (tools/harness)

The coins sit in a taproot output with one Simplicity leaf (leaf version 0xbe, whose script is the program's commitment, the CMR), and by default an internal key nobody can sign with. `deploy compile` parses the program text once per key, which takes minutes, and stores the unpruned program. `deploy spend` prunes it against the actual transaction, executes it, and builds the spend in seconds. The input's witness stack holds the Simplicity witness, the pruned program, the CMR and the control block.
