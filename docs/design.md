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
2. **Explicit environments.** Values are bound with `let`, which adds them to the environment, or `scope`, which replaces the environment with just those values. A value read in one place only is a witness node of its own, read where it is used: each of the 88 steps of the loop reads its leaf (B's slope, and a committed value) from its own node, and the end reads Q from one, so they are never carried through the environment.
3. **Static bounds.** Every field value carries an upper bound. Each operation computes the bound of its result and checks it against the limit of the arithmetic. When a sum would overflow, its operands are normalised first; if a bound still cannot be met, the build stops with an error.
4. **Shared functions.** Repeated parts, such as a step of the Miller loop, are defined once as named functions and called with their data. This does not reduce cost, since every call executes, but it keeps the pruned program at 34 kB.

| module | what it builds |
|---|---|
| `dsl.py` | Simplicity text, balanced trees, witness files |
| `sym.py` | the two backends and the cost model |
| `fp.py` | BN254 field arithmetic |
| `poly.py` | F_p12 as polynomials modulo w^12 - 18w^6 + 82 |
| `curve.py` | on-curve checks, constant tables selected by the bits of a word, the range check of an input |
| `pairing.py` | the pairing check as one polynomial identity |
| `groth16.py` | the whole verifier and the transaction binding |
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

The flat form matters because a polynomial identity can be checked at a single point. If A B = C in F_p12, then A(w) B(w) = C(w) + Q(w) M(w) for a quotient polynomial Q, and at any number z this becomes one equation in F_p: A(z) B(z) = C(z) + Q(z) M(z). An F_p12 product, which costs about 1.6 M mWU when computed coefficient by coefficient, becomes one F_p product of two evaluations. The Frobenius maps π, π^2, π^3 are ring homomorphisms that fix F_p, so π^n(a) is a(t_n) modulo M, where t_n = π^n(w) has one or two terms: t_1 = a w + b w^7, t_2 = g w and t_3 = g t_1, with g a sixth root of unity.

## The pairing check (pairing.py)

The Groth16 equation e(A, B) = e(α, β) e(L, γ) e(C, δ) holds if and only if f^h = 1, h = (p^12 - 1)/r, for the product f of the Miller functions of (-A, B) and (C, δ), the Miller value of (α, β), and a product of constants that stands for e(L, γ) (below). The prover runs the Miller loop off-chain and writes every intermediate value into the witness. The program does not recompute the loop; it checks that every step of it holds, all at once, at one random point.

### The steps as relations

The Miller loop runs along the signed-binary (NAF) digits of 6x + 2, the loop length of BN254's optimal ate pairing, and ends with two additions by Frobenius images of each G2 point: 88 steps, 65 doublings and 23 additions. The two pairs (-A, B) and (C, δ) advance in lockstep, so the accumulator f is squared once per step for both. The pair (α, β) belongs to the verifying key; its Miller value is a constant of the program. The pair (L, γ) has no loop at all: its pairing is a product of constants selected by the public inputs, multiplied in at some of the additions (see The public inputs' term).

Each step multiplies f (squared, for a doubling) by two lines, one per pair, each of the form `yP + c3 xP w + c4 w^3` with c3 = -λ and c4 = λ xT - yT, where T is the pair's running G2 point and λ the slope of the step. When the prover writes the new value f' into the witness, the step becomes a relation between polynomials:

```
f^2 l_B l_δ - f' = 0   (mod M)
```

The prover does not commit after every step. Without a commitment, f' is the product itself, a polynomial of higher degree that the next relation carries along, and that next relation checks two steps at once. A committed value costs 6 witness words (it is compressed, below); a higher degree costs words of the quotient. Every addition commits its value (most would anyway, and so one function serves all additions), and a doubling skips its commitment whenever the identity's degree stays within 171, the degree of the largest relation once two doublings go uncommitted: 37 of the 88 Miller values are committed.

δ belongs to the key, so its slopes and lines are computed when the program is generated: each step receives its c3 and c4, four words. B comes from the proof. The prover writes only B's slopes; B's points are never written down. The new point of a doubling is x' = λ^2 - 2x, y' = λ (x - x') - y, a polynomial in the slopes, and the program checks each slope instead:

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

Since r divides λ and 27 divides h, this equation implies f^h = 1. The loop starts with f = c^(-1) and multiplies f by c or c^(-1) at each addition step, so that its squarings raise c to -(6x + 2). After the loop, one more relation checks f π(c^(-1)) π^2(c) π^3(c^(-1)) against (w e(α, β))^(-1). The program evaluates the Frobenius images at z by composition, π^n(a)(z) = a(t_n(z)), with Horner's rule, which needs the two or three constants of t_n instead of the 45 of the Frobenius matrices. As polynomials, these images have degree 70 for n = 1, 3, so the last Miller value is committed to keep this relation within the degree cap.

### Miller values in the torus

The relations are not about f itself but about u = E(f) = f^(p^6 - 1) = conj(f)/f, where conj, the Frobenius map π^6, sends w to -w. That is enough. E multiplies, commutes with π, and kills F_p6, so the residue check after E reads E(y) = c'^λ for the product y of everything above and c' = E(c). Then y^h = E(y)^((p^6 + 1)/r) = (c'^(p^6 + 1))^(λ/r) = 1, because c' lies in the torus T2 = {u : u conj(u) = 1}, a cyclic group of order p^6 + 1. Conversely, gcd(λ/r, (p^6 + 1)/r) = 1, so an honest y always has such a c', E of Novakovic and Eagen's c.

The torus makes the witness smaller. Every element of T2 other than 1 is (a + w)/(a - w) for a single a in F_p6, a = w (u + 1)/(u - 1), and an element of F_p6 is a polynomial in w^2: 6 coefficients instead of 12. So the prover commits a for each committed value and a_c for c'. The inverse of c' is its conjugate, (a_c - w)/(a_c + w), so c^(-1) leaves the witness. And 3 does not divide p^6 + 1, so the 27th root of unity w has E(w) = 1: the two selector bits and the table of three constants go, and the end relation compares with one constant τ, E of the inverse of the constants (α, β)'s Miller value and the inputs' term contribute, compressed as well.

The program keeps u as a fraction N/D of two polynomials:

- A doubling squares both, and multiplies N by conj(L) and D by L, where L is the product of the two lines: E(L) = conj(L)/L.
- An addition multiplies them by (a_c - w, a_c + w) or (a_c + w, a_c - w).
- A committed value a gives the relation N (a - w) - D (a + w) = 0, and N and D start again from a + w and a - w.

D is always N with w replaced by -w (up to a sign, which each factor of the inputs' term flips), so in N (a - w) - D (a + w) one of the two halves, the even or the odd powers of w, cancels, and the relation's degree is 9 below that of the product. The generator's degree count follows both halves.

A line is yP + o with o its odd part (yP ∈ F_p is the even part), so its conjugate is yP - o. The program evaluates o once and gets both. N and D are never 0: every line has the nonzero constant term yP, and a ± w is not 0 because w is not in F_p6. Keeping two values instead of one costs each step about 50 k mWU, 4 M in all, and saves 7.4 kB of witness. (u = 1 has no compressed form; an honest prover meets it with probability about 1/p^6, and then fails.)

### B is in G2

The loop also proves that B is in G2. Its last point is T = [6x+2]B + ψ(B) - ψ^2(B), where ψ is the Frobenius map carried over to the twist. On G2, ψ acts as multiplication by p, and 6x + 2 + p - p^2 + p^3 is a multiple of the group order, so there T = -ψ^3(B). Off G2 the two differ: the rest of the twist is a cyclic group of square-free order, and the map [6x+2] + ψ - ψ^2 + ψ^3 sends none of its points except the identity to the identity (tests/test_g2_check.py checks one point of each prime order). Two relations compare T with -ψ^3(B). That point needs no constants of its own: ψ^2 multiplies x by a cube root of unity and negates y, so -ψ^3(B) = -ψ^2(ψ(B)) is ψ(B) with x scaled, and ψ(B) is the point the first Frobenius addition uses.

### The public inputs' term

L = IC_0 + Σ x_i IC_i depends on the public inputs, but γ does not. By bilinearity e(L, γ) = e(IC_0, γ) Π e(IC_i, γ)^(x_i), a product of powers of constants of GT, so γ needs no Miller loop and L is never computed. K_i = e(IC_i, γ)^(h^(-1) mod r) is an element of the group of order r whose h-th power is e(IC_i, γ); the product f takes K_0 Π K_i^(x_i) in place of (L, γ)'s Miller value.

Each input is cut into windows of 8 bits. For the digit d at bits 8j to 8j + 7 of x_i, the relations multiply u by E(K_i^((d + 1) 2^(8j))), which the program selects from a table of 256 with a case tree on the digit's bits (curve.py). The +1 keeps 1, which has no compressed form, out of the tables, and the end's constant takes the offset. When the program is pruned for a spend, a window keeps the entry it selected and the commitments of the eight branches it did not take.

The factors have order r, so they lie in the cyclotomic subgroup T6 of order p^4 - p^2 + 1, which needs fewer words than T2. Write u = (s + 1)/(s - 1) with s odd, s = b0 w + b1 w^3 + b2 w^5 for b_i in F_p2. Then u is in T6 exactly when b0 b2 - b1^2 = κ = 1/(3ξ), so b1 and b2, 4 words, fix the factor, and multiplying by b2 gives it without a division: (σ + b2)/(σ - b2) with σ = (κ + b1^2) w + b1 b2 w^3 + b2^2 w^5. A shared function evaluates σ ± b2 at z.

The factors join the additions: an addition multiplies N and D by g_N and g_D already, and its windows' factors multiply them further, which raises that relation's degree by 17 or 8 per factor. The generator gives each addition as many windows as its relation has room for under the degree cap, the additions with the most room first: 7 additions, with 3 to 7 windows each, for one input. A factor multiplied in before k more doublings is squared k times by the loop, so its table holds the 2^k-th root of the factor, which exists in a group of odd order. The six top bits of the first input select the end's constant instead: τ is a table of 64 that also absorbs e(IC_0, γ), the offsets and (α, β).

For one input, this replaces the MSM in G1 (5.3 M mWU, 32 slopes in the witness) and γ's line constants (11.3 kB, and a line per step) with 31 table factors of 4 words. Each further input adds 32 windows with entries of 4 words where G1 needed 2, and more room in the relations, so with more than about five inputs the MSM in G1 would be lighter; the transaction-bound circuits have one. Each input adds about 6 M mWU and 14 kB to the pruned program (61.4 M mWU and 62 kB with three). With three or more, some additions carry ten or more windows, and the product of their factors is normalised partway, so that it stays within the bound of the field arithmetic. The program text grows by 2.6 MB per input, and its parse time with it: about 25 minutes for three inputs.

### One identity, checked at one point

That makes 128 relations R_k, each a polynomial in w of degree at most 171. The prover combines them with the powers of a challenge r into S = Σ r^k R_k, divides S by M, and writes the quotient Q into the witness: 160 coefficients, a multiple of 8 (with more inputs, the cap and Q grow). The program then picks a point z, evaluates every polynomial at z, and checks

```
S(z) = Q(z) M(z)
```

This is randomized extension-field arithmetic: [Garaga](https://hackmd.io/@feltroidprime/B1eyHHXNT) checks each F_p12 product with its own quotient, and Novakovic and Eagen (section 6) combine all relations into one quotient, as here. Two things are specific to this verifier: the challenges come from SHA-256 inside the program, and B's F_p2 arithmetic is part of the same identity, so B's points never enter the witness.

The program never multiplies in F_p12. A committed value a becomes the number a(z), a 6-term dot product with the even powers of z; a line becomes two numbers, at z and -z; a step's relation becomes a few F_p products, added to a running Horner sum of S(z). A doubling step costs 0.32 M mWU, or 0.47 M with a commitment, against 3.6 M for computing it in the tower. Q(z) is evaluated eight coefficients at a time by one shared function, so its code is in the program once.

r and z come from SHA-256 (Fiat-Shamir): r hashes the public inputs, the proof, a_c and everything the loop committed, and z hashes r and Q. The program gets r and z as witness words, uses them throughout, and at the end compares them with the two hashes it has computed along the way. If some relation does not hold, S is nonzero modulo M except for at most 128 values of r, and then S - Q M is a nonzero polynomial of degree at most 171, which vanishes at z with probability at most 171/p. A cheating prover must find a hash output in a set of relative size about 2^-245.

The committed words are checked to be below 2^254 (their two top bits are zero), so that the dot products fit the bound of the field arithmetic; every canonical word passes. The program normalises the challenges, whose words are arbitrary 256-bit hashes.

The witness is 18 kB: the committed values (7 kB), the quotient (5 kB), B's slopes (6 kB) and the rest of the proof. The program is 34 kB; the line data of δ, four words per step, is 11 kB of it, and the inputs' tables, with their pruned branches, 12 kB.

### The size of the program

Since the program earns more budget than it costs, the transaction's weight is its bytes, and the program is written to be small:

- A constant of several words is one wide constant, a single node with all the bits, instead of a tree of 2n - 1 nodes: the line data of each step (4 words), each entry of the inputs' tables (4 words), each τ (4 + 2 words).
- Code that would repeat is a function: three step functions (a doubling with and without a commitment, an addition), Q(z) eight coefficients at a time, a(t) for an element of F_p6 by Horner's rule (a_c at z, t_1, t_2 and t_3, and τ at z), the pair σ ± b2 of a table factor, and the range check of 6 committed words. A function costs about 0.5 kB of code; the Frobenius additions run the addition's function with g = 1.
- A function's intermediate values are pushed in front of its environment instead of being copied into a new one, so the values it only reads stay where they are.
- A function's environment holds only what it reads, since every node that passes the environment on costs its width. The loop state carries 22 values computed once in the setup (powers of z, the points at z, a_c(z) ± z, r and r^2) and the public input; a step function gets the 9 that every step reads, or those and the 7 that only a committed step reads, and the loop passes the rest around it. z^5, z^7 and r^3, which only the end reads, and -B and -π^2(B), which one or a few steps read, are not carried at all: the first are kept beside the loop, the others are computed where they are used.
- A table window takes its 8 bits from the input as one projection of the byte, and a function shared by all windows turns them into the digit as a nested sum, T_8 with T_k = T_(k-1) + T_(k-1): each level of the case tree then sees the next level's input directly, without a `drop`.
- Steps of the same kind share their code: a step passes its line constants of δ, one wide constant, to the code of its kind, so a step adds only that constant and the three nodes that pass it. The 7 additions with windows have code of their own.
- The setup takes -ψ^3(B) from ψ(B) and the Frobenius images from t_n, as above: three constants where it held about fifty.

## Public input and transaction binding (curve.py, merkle.py, groth16.py)

The public inputs enter through the inputs' term of the pairing check (above): tables of constants of GT, selected by their bits. The inputs are checked to be below the group order. When the program is pruned for a spend, the table entries that were not selected disappear, so the tables cost nothing on chain: a window keeps its entry (128 bytes) and the commitments of the eight branches it did not take (32 bytes each). One public input takes 31 windows and the τ table, 12 kB in all, and costs about 5.7 M mWU; 8 bits is the width with the fewest bytes whose program text still parses in a few minutes.

To need only one, a circuit for this verifier exposes a single public signal: the SHA-256 Merkle root of its public values, with the sighash of the spending transaction as leaf 0 and the top three bits cleared so that it fits the field (circuits/public_merkle.circom, merkle.py). The witness carries the sibling hashes of leaf 0, and the program recomputes the root from its `sig_all_hash` jet, which hashes the transaction it runs in. A proof is therefore valid for exactly one transaction: it cannot be replayed or redirected, and no signature is needed. This costs the program about 15 k mWU and the circuit about 59 k constraints per hashed node.

A key compiled with `--unbound` has none of this. Its public inputs are whatever the spender proves, so the statement's constants must be fixed in the circuit, and a broadcast witness can be reused in any transaction to the same output. `tools/groth16_snarkjs.py` therefore binds unless `--unbound` is given, also for `PublicMerkleRoot(0)`, whose tree holds only the sighash.

## Budget

The program costs 48.6 M mWU. Its budget is 1,000 mWU per byte of the input's witness stack, so the 34 kB program and the 18 kB witness already earn about 52.7 M mWU: the verifier needs no padding, and the transaction weighs about 53 kWU. More public inputs keep it that way, since each one adds more bytes (its tables, about 14 kB) than cost (about 6.6 M mWU). `tests/test_groth16.py` checks that the budget covers the cost, and `deploy spend` reports it for a real transaction.

## Spending (tools/harness)

The coins sit in a taproot output with one Simplicity leaf (leaf version 0xbe, whose script is the program's commitment, the CMR), and by default an internal key nobody can sign with. `deploy compile` parses the program text once per key, which takes minutes, and stores the unpruned program, with the names of its witness nodes in the order its encoding reads their values (`.wnames`). `deploy spend` binds the witness file's values to those nodes, prunes the program against the actual transaction, executes it, and builds the spend in seconds. The input's witness stack holds the Simplicity witness, the pruned program, the CMR and the control block.
