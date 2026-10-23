# The fflonk verifier

`groth/fflonk.py` generates a Simplicity verifier for [snarkjs](https://github.com/iden3/snarkjs) 0.7.6 fflonk proofs on BN254. fflonk's setup is universal: a circuit needs a powers-of-tau file of the right size and no ceremony of its own. The price is a larger verifier than Groth16's.

The verifier has two transcript modes:

- **keccak** checks proofs from snarkjs as it is. Its Fiat-Shamir transcript hashes with Keccak-256, which Simplicity has no jet for, so the program computes Keccak-f[1600] from 64-bit jets (`groth/keccak.py`).
- **sha256** checks proofs whose transcript hashes with SHA-256 instead. `tools/snarkjs_sha256.mjs` makes them: it is snarkjs with the transcript's hash swapped. Such proofs no longer verify with snarkjs's own verifier or its Solidity verifier.

## Cost

Measured in `hand` on the toy circuit `circuits/multiplier_fflonk.circom` (3 public inputs). The generator predicts each cost exactly.

| | fflonk, SHA-256 | fflonk, Keccak | Groth16 (for reference) |
|---|---:|---:|---:|
| ranges and on-curve checks | 0.5 M | 0.5 M | |
| transcript | 0.3 M | 49.1 M | |
| opening (F_r) | 6.0 M | 6.0 M | |
| MSM | 73.4 M | 73.4 M | |
| pairing check | 42.9 M | 42.9 M | |
| binding | 0.1 M | 0.1 M | |
| **cost before padding** | **123.2 M mWU** | **172.0 M mWU** | **48.6 M mWU** |
| pruned program | 66 kB | 75 kB | 34 kB |
| witness, before padding | 45 kB | 45 kB | 18 kB |

The verifier costs more than its program and witness weigh, so a spend pads its witness (below): about 2.4 M mWU of padding with SHA-256, and the transaction weighs about the cost, 1 WU per 1,000 mWU, under the 400 kWU standard limit.

## How it works

The program checks what snarkjs's `fflonkVerify` checks. `groth/fflonk_ref.py` is a line-by-line Python port of it, and the tests compare the program with the port on every intermediate value.

### Inputs and transcript

The witness holds the public inputs, the points C1, C2 and W1, the 15 evaluations and the five challenges, each as a canonical word. The program checks the words below r and the coordinates below p, and the points on the curve.

Each challenge is the transcript's digest, reduced mod r. The prover supplies the reduced challenge, the program hashes the transcript and checks digest = word (mod r). The next transcript absorbs the word, as snarkjs absorbs the reduced challenge.

Keccak-f[1600] takes about 120 jets per round: `xor_xor_64` for theta's column parities, `xor_64`, `left_rotate_64` for rho, and `ch_64` for chi, since b0 ^ (~b1 & b2) = ch(b1, b0, b0 ^ b2). A round is one function, ROUND, called 24 times by KECCAKF. The state is a balanced tree of the 25 lanes, each holding its 8 bytes little-endian. A 32-byte big-endian word becomes 4 lanes by re-pairing byte projections, with no jet. One permutation costs 5.25 M mWU, and the jets are only 11 k of each round's 220 k: the rest is moving lanes. fflonk's transcript needs 9 permutations. The same code is published on its own as [simple-keccak](https://github.com/BlockstreamResearch/simple-keccak).

### The opening

The F_r arithmetic uses the same CRT Montgomery method as F_p (`groth/fp.py` with `FR`). `groth/frprog.py` writes it as straight-line code: the prover runs it on integers, and the program generator records it and lays it out level by level, each value bound once. An inverse is a hint: the prover supplies w and the program checks x w = 1.

The formulas are snarkjs's, simplified so they need fewer products and inverses:

- the products over the roots are y^8 - xi, y^4 - xi and (y^3 - xi)(y^3 - xi w), since h0^8 = h1^4 = xi;
- the roots are powers of xiSeed times constants, so every inverse of a power of xiSeed comes from one hint;
- each Lagrange basis at the roots becomes one inverse of y - root.

That leaves 22 inverse hints, plus one per public input.

### The MSM

A1 - C0 = q1 C1 + q2 C2 - t W1 + y W2 - e G1, with four points from the proof and one constant (`groth/msm.py`).

**Group law.** Points are affine. The prover supplies each operation's slope, and for an addition also d = 1 / (x_Q - x_T). The program checks

- λ (x_Q - x_T) = y_Q - y_T and d (x_Q - x_T) = 1 for an addition;
- λ y = 3/2 x² for a doubling.

The inverse makes x_Q ≠ x_T, so the slope is the chord's. A doubling needs none: y = 0 would make x = 0, and (0, 0) is not on the curve. So every point the program computes is on the curve and is the group-law result. ADD and DBL are functions of the program.

**Variable base.** GLV splits each scalar k = n1 + λ n2 (mod r) into two odd halves below 2^128 in absolute value. So each point gives two columns, P and φ(P) = (β x, y). An odd n with |n| < 2^128 is Σ d_j 2^j with every digit ±1, d_j = 2 c_j - 1 for the bits c of C = (n + 2^128 - 1) / 2. The prover supplies C, and the program checks n1 + λ n2 = k in F_r.

The eight columns form two groups of four. Each group has a table of the 8 sums Q1 ± Q2 ± Q3 ± Q4, built at run time with 14 additions. A step's digits select d1 (Q1 + d1 d2 Q2 + d1 d3 Q3 + d1 d4 Q4): the entry by the bits c1 xor ck, the sign by c1. So the loop is 128 steps, each a doubling and two additions, with no digit 0 to skip.

**The start.** The accumulator starts at a fixed point S, found by hashing a label, not at a table entry. With every digit ±1, a short scalar's first steps add back what they double (2Q - Q = Q), so the accumulator would repeat, and with it the hints. Two witness nodes of equal value break the maximal sharing that a program's encoding must have, and `deploy` would refuse the program. From S, the accumulator is 2^j S plus the partial sum, which does not repeat. The variable-base sum is then off by 2^127 S, which the fixed base takes back.

**Fixed base.** e G1 uses windows of 8 bits of the canonical v = -e (checked against e in F_r), each selecting a constant (d + 1) 2^(8j) G1 by a case tree. The start is -Σ 2^(8j) G1 - 2^127 S, so no entry is the point at infinity.

### The pairing check

The pairing check is `pairing.py`'s polynomial identity, unchanged. It was written for Groth16's e(-A, B) e(C, δ) e(α, β) = 1 with one variable G2 point, B. Here:

- B is the generator [1]₂, which the program checks;
- C is W2 and δ is [x]₂;
- e(-C0, [1]₂) is the constant in α, β's place, so the first G1 point is -(A1 - C0), which the program checks against the MSM.

A version for two fixed G2 points would save B's slope relations, about 15 M.

### Padding

The input's budget is 1,000 mWU per byte of its witness stack, plus 50,000. The verifier costs more than its program and witness weigh, so a spend adds zero blocks of 512 bytes to the witness. A block costs 0.05 to 0.12 M mWU to check, depending on its group, and earns 0.51 M.

How many blocks a spend needs depends on the pruned program's size, which is known only at spend time. So the program offers groups of 1, 2, 4, ... 256 blocks, each behind a case on a bit of a 16-bit witness word. A group not taken is pruned. `Fflonk.pad_for` finds the fewest blocks for the pruned program's size, counting the budget low, as for Groth16 (`Groth16.budget_ok`).

## Soundness

- Every hint is checked: inverses by a product, slopes and inverses by the group-law relations, the column words and v by their relation to the scalars in F_r.
- Every hint word is below 2^254 (two bits checked), so its products stay within the CRT bound.
- Each witness node is read once in the program's tree unfolding (`Fflonk.compile` checks it), so a spender who unshares a node cannot give its copies different values.
- The challenges are recomputed from the transcript. The evaluations, the public inputs and the challenge words must be canonical, which is stricter than snarkjs: snarkjs reduces an evaluation mod r.
- The pairing check's soundness is as `docs/design.md` explains, and the program checks its G2 slot and both G1 slots.
- A proof with a commitment at the point at infinity has no witness. snarkjs would accept one, but an honest prover produces one with negligible probability.
- The key is compiled in, so it is trusted as the deployer's: `fflonk_ref.load_vk` checks that its points are on the curves and X_2 in the order-r subgroup, nothing more.

## Tests

- `tests/test_keccak.py`: the permutation and Keccak-256 of 1 to 9 words, against hashlib and test vectors.
- `tests/test_msm.py`: the group law, the variable-base MSM with and without GLV, and the fixed base, with wrong hints rejected.
- `tests/test_fflonk.py`: both modes on the proofs in `examples/fflonk`. The honest witness passes at the predicted cost, also padded so the budget covers it. These are rejected: a tampered evaluation, challenge, public input, inverse, column word, scalar, MSM hint, G1 slot or G2 slot, and a valid proof for another sighash.
