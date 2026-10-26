# Benchmarks

All costs are Simplicity's static cost bound in milliweight units (mWU), as rust-simplicity 0.9 and Elements 23.3 compute it; 1,000 mWU is 1 WU. The generator predicts each cost exactly, and every test checks the prediction against `hand`.

## One spend

The toy circuit's verifier (one public signal bound to the transaction), in one spend on an Elements 23.3.1 regtest node, whose files are in `examples/multiplier/`:

| | |
|---|---|
| program cost | 48,646,805 mWU |
| budget: (witness stack bytes + 50) x 1000 | 52,699,000 mWU, no padding needed |
| pruned program | 34,147 bytes |
| witness (proof, 37 compressed Miller values, slopes, quotient, Merkle sibling) | 18,432 bytes |
| transaction | 53,308 WU, 13,327 vB |
| fee at 0.115 sat/vB | about 1,500 sat |

## Where the cost goes

| part | mWU | share |
|---|---:|---:|
| the loop: 88 steps, each a few relations at z | 38,188,706 | 78.5% |
| the public input's term: 31 table factors, at 7 of the additions | 5,664,636 | 11.6% |
| end: the last relations, Q(z) (160 coefficients), the two hashes | 2,676,830 | 5.5% |
| setup: on-curve checks, powers of z, a_c at z, the Frobenius images, τ, the transcript header | 2,061,315 | 4.2% |
| reading the witness, passing it between the parts | 29,822 | 0.1% |
| transaction binding, range check | 25,496 | 0.0% |
| total | 48,646,805 | |

Of the loop, 34.1 M is in the steps and 4.0 M in passing the state from one step to the next: the state carries 22 values computed in the setup (powers of z, the points at z, a_c(z) ± z, r and r^2) and the public input to every step, and a step function gets the 9 or 16 of them it reads. Each step reads its leaf from a witness node of its own, so the leaves are not carried.

## Where the bytes go

| | bytes |
|---|---:|
| line constants of δ: 4 words per step | 11,264 |
| program code | about 9,000 |
| the public input's tables: 31 selected entries of 4 words, τ, and the commitments of 254 pruned branches | 12,288 |
| other constants: the curve and field constants | about 1,600 |
| 37 committed Miller values, 6 words each | 7,104 |
| quotient Q, 160 coefficients | 5,120 |
| B's slopes, 88 steps | 5,632 |
| a_c, the proof, the challenges, the input, the sibling | 576 |

`tools/harness/target/release/sizes <program.simpl> <witness.json> [name,...]` splits a pruned program into constants, pruned-branch commitments and code and, given definition names, attributes its bytes to them.

## Building blocks

| operation | mWU |
|---|---:|
| F_p product (operands and result excluded) | 13,241 |
| F_p squaring | 10,966 |
| F_p product with a constant, or normalisation | 8,923 |
| F_p addition | 2,579 |
| 12-term dot product, one reduction | 116,744 |
| loop step: doubling (51 of them) | 315,253 |
| loop step: doubling with a committed Miller value (14) | 473,513 |
| loop step: addition, committed (23, the two Frobenius additions with g = 1) | 497,433 |
| Q(z): eight coefficients (20 calls) | 94,597 |
| a(t) for an element of F_p6 by Horner's rule (5 calls in the setup) | 80,097 |
| a factor of the public input's term: σ ± b2 at z (31 calls) | 130,429 |
| a factor with its selection and its share of the products | about 183,000 |

A doubling step evaluates B's slope and the two lines at z and -z, updates N and D, and adds its relations to the Horner sum; a committed one also evaluates the committed value (a 6-term dot product). Computed in the tower, the same step would cost 3,644,556.

## Time

| | |
|---|---|
| `groth16_snarkjs.py program`: the program from a key, with its tables (Python) | 5 s |
| `groth16_snarkjs.py witness`: check the proof, then the Miller values, residue witness and quotient (Python) | 8 s |
| `deploy compile`: parse the 2.8 MB program text, once per key | 3.1 min |
| `deploy compile` of the Noir verifier (5.4 MB, two inputs) and of the fflonk SHA-256 verifier | 10 min, 5.8 min |
| `deploy spend`: load the program, prune and execute it, build the transaction | 6 s |
| `tools/demo.py setup`: circom, the snarkjs setup and contribution, the program | 2.1 min |
| `fflonk_snarkjs.py witness`: one run in `hand` to size the padding | 5.6 min |
| `tests/test_groth16.py` | about 3 min |

Measured on a 2-core cloud VM.

## Reproducing

The tests print the costs and sizes (`make bench` for the F_p operations, `make -j4 test` for the rest). The weights come from `deploy spend` and `tools/regtest.sh`, and the times from running the commands.

```sh
python3 tests/test_fp.py bench   # F_p operations
python3 tests/test_poly.py       # F_p12 as polynomials, against the tower
python3 tests/test_curve.py      # on-curve checks, tables, the range check of an input
python3 tests/test_pairing.py    # the check alone: its parts, its steps, tampered witnesses
python3 tests/test_g2_check.py   # the G2 membership check
python3 tests/test_groth16.py    # the whole verifier (INPUTS=2 for two public inputs)
python3 tests/test_inputs.py     # keys with 3 to 5 public inputs (numeric model; only some window factors run)
python3 tests/test_binding.py    # the verifier with the transaction binding
python3 tests/test_noir.py       # the Noir circuit's verifier, and noir_r1cs.py's checks
python3 tests/test_keccak.py     # Keccak-f[1600] for the fflonk transcript
python3 tests/test_msm.py        # the fflonk MSM: group law, GLV, fixed base
python3 tests/test_fflonk.py     # the fflonk verifier, both transcripts, with its cost by part
python3 tests/test_invariants.py # what the generator refuses
python3 tests/test_tools.py      # what the command-line tools refuse
```

The fflonk and Noir costs are in [fflonk.md](fflonk.md) and [noir.md](noir.md). `deploy spend` prints the cost, the sizes and the budget of a real transaction, and `tools/harness/target/release/costs <program.simpl>` the cost of every named definition of a program. The files in `examples/multiplier/` regenerate the program and the witness of that spend byte for byte (`make example`):

```sh
E=examples/multiplier
python3 tools/groth16_snarkjs.py program $E/verification_key.json --values 1 --out build/check
python3 tools/groth16_snarkjs.py witness $E/verification_key.json $E/proof.json $E/public.json --leaves $E/leaves.json --out build/check
gunzip -c $E/verifier.simpl.gz | cmp - build/check.simpl && gunzip -c $E/verifier.w0.json.gz | cmp - build/check.w0.json
```

## Runs on a node

`tools/regtest.sh` on Elements 23.3.1 regtest, with each toy circuit. Each run spends one output with the proof, shows that the same proof is rejected in a transaction paying someone else (`Assertion failed inside jet`), and spends a second output of the same leaf through a key path.

| verifier | proof spend | key path |
|---|---|---|
| Groth16, circom | 53,315 WU, 13,329 vB | 721 WU |
| Groth16, Noir | 67,803 WU, 16,951 vB | 721 WU |
| fflonk, SHA-256 transcript | 126,589 WU, 31,648 vB | 721 WU |

The weights vary by a few WU between runs, with the signature and the transaction's other fields.
