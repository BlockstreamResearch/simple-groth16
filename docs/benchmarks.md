# Benchmarks

All costs are Simplicity's static cost bound in milliweight units (mWU), as rust-simplicity 0.9 and Elements 23.3 compute it; 1,000 mWU is 1 WU. The generator predicts each cost exactly, and every test checks the prediction against `hand`.

## One spend

The toy circuit's verifier (one public signal bound to the transaction), spent on an Elements 23.3.1 regtest node in `116f7d63…`:

| | |
|---|---|
| program cost | 61,468,974 mWU |
| budget: (witness stack bytes + 50) x 1000 | 66,170,000 mWU, no padding needed |
| pruned program | 45,058 bytes |
| witness (proof, 37 compressed Miller values, slopes, quotient, Merkle sibling) | 20,992 bytes |
| transaction | 66,779 WU, 16,695 vB |
| fee at 0.115 sat/vB, which Liquid testnet accepts | about 1,900 sat |

## Where the cost goes

| part | mWU | share |
|---|---:|---:|
| the loop: 88 steps, each a few relations at z | 49,589,014 | 80.7% |
| MSM of the public input: 32 windows of 8 bits | 5,342,640 | 8.7% |
| end: the last relations, Q(z) (208 coefficients), the two hashes | 3,417,151 | 5.6% |
| setup: on-curve checks, powers of z, a_c at z, the Frobenius images, the transcript header | 2,097,287 | 3.4% |
| reading the witness, passing it between the parts | 996,586 | 1.6% |
| transaction binding, range check | 26,296 | 0.0% |
| total | 61,468,974 | |

Of the loop, 43.1 M is in the steps and 6.5 M in folding the loop state over the witness: the state carries 25 values computed in the setup (powers of z, the points at z, a_c(z) ± z, r and r^2) to every step, and a step function gets the 12 or 19 of them it reads.

## Where the bytes go

| | bytes |
|---|---:|
| line constants of γ and δ: 4 words per pair and step | 22,528 |
| program code | about 10,500 |
| MSM: 32 selected table entries, and the commitments of 8 pruned branches each | 10,240 |
| other constants: τ, the curve and field constants | about 1,800 |
| 37 committed Miller values, 6 words each | 7,104 |
| quotient Q, 208 coefficients | 6,656 |
| B's slopes, 88 steps | 5,632 |
| MSM slopes, a_c, the proof, the challenges | about 1,600 |

`tools/harness/target/release/sizes <program.simpl> <witness.json>` splits a pruned program into constants, pruned-branch commitments and code, and attributes it to named definitions.

## Building blocks

| operation | mWU |
|---|---:|
| F_p product (operands and result excluded) | 13,241 |
| F_p squaring | 10,966 |
| F_p product with a constant, or normalisation | 8,923 |
| F_p addition | 2,579 |
| 12-term dot product, one reduction | 116,744 |
| loop step: doubling (51 of them) | 412,351 |
| loop step: doubling with a committed Miller value (14) | 582,269 |
| loop step: addition, committed (23, the two Frobenius additions with g = 1) | 606,389 |
| Q(z): eight coefficients (26 calls) | 94,597 |
| a(t) for an element of F_p6 by Horner's rule (5 calls in the setup) | 80,097 |
| MSM window (select and add) | about 167,000 |

A doubling step evaluates B's slope and the three lines at z and -z, updates N and D, and adds its relations to the Horner sum; a committed one also evaluates the committed value (a 6-term dot product). Computed in the tower, the same step cost 3,644,556.

## Before and after

| | tower Miller loop (main) | one polynomial identity |
|---|---:|---:|
| program cost | 371.8 M mWU (with 414 padding blocks) | 61.5 M mWU |
| pruned program | 161 kB | 45 kB |
| witness | 220 kB (212 kB of it padding) | 21 kB |
| transaction | 382.2 kWU, 95.6 kvB | 66.8 kWU, 16.7 kvB |

## Time

| | |
|---|---|
| generate the program from a key (Python) | 2 s |
| generate the witness: Miller values, residue witness, quotient (Python) | 2 s |
| `deploy compile`: parse the 2.0 MB program text, once per key | 2 min |
| `deploy spend`: prune, execute, build the transaction | 1 s |
| snarkjs setup / proof of the toy circuit | 1.3 min / 1 s |
| `tests/test_groth16.py` | 2.2 min |

Measured on a 2-core cloud VM.

## Reproducing

Each number comes from a test, which prints it:

```sh
python3 tests/test_fp.py bench   # F_p operations
python3 tests/test_poly.py       # F_p12 as polynomials, against the tower
python3 tests/test_curve.py      # on-curve checks, MSM
python3 tests/test_pairing.py    # the check alone: its parts, its steps, tampered witnesses
python3 tests/test_g2_check.py   # the G2 membership check
python3 tests/test_groth16.py    # the whole verifier
python3 tests/test_binding.py    # the verifier with the transaction binding
```

`deploy spend` prints the cost, the sizes and the budget of a real transaction, and `tools/harness/target/release/costs <program.simpl>` the cost of every named definition of a program. The files in `examples/multiplier/` regenerate the program and the witness of the regtest spend `116f7d63…` byte for byte:

```sh
E=examples/multiplier
python3 tools/groth16_snarkjs.py program $E/verification_key.json --values 1 --out build/check
python3 tools/groth16_snarkjs.py witness $E/verification_key.json $E/proof.json $E/public.json --leaves $E/leaves.json --out build/check
gunzip -c $E/verifier.simpl.gz | cmp - build/check.simpl && gunzip -c $E/verifier.w0.json.gz | cmp - build/check.w0.json
```

## On-chain runs

| network | transaction | what |
|---|---|---|
| Elements 23.3.1 regtest | `9e3770ac…` | the walkthrough (`tools/regtest.sh`): proof spend, 66,775 WU, vsize 16,694 |
| Elements 23.3.1 regtest | `116f7d63…` | proof spend, the files in `examples/multiplier/` |
| Elements 23.3.1 regtest | a redirected proof | rejected with `Assertion failed inside jet` |
| Elements 23.3.1 regtest | `cd7a7455…` | the key path of the same leaf, 721 WU |
| Liquid testnet | [`f25a6e90…`](https://blockstream.info/liquidtestnet/tx/f25a6e90417c427f25c1d6883869825f30ec111a357b0e550bf24a20725d3cdb), block 2,659,534 | an earlier verifier (tower Miller loop, without the G2 check): 381,492 WU, fee 11,000 sat |
