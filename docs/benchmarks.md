# Benchmarks

All costs are Simplicity's static cost bound in milliweight units (mWU), as rust-simplicity 0.9 and Elements 23.3 compute it; 1,000 mWU is 1 WU. The generator predicts each cost exactly, and every test checks the prediction against `hand`.

## One spend

The toy circuit's verifier (one public signal bound to the transaction), spent on an Elements 23.3.1 regtest node in `69a21870…`:

| | |
|---|---|
| program cost | 66,733,221 mWU |
| budget: (witness stack bytes + 50) x 1000 | 88,359,000 mWU, no padding needed |
| pruned program | 59,982 bytes |
| witness (proof, 35 Miller values, slopes, quotient, Merkle sibling) | 28,257 bytes |
| transaction | 88,994 WU, 22,249 vB |
| fee at 0.115 sat/vB, which Liquid testnet accepts | about 2,600 sat |

## Where the cost goes

| part | mWU | share |
|---|---:|---:|
| the loop: 88 steps, each a few relations at z | 50,261,517 | 75.3% |
| MSM of the public input: 51 windows of 5 bits | 8,645,585 | 13.0% |
| end: the last relations, Q(z) (200 coefficients), the two hashes | 3,305,204 | 5.0% |
| setup: on-curve checks, powers of z, c(z), the Frobenius images, the transcript header | 3,166,661 | 4.7% |
| reading the witness, passing it between the parts | 1,327,958 | 2.0% |
| transaction binding, range check | 26,296 | 0.0% |
| total | 66,733,221 | |

Of the loop, 42.3 M is in the steps and 8.0 M in folding the loop state over the witness: the state carries 33 per-run values (the powers of z, the points at z, r) to every step.

## Where the bytes go

| | bytes |
|---|---:|
| line constants of γ and δ: 4 words per pair and step | 22,528 |
| program code | about 26,000 |
| MSM: selected table entries and pruned branches | about 11,400 |
| 35 committed Miller values | 13,440 |
| quotient Q, 200 coefficients | 6,400 |
| B's slopes, 88 steps | 5,632 |
| MSM slopes, c, c^-1, the proof, the challenges | about 2,800 |

## Building blocks

| operation | mWU |
|---|---:|
| F_p product (operands and result excluded) | 13,241 |
| F_p squaring | 10,966 |
| F_p product with a constant, or normalisation | 8,923 |
| F_p addition | 2,579 |
| 12-term dot product, one reduction | 116,744 |
| loop step: doubling (51 of them) | 385,831 |
| loop step: doubling with a committed Miller value (14) | 608,873 |
| loop step: addition with c or c^-1, committed (21) | 633,646 |
| loop step: Frobenius addition (2) | 394,395 |
| Q(z): eight coefficients (25 calls) | 94,597 |
| MSM window (select and add) | about 169,500 |

A doubling step evaluates B's slope and the three lines at z and adds its relations to the Horner sum; a committed one also evaluates the committed Miller value (a 12-term dot product). Computed in the tower, the same step cost 3,644,556.

## Before and after

| | tower Miller loop (main) | one polynomial identity |
|---|---:|---:|
| program cost | 371.8 M mWU (with 414 padding blocks) | 66.7 M mWU |
| pruned program | 161 kB | 60 kB |
| witness | 220 kB (212 kB of it padding) | 28 kB |
| transaction | 382.2 kWU, 95.6 kvB | 89.0 kWU, 22.2 kvB |

## Time

| | |
|---|---|
| generate the program from a key (Python) | 2 s |
| generate the witness: Miller values, residue witness, quotient (Python) | 2 s |
| `deploy compile`: parse the 1.1 MB program text, once per key | 2.5 min |
| `deploy spend`: prune, execute, build the transaction | 1 s |
| snarkjs setup / proof of the toy circuit | 1.3 min / 1 s |
| `tests/test_groth16.py` | 3 min |

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

`deploy spend` prints the cost, the sizes and the budget of a real transaction, and `tools/harness/target/release/costs <program.simpl>` the cost of every named definition of a program. The files in `examples/multiplier/` regenerate the program and the witness of the regtest spend `69a21870…` byte for byte:

```sh
E=examples/multiplier
python3 tools/groth16_snarkjs.py program $E/verification_key.json --values 1 --out build/check
python3 tools/groth16_snarkjs.py witness $E/verification_key.json $E/proof.json $E/public.json --leaves $E/leaves.json --out build/check
gunzip -c $E/verifier.simpl.gz | cmp - build/check.simpl && gunzip -c $E/verifier.w0.json.gz | cmp - build/check.w0.json
```

## On-chain runs

| network | transaction | what |
|---|---|---|
| Elements 23.3.1 regtest | `f47584cd…` | the walkthrough (`tools/regtest.sh`): proof spend, 88,968 WU, vsize 22,242 |
| Elements 23.3.1 regtest | `69a21870…` | proof spend, the files in `examples/multiplier/` |
| Elements 23.3.1 regtest | a redirected proof | rejected with `Assertion failed inside jet` |
| Elements 23.3.1 regtest | `2373f0d3…` | the key path of the same leaf, 721 WU |
| Liquid testnet | [`f25a6e90…`](https://blockstream.info/liquidtestnet/tx/f25a6e90417c427f25c1d6883869825f30ec111a357b0e550bf24a20725d3cdb), block 2,659,534 | an earlier verifier (tower Miller loop, without the G2 check): 381,492 WU, fee 11,000 sat |
