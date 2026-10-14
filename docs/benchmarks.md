# Benchmarks

All costs are Simplicity's static cost bound in milliweight units (mWU), as rust-simplicity 0.9 and Elements 23.3 compute it; 1,000 mWU is 1 WU. The generator predicts each cost exactly, and every test checks the prediction against `hand`.

## One spend

The toy circuit's verifier (one public signal bound to the transaction), spent on an Elements 23.3.1 regtest node in `9f4c1cb0…`:

| | |
|---|---|
| program cost | 81,743,632 mWU |
| budget: (witness stack bytes + 50) x 1000 | 106,812,000 mWU, no padding needed |
| pruned program | 61,411 bytes |
| witness (proof, Miller values, slopes, quotient, Merkle sibling) | 45,281 bytes |
| transaction | 107,423 WU, 26,856 vB |
| fee at 0.115 sat/vB, which Liquid testnet accepts | about 3,100 sat |

## Where the cost goes

| part | mWU | share |
|---|---:|---:|
| the loop: 88 steps, each a few relations at z | 66,612,776 | 81.5% |
| MSM of the public input: 51 windows of 5 bits | 8,645,785 | 10.6% |
| setup: on-curve checks, powers of z, c(z), the Frobenius images, the transcript header | 3,166,661 | 3.9% |
| reading the witness, passing it between the parts | 2,144,910 | 2.6% |
| end: the last relations, Q(z), the two hashes | 1,147,204 | 1.4% |
| transaction binding, range check | 26,296 | 0.0% |
| total | 81,743,632 | |

Of the loop, 55.6 M is in the steps and 11.0 M in folding the loop state over the witness: the state carries 33 per-run values (the powers of z, the points at z, r) to every step.

## Building blocks

| operation | mWU |
|---|---:|
| F_p product (operands and result excluded) | 13,241 |
| F_p squaring | 10,966 |
| F_p product with a constant, or normalisation | 8,923 |
| F_p addition | 2,579 |
| 12-term dot product, one reduction | 116,744 |
| loop step: doubling (65 of them) | 609,273 |
| loop step: addition with c or c^-1 (21) | 698,901 |
| loop step: Frobenius addition (2) | 683,092 |
| MSM window (select and add) | about 169,500 |

A doubling step evaluates the committed Miller value at z (a 12-term dot product), B's slope, the three lines, and adds its two relations to the Horner sum. Computed in the tower, the same step cost 3,644,556.

## Before and after

| | tower Miller loop | one polynomial identity |
|---|---:|---:|
| program cost | 371.8 M mWU (with 414 padding blocks) | 81.7 M mWU |
| pruned program | 161 kB | 61 kB |
| witness | 220 kB (212 kB of it padding) | 45 kB |
| transaction | 382.2 kWU, 95.6 kvB | 107.4 kWU, 26.9 kvB |
| room under the 400 kWU limit | one more public input | about 20 more |

## Time

| | |
|---|---|
| generate the program from a key (Python) | 2 s |
| generate the witness: Miller values, residue witness, quotient (Python) | 2 s |
| `deploy compile`: parse the 1.1 MB program text, once per key | 2.6 min |
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

`deploy spend` prints the cost, the sizes and the budget of a real transaction, and `tools/harness/target/release/costs <program.simpl>` the cost of every named definition of a program. The files in `examples/multiplier/` regenerate the program and the witness of the regtest spend `9f4c1cb0…` byte for byte:

```sh
E=examples/multiplier
python3 tools/groth16_snarkjs.py program $E/verification_key.json --values 1 --out build/check
python3 tools/groth16_snarkjs.py witness $E/verification_key.json $E/proof.json $E/public.json --leaves $E/leaves.json --out build/check
gunzip -c $E/verifier.simpl.gz | cmp - build/check.simpl && gunzip -c $E/verifier.w0.json.gz | cmp - build/check.w0.json
```

## On-chain runs

| network | transaction | what |
|---|---|---|
| Elements 23.3.1 regtest | `0da39ffd…` | the walkthrough (`tools/regtest.sh`): proof spend, 107,421 WU, vsize 26,856 |
| Elements 23.3.1 regtest | `901f2f6a…` | the same kind of proof redirected to another address: rejected with `Assertion failed inside jet` |
| Elements 23.3.1 regtest | `9f4c1cb0…` | proof spend, the files in `examples/multiplier/` |
| Elements 23.3.1 regtest | `d8d87a6a…` | the key path of the same leaf, 721 WU |
| Liquid testnet | [`f25a6e90…`](https://blockstream.info/liquidtestnet/tx/f25a6e90417c427f25c1d6883869825f30ec111a357b0e550bf24a20725d3cdb), block 2,659,534 | an earlier verifier (tower Miller loop, without the G2 check): 381,492 WU, fee 11,000 sat |
