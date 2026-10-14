# Benchmarks

All costs are Simplicity's static cost bound in milliweight units (mWU), as rust-simplicity 0.9 and Elements 23.3 compute it; 1,000 mWU is 1 WU. The generator predicts each cost exactly, and every test checks the prediction against `hand`.

## One spend

The toy circuit's verifier:

| | |
|---|---|
| program cost | 371,781,108 mWU |
| budget: (witness stack bytes + 50) x 1000 | 381,589,000 mWU |
| pruned program | 161,148 bytes |
| witness (proof, hints, Merkle sibling, 414 padding blocks) | 220,321 bytes |
| transaction | 382,202 WU (standard limit 400,000), 95,551 vB |
| fee at 0.115 sat/vB, which Liquid testnet accepted | about 11,000 sat |

## Where the cost goes

| part | mWU | share |
|---|---:|---:|
| Miller loop: 88 steps, residue witness folded in | 343,032,389 | 92.3% |
| witness padding: 414 blocks | 10,531,554 | 2.8% |
| MSM of the public input: 51 windows of 5 bits | 8,645,585 | 2.3% |
| final residue check and G2 membership check | 6,216,124 | 1.7% |
| setup: on-curve checks, normalisation, c c^-1 = 1 | 3,014,174 | 0.8% |
| transaction binding, range check, reading the witness | 341,282 | 0.1% |
| total | 371,781,108 | |

## Building blocks

The F_p rows exclude reading the operands and checking the result; the other rows include them (about 1.25 k mWU per output word).

| operation | mWU |
|---|---:|
| F_p product | 13,241 |
| F_p squaring | 10,966 |
| F_p product with a constant, or normalisation | 8,923 |
| F_p addition | 2,579 |
| F_p12 product | 1,635,135 |
| F_p12 squaring | 994,014 |
| F_p12 times a line | 714,790 |
| G2 doubling, hinted slope | 414,816 |
| G2 addition, hinted slope | 423,491 |
| MSM window (select and add) | ~ 169,500 |
| loop step: doubling (65 of them) | 3,644,556 |
| loop step: addition with c or c^-1 (21) | 4,327,665 |
| loop step: Frobenius addition (2) | 2,594,134 |
| G2 membership check of B | ~ 144,000 |
| padding block of 512 bytes | 25,500 |

## Time

| | |
|---|---|
| generate the program from a key (Python) | 2 s |
| generate the witness, including the residue witness (Python) | 3 s |
| `deploy compile`: parse the 1.6 MB program text, once per key | 6.5 min |
| `deploy spend`: prune, execute, build the transaction | 2 s |
| snarkjs setup / proof of the toy circuit | 2 min / 1 s |
| Elements node: script verification of the spend | 0.7 s |
| `tests/test_groth16.py` | 8 min |

Measured on an Apple Silicon laptop, except the test, which ran on a 2-core cloud VM.

## Reproducing

Each number comes from a test, which prints it:

```sh
python3 tests/test_fp.py bench   # F_p operations
python3 tests/test_tower.py      # F_p2, F_p6, F_p12 products, Frobenius maps
python3 tests/test_curve.py      # curve steps, on-curve checks, MSM
python3 tests/test_miller.py     # the plain Miller loop and its functions
python3 tests/test_pairing.py    # the loop with the residue witness, the final check
python3 tests/test_groth16.py    # the whole verifier, its parts, the padded version
python3 tests/test_binding.py    # the verifier with the transaction binding
python3 tests/test_g2_check.py   # the G2 membership check
```

`deploy spend` prints the cost, the sizes and the budget of a real transaction. The files in `examples/multiplier/` regenerate the program and the witness of the regtest spend `ecc9764f…` byte for byte:

```sh
E=examples/multiplier
python3 tools/groth16_snarkjs.py program $E/verification_key.json --values 1 --out build/check
python3 tools/groth16_snarkjs.py witness $E/verification_key.json $E/proof.json $E/public.json --leaves $E/leaves.json --out build/check
gunzip -c $E/verifier.simpl.gz | cmp - build/check.simpl && gunzip -c $E/verifier.w0.json.gz | cmp - build/check.w0.json
```
