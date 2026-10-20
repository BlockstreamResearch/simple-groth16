# Examples

The verifier is generated from a verifying key, so there is no single Simplicity file to read: the key's points are the program's constants. This directory keeps two generated programs, a small one and the one spent on Liquid testnet.

## fp_mul.simpl

One multiplication in the BN254 field, the smallest piece of the verifier (17 lines, written by `fp_mul.py`). The witness holds two field elements in Montgomery form; the program multiplies them with the secp256k1 jets and checks the result.

- `n1`, `n2`: the product modulo the secp256k1 field prime and modulo the group order. Together they are the exact 512-bit product.
- `n4` to `n9`: the Montgomery reduction, four jets and three constants. The result is a·b·R⁻¹ mod p as a word below 2p.
- `n11` to `n15`: the result equals the expected word, or that word plus p.

```sh
tools/harness/target/release/hand examples/fp_mul.simpl examples/fp_mul.w0.json    # cost 19,156 mWU
```

## multiplier/

The verifier of `circuits/multiplier.circom` (a·b = c, bound to the spending transaction) and the files of one spend on an Elements regtest node, transaction `cf7b0663…`, which proves c = 21.

| file | |
|---|---|
| `verification_key.json` | the snarkjs key |
| `verifier.simpl.gz` | the generated program, 2.0 MB of text (most of it the MSM tables) |
| `verifier.uprog` | its consensus encoding before pruning (`deploy compile`), CMR `02b0fb82…d2c5e1c7` |
| `proof.json`, `public.json` | the snarkjs proof and its public signal |
| `leaves.json` | the two leaves behind the public signal: the transaction's sighash and c |
| `verifier.w0.json.gz` | the witness: proof, Miller values, slopes, quotient, Merkle sibling |

`tools/groth16_snarkjs.py` regenerates the program and the witness from the key, the proof and the leaves byte for byte; docs/benchmarks.md has the commands. The output had no key path: its internal key is BIP341's unspendable point.

The verifier spent on Liquid testnet ([`f25a6e90…`](https://blockstream.info/liquidtestnet/tx/f25a6e90417c427f25c1d6883869825f30ec111a357b0e550bf24a20725d3cdb)) was an earlier version of this program: the Miller loop computed in the tower, without the G2 membership check.
