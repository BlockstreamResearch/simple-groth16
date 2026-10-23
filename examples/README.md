# Examples

The verifier is generated from a verifying key, so there is no single Simplicity file to read: the key's points are the program's constants. This directory keeps two generated programs, a small one and the one spent on Liquid testnet, and the fflonk verifier's test proofs.

## fp_mul.simpl

One multiplication in the BN254 field, the smallest piece of the verifier (17 lines, written by `fp_mul.py`). The witness holds two field elements in Montgomery form; the program multiplies them with the secp256k1 jets and checks the result.

- `n1`, `n2`: the product modulo the secp256k1 field prime and modulo the group order. Together they are the exact 512-bit product.
- `n4` to `n9`: the Montgomery reduction, four jets and three constants. The result is a·b·R⁻¹ mod p as a word below 2p.
- `n11` to `n15`: the result equals the expected word, or that word plus p.

```sh
tools/harness/target/release/hand examples/fp_mul.simpl examples/fp_mul.w0.json    # cost 19,156 mWU
```

## multiplier/

The verifier of `circuits/multiplier.circom` (a·b = c, bound to the spending transaction) and the files of one spend on an Elements regtest node, transaction `407cf881…`, which proves c = 21.

| file | |
|---|---|
| `verification_key.json` | the snarkjs key |
| `verifier.simpl.gz` | the generated program, 2.8 MB of text (most of it the public input's tables) |
| `verifier.uprog` | its consensus encoding before pruning (`deploy compile`), CMR `bab3e5faa2f18478ca38eea1217dec723e58dab47589db3bd29b020aae222d55` |
| `verifier.wnames` | the names of its witness nodes in the order the encoding reads their values (`deploy compile`) |
| `proof.json`, `public.json` | the snarkjs proof and its public signal |
| `leaves.json` | the two leaves behind the public signal: the transaction's sighash and c |
| `verifier.w0.json.gz` | the witness, by witness node: proof and Merkle sibling (`w_in`), each step's slope and compressed Miller value (`wl0` to `wl87`), the quotient (`wq`) |

`tools/groth16_snarkjs.py` regenerates the program and the witness from the key, the proof and the leaves byte for byte; docs/benchmarks.md has the commands. The output had no key path: its internal key is BIP341's unspendable point.

The verifier spent on Liquid testnet ([`f25a6e90…`](https://blockstream.info/liquidtestnet/tx/f25a6e90417c427f25c1d6883869825f30ec111a357b0e550bf24a20725d3cdb)) was an earlier version of this program: the Miller loop computed in the tower, without the G2 membership check.

## fflonk/

The fixtures of `tests/test_fflonk.py`: the snarkjs 0.7.6 fflonk key of `circuits/multiplier_fflonk.circom` and proofs of c = 21 for the harness's dummy sighash.

| file | |
|---|---|
| `verification_key.json` | the snarkjs key (universal setup: no ceremony of its own) |
| `public.json` | the public signals: the sighash as two limbs, then c |
| `proof_keccak.json` | a proof from snarkjs as it is (Keccak-256 transcript) |
| `proof_sha256.json` | a proof from `tools/snarkjs_sha256.mjs` (SHA-256 transcript) |
| `proof_keccak_other_sighash.json`, `public_other_sighash.json` | a valid proof for another sighash, which the bound program must reject |
