# Examples

A verifier is generated from a verifying key, so there is no single Simplicity file to read: the key's points become the program's constants. This directory holds:

- a small generated program, one field multiplication;
- the verifier of the circom toy circuit, with the files of one regtest spend;
- the test proofs of the fflonk verifier;
- the test proofs of the Noir circuit.

## fp_mul.simpl

One multiplication in the BN254 field, the smallest piece of the verifier. It is 23 lines, written by `fp_mul.py`. The witness holds two field elements in Montgomery form, x·R mod p with R = p_s, the secp256k1 field prime. The program checks that both words are below 2^254, multiplies them with the secp256k1 jets, and compares the product with the expected value.

- `n1`, `n2`: the product modulo the secp256k1 field prime p_s and modulo the group order n_s. The product is below p_s·n_s, so the two residues fix it exactly.
- `n4`, `n6`, `n7`, `n9`: the Montgomery reduction. These are four jets with the constants `k3` (−p⁻¹ mod p_s), `k5` (p) and `k8` (p_s⁻¹ mod n_s). The result is a·b·R⁻¹ mod p, as a word below 2p.
- `n11` to `n15`: the result equals the expected word `k10`, or that word plus p (`k12`).
- `n16` to `n21`: each witness word is below 2^254: its top two bits are 0.

The reduction is exact only while the operands stay within the bound the generator assumed. That is why the words are checked: the verifiers check every word they multiply in the same way, or reduce it first. Words between p and 2^254 are harmless: they stand for their value mod p, and the reduction stays exact. Without the check, words near 2^256 could make the reduction wrap around modulo n_s, and a pair of them could give the expected word for the wrong product.

```sh
tools/harness/target/release/hand examples/fp_mul.simpl examples/fp_mul.w0.json    # cost 22,994 mWU
```

## multiplier/

The verifier of `circuits/multiplier.circom`, the toy statement a·b = c, bound to the spending transaction. The directory also has the files of one spend on an Elements regtest node, which proves c = 21.

| file | |
|---|---|
| `verification_key.json` | the snarkjs key |
| `verifier.simpl.gz` | the generated program, 2.8 MB of text (most of it the public input's tables) |
| `verifier.uprog` | its consensus encoding before pruning (`deploy compile`), CMR `bab3e5faa2f18478ca38eea1217dec723e58dab47589db3bd29b020aae222d55` |
| `verifier.wnames` | the names of its witness nodes, in the order the encoding reads their values (`deploy compile`) |
| `proof.json`, `public.json` | the snarkjs proof and its public signal |
| `leaves.json` | the two leaves behind the public signal: the transaction's sighash and c |
| `verifier.w0.json.gz` | the witness, by witness node (see below) |

The witness has three kinds of node:

- `w_in` holds the public signal, the proof, the compressed residue witness, the challenges r and z, and the Merkle sibling.
- `wl0` to `wl87` hold each step's slope, plus a compressed Miller value at 37 of the 88 steps.
- `wq` holds the quotient.

`make example` regenerates the program and the witness from the key, the proof, the public signal and the leaves, and compares them byte for byte. `make example-uprog` also runs `deploy compile` and compares the `.uprog` and `.wnames`. docs/benchmarks.md has the commands.

The output that spend took had no key path: its internal key is BIP341's unspendable point, `deploy`'s default.

## fflonk/

The fixtures of `tests/test_fflonk.py`. They hold the snarkjs 0.7.6 fflonk key of `circuits/multiplier_fflonk.circom`, and proofs of c = 21 for the harness's dummy sighash.

| file | |
|---|---|
| `verification_key.json` | the snarkjs key (universal setup: no ceremony of its own) |
| `public.json` | the public signals: the sighash as two limbs, then c |
| `proof_keccak.json` | a proof from snarkjs as it is (Keccak-256 transcript) |
| `proof_sha256.json` | a proof from `tools/snarkjs_sha256.mjs` (SHA-256 transcript) |
| `proof_keccak_other_sighash.json`, `public_other_sighash.json` | a valid proof for another sighash, which the bound program must reject |

## noir/

The fixtures of `tests/test_noir.py`. They hold the snarkjs Groth16 key of `circuits/noir/multiplier`, and proofs of c = 21. The key was set up from the R1CS that `tools/noir_r1cs.py` converted the circuit to.

| file | |
|---|---|
| `multiplier.r1cs` | the R1CS the key was made from (2 constraints) |
| `verification_key.json` | the snarkjs key (one demo contribution) |
| `proof.json`, `public.json` | a proof for the harness's dummy sighash. The public signals are that sighash with its top three bits cleared, and c |
| `proof_other_sighash.json`, `public_other_sighash.json` | a valid proof for another sighash, which the program must reject |
