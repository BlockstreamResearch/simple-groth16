# Noir circuits

A [Noir](https://noir-lang.org) circuit can spend a Liquid output through the Groth16 verifier, as a circom circuit does. Noir's own prover (Barretenberg's UltraHonk) is out of reach: its proofs are padded to 14.6 kB, and hashing them with Keccak alone would take about 570 M mWU, more than a standard transaction can pay for. So the circuit goes through R1CS instead:

1. `nargo compile` compiles the circuit to ACIR.
2. `noir-cli` converts the ACIR to iden3 R1CS and witness files. It is the CLI of [Noir-Groth16](https://github.com/jamesbachini/Noir-Groth16).
3. snarkjs makes the key and the proofs, as for circom.
4. `tools/groth16_snarkjs.py` makes the program and the witness, as for circom.

`tools/noir_r1cs.py` runs steps 1 and 2, and checks what they produce (below).

## Binding the transaction

The circom convention binds the transaction with a SHA-256 Merkle root of the public values, computed in the circuit. A Noir circuit converted to R1CS should not hash: noir-cli lowers some hashes soundly and others not (below). So the circuit takes the sighash itself as its first public input, with the top three bits cleared so that it is below r, as the root's are:

```noir
fn main(sighash: pub Field, c: pub Field, a: Field, b: Field) {
    let _ = sighash;
    assert(a * b == c);
}
```

`groth16_snarkjs.py --sighash-input` makes the program compare that input with its `sig_all_hash` jet, masked the same way. A proof is then valid for one transaction only. The witness command needs the sighash itself (`--sighash`), since the signal lacks its top three bits.

The circuit needs no constraint on the sighash. snarkjs's setup adds one row per public input, so each input's point in the key is independent, and changing an input invalidates the proof. The tests check this with a valid proof for another sighash, which the program rejects.

The toy circuit has two public inputs (the sighash and c), where the circom one has one (the root). The second costs 6.6 M mWU and 14 kB of program.

## What the tools check

noir-cli is experimental, and it lowers some ACIR opcodes in ways a verifier must not accept:

- **Unconstrained hints.** Black-box functions it does not implement, Keccak-f[1600] among them, become witness values with no constraint tying them to their inputs. A circuit that asserts `keccakf1600(x)[0] == h` would accept any `x`.
- **Folded witness values.** For some black boxes (Blake2s, Blake3, ECDSA, MSM), given a witness, it writes the witness's values into the R1CS as constants. The R1CS would then depend on the witness.

So `noir_r1cs.py compile` reads `nargo compile --print-acir` and allows only these opcodes:

- assertions (`ASSERT`);
- Brillig calls, Noir's unconstrained code. The circuit must constrain their outputs, as with any Noir backend. nargo checks for outputs left unconstrained, but on its own only prints what it finds. So the tool makes its warnings fatal: it passes `--deny-warnings`, and refuses any bug, error or warning line on stderr whatever nargo's exit status. With `--deny-warnings`, nargo also requires a `// Safety:` comment above each `unsafe` block. The check is a heuristic: it misses some under-constrained hints and flags some constrained ones (a hint checked under an `if`, say). `--allow-nargo-warnings` prints the warnings instead, for a circuit you have reviewed.
- the black boxes `RANGE`, `AND` and `XOR`, which noir-cli lowers by bit decomposition.

It refuses any other black box, memory operations, calls and any line it does not recognize. `--trust` allows more kinds, after you have read how noir-cli lowers them.

nargo compiles into a fresh directory, and the tool converts the artifact that run wrote, the one whose ACIR it checked. It never reads the circuit's own `target/`.

noir-cli makes the circuit's first ACIR witnesses the public signals, whatever their visibility, and nargo numbers the parameters in the order they are declared, return values last. So the tool also refuses a circuit unless its public parameters come before any private one and it returns nothing. Otherwise a private parameter would become a public signal, published in the spend, and a declared public input would be missing from the statement.

`noir_r1cs.py witness` converts the compiled circuit again for each proof's inputs. It refuses the result unless its R1CS is byte for byte the `x.r1cs` that `compile` wrote, the file the key is made from.

The versions are pinned:

- **nargo:** 1.0.0-beta.19, the version noir-cli reads. The tool checks it.
- **noir-cli:** Noir-Groth16 at commit 4b7caace1f21. Install it with `cargo install --locked --git https://github.com/jamesbachini/Noir-Groth16 --rev 4b7caace1f2128e454c8d0fe50cac1ec46b1e272 noir-cli`. Give the full hash: cargo resolves a shorter rev as a name, which a tag of that name would capture. The tool cannot check the commit.

## Cost

The toy circuit `circuits/noir/multiplier`: 2 public inputs, 2 R1CS constraints.

| | Noir, Groth16 | circom, Groth16 (for reference) |
|---|---:|---:|
| public inputs | 2 (sighash, c) | 1 (the root) |
| program cost | 55.3 M mWU | 48.6 M mWU |
| pruned program / witness | 47.9 / 19.2 kB | 34 / 18 kB |
| transaction | 67.8 kWU, 17.0 kvB | 53.3 kWU, 13.3 kvB |

The program's bytes earn more budget than it costs, so it needs no padding.

## Using it

The toy circuit:

```sh
python3 tools/demo.py setup --frontend noir --out build/noir
tools/harness/target/release/deploy compile build/noir/verifier.simpl build/noir/verifier
tools/regtest.sh build/noir
```

`setup` compiles and converts the circuit, runs the Groth16 setup with one contribution, and writes the program. `deploy compile` parses the program's 5.4 MB of text in about 10 minutes. `prove` (which `regtest.sh` calls) makes the circuit's witness, the proof and the program's witness. `make noir-demo` runs setup and prove without a node. On Liquid testnet or Liquid, `tools/liquid.py` spends the verifier (README).

For your own circuit, declare its public parameters before any private one, the sighash first, and return nothing. Then:

```sh
python3 tools/noir_r1cs.py compile path/to/circuit inputs.json --out build/x     # build/x.r1cs
# snarkjs groth16 setup build/x.r1cs <ptau> ..., zkey contribute, zkey export verificationkey
python3 tools/groth16_snarkjs.py program verification_key.json --sighash-input --out build/x
python3 tools/noir_r1cs.py witness inputs.json --out build/x                      # build/x.wtns
# snarkjs groth16 prove ... build/x.wtns proof.json public.json
python3 tools/groth16_snarkjs.py witness verification_key.json proof.json public.json --sighash-input --sighash <hex> --out build/x
```

`inputs.json` gives the circuit's parameters by name, as its ABI shapes them.

## fflonk

The fflonk verifier binds by two public inputs instead: the sighash as two 128-bit limbs (`fflonk_snarkjs.py --bind`). A Noir circuit whose first two public parameters are those limbs should work with it, through the same `noir_r1cs.py` and snarkjs's `fflonk setup`, but this pairing is not tested. The demo's circuit is for Groth16, which is cheaper.

## Tests

`tests/test_noir.py`:

- **The opcode check, on canned `--print-acir` output.** Assertions, Brillig calls and RANGE pass. Keccak-f, memory and calls are refused, and so is a line the check does not know.
- **The layout check.** Public parameters declared first pass. A private parameter before a public one, and a return value, are refused.
- **nargo's run, stubbed.** The artifact converted is the one the run wrote, not a decoy under the circuit's `target/` named in its `Nargo.toml`. A diagnostic on stderr is refused even when nargo exits 0.
- **The verifier, on the proofs in `examples/noir`.** The proof for the harness's sighash passes at the predicted cost, within its budget. A valid proof for another sighash is rejected, and so is a wrong c.

`tests/test_tools.py` checks the `--sighash-input` flags.
