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

Every public input costs about 6.6 M mWU and 14 kB of program. The toy circuit has two (the sighash and c), where the circom one has one (the root).

## What the tools check

noir-cli is experimental, and it lowers some ACIR opcodes in ways a verifier must not accept:

- **Unconstrained hints.** Black-box functions it does not implement, Keccak-f[1600] among them, become witness values with no constraint tying them to their inputs. A circuit that asserts `keccakf1600(x)[0] == h` would accept any `x`.
- **Folded witness values.** For some black boxes (Blake2s, Blake3, ECDSA, MSM), given a witness, it writes the witness's values into the R1CS as constants. The R1CS would then depend on the witness.

So `noir_r1cs.py compile` reads `nargo compile --print-acir` and allows only these opcodes:

- assertions (`ASSERT`);
- Brillig calls, Noir's unconstrained code. The circuit must constrain their outputs, as with any Noir backend, and nargo's own check for unconstrained outputs runs.
- the black boxes `RANGE`, `AND` and `XOR`, which noir-cli lowers by bit decomposition.

It refuses any other black box, memory operations, calls and any line it does not recognize. `--trust` allows more kinds, after you have read how noir-cli lowers them.

`noir_r1cs.py witness` converts the compiled circuit again for each proof's inputs. It refuses the result unless the R1CS is the one the key was made from, byte for byte.

The versions are pinned:

- **nargo:** 1.0.0-beta.19, the version noir-cli reads. The tool checks it.
- **noir-cli:** Noir-Groth16 at commit 4b7caac. Install it with `cargo install --locked --git https://github.com/jamesbachini/Noir-Groth16 --rev 4b7caac noir-cli`. The tool cannot check the commit.

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
python3 tools/circom_demo.py setup --frontend noir --out build/noir
tools/harness/target/release/deploy compile build/noir/verifier.simpl build/noir/verifier
tools/regtest.sh build/noir
```

`setup` compiles and converts the circuit, runs the Groth16 setup with one contribution, and writes the program. `prove` (which `regtest.sh` calls) makes the witness, the proof and the program's witness. `make noir-demo` runs both without a node.

For your own circuit, put the sighash first among its public inputs, then:

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

The fflonk verifier binds by two public inputs instead: the sighash as two 128-bit limbs (`fflonk_snarkjs.py --bind`). A Noir circuit whose first two public inputs are those limbs works with it, through the same `noir_r1cs.py` and snarkjs's `fflonk setup`. The demo's circuit is for Groth16, which is cheaper.

## Tests

`tests/test_noir.py`:

- **The opcode check, on canned `--print-acir` output.** Assertions, Brillig calls and RANGE pass. Keccak-f, memory and calls are refused, and so is a line the check does not know.
- **The verifier, on the proofs in `examples/noir`.** The proof for the harness's sighash passes at the predicted cost, within its budget. A valid proof for another sighash is rejected, and so is a wrong c.

`tests/test_tools.py` checks the `--sighash-input` flags.
