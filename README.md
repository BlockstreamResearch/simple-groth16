# Simple Groth16

SNARK verifiers written in [Simplicity](https://github.com/BlockstreamResearch/simplicity). With them, a proof can spend a Liquid transaction output. The proof is made with [snarkjs](https://github.com/iden3/snarkjs) for a [circom](https://docs.circom.io) or [Noir](https://noir-lang.org) circuit.

A Python generator compiles a snarkjs verification key into a Simplicity program, and that program is the output's only spending condition. Two verifiers share the generator:

- **Groth16**, the cheaper one, whose setup is per circuit;
- **fflonk**, whose setup is universal.

> ⚠️ This is experimental research code. It has not been independently audited. Don't use it with funds you cannot lose. To report a vulnerability, see [SECURITY.md](SECURITY.md).

## What it supports

| | Groth16 ([docs](docs/groth16.md)) | fflonk ([docs](docs/fflonk.md)) |
|---|---|---|
| setup | per circuit: snarkjs's phase 2 on a powers of tau | universal: the powers of tau alone |
| circom circuits | bound by a Merkle root of the public values | bound by the sighash as two public inputs |
| Noir circuits ([docs](docs/noir.md)) | bound by the sighash as the first public input | should work, with the sighash as two inputs (untested) |
| proofs | snarkjs `groth16` | snarkjs `fflonk` (Keccak-256 transcript), or `tools/snarkjs_sha256.mjs` (SHA-256 transcript) |
| cost, toy circuit | 48.6 M mWU (circom), 55.3 M mWU (Noir) | 123.2 M mWU (SHA-256), 172.0 M mWU (Keccak), before padding |
| spending transaction | 53.3 kWU (circom), 67.8 kWU (Noir) | 126.6 kWU (SHA-256), 185.3 kWU (Keccak) |
| spent on | Elements regtest and Liquid testnet | Elements regtest and Liquid testnet |

Every transaction fits under the 400 kWU standard limit. A spend's budget is 1,000 mWU per byte of the input's witness stack (the program and its witness), plus 50,000, and the Groth16 programs earn more budget than they cost. The fflonk program costs more, so its spends pad the witness to pay for it.

Each binding ties the proof to the transaction that spends the output: the program reads that transaction's signature hash (`sig_all_hash`) and compares it with the proof's public inputs. A broadcast proof therefore cannot be replayed or redirected.

## How it works

Simplicity has jets for SHA-256 and for arithmetic modulo the secp256k1 primes, but none for BN254 or pairings. The generator builds both verifiers from these few ideas:

- **BN254 arithmetic on secp256k1 jets.** A product is computed exactly modulo both secp256k1 primes, then reduced with [Montgomery reduction](https://en.wikipedia.org/wiki/Montgomery_modular_multiplication) in CRT form. The generator tracks a static bound on every value, and refuses to emit a program in which a value could wrap around.
- **Hints instead of inversions.** The prover puts every slope and inverse in the witness. The program checks each one with a multiplication, such as `λ (x2 - x1) = y2 - y1` for an addition.
- **The pairing as one polynomial identity.** The prover writes the Miller loop's intermediate values into the witness. The program checks all 88 steps at once, at one random point chosen by hashing the witness (Fiat–Shamir with SHA-256). A [residue witness](https://eprint.iacr.org/2024/640) replaces the final exponentiation.
- **The key compiled in.** For Groth16, δ's lines are constants. γ and the IC points become tables of pairing values selected by the public inputs' bits, so the inputs' combination L = IC_0 + Σ x_i IC_i is never computed.
- **fflonk** reuses the arithmetic and the pairing check. It adds a Keccak-256 transcript, F_r arithmetic for the opening, and a G1 multi-scalar multiplication with hints.

Each verifying key gives its own program (2.8 MB of Simplicity text for the toy circuit), so the repository has no hand-written Simplicity. The tools write the programs into `build/`. The [Groth16 document](docs/groth16.md) explains the method, and [benchmarks](docs/benchmarks.md) has the numbers.

## Requirements

- Python 3.10 or later, with no packages, and Rust 1.97 (pinned in `tools/harness/rust-toolchain.toml`) for the harness.
- For the circuits: [circom](https://github.com/iden3/circom/releases) 2.2.2 and Node.js 22. snarkjs 0.7.6 and circomlib come from `npm ci --ignore-scripts` in `circuits/`.
- For Noir circuits: nargo 1.0.0-beta.19 and Noir-Groth16's `noir-cli` ([docs/noir.md](docs/noir.md)).
- For the regtest walkthrough: [Elements Core](https://github.com/ElementsProject/elements/releases) 23.3.1.

Tested with Python 3.10, 3.13 and 3.14, rust-simplicity 0.9.0, Elements Core 23.3.1, circom 2.2.2, snarkjs 0.7.6, nargo 1.0.0-beta.19 and Node.js 22.

## Quick start

```sh
make harness         # builds hand, deploy, costs and sizes (tools/harness)
make test-fp         # field arithmetic
make test-groth16    # the whole Groth16 verifier
make -j4 test        # all tests, in parallel
```

Each test generates programs for one layer and runs them through `hand`, which executes them the way a node does. It compares every result with the plain-Python model, and every cost with the generator's prediction. `make help` lists the targets. `make test-bn254_ref` checks the reference code against py_ecc, which it needs: `pip install --require-hashes -r ci/requirements-ref.txt`.

## The toy circuit on regtest

![From a circom circuit to a Liquid spend: what circom and snarkjs produce, what the Python generator produces, and what deploy builds](docs/architecture.png)

`circuits/multiplier.circom` is a toy statement: the prover knows `a` and `b` with `a * b = c`. Its public signal is the Merkle root of the spending transaction's sighash and `c`. Anyone with its proving key can satisfy it for any `c`, so it locks nothing of value.

1. Build the key and the program:

   ```sh
   cd circuits && npm ci --ignore-scripts && cd ..
   python3 tools/demo.py setup --out build/multiplier
   D=tools/harness/target/release/deploy
   P=build/multiplier/verifier.uprog
   $D compile build/multiplier/verifier.simpl build/multiplier/verifier
   ```

   `setup` takes about two minutes. It compiles the circuit, downloads a powers-of-tau file and checks it against a pinned digest, runs the snarkjs setup, and writes `verifier.simpl`. `deploy compile` takes about three minutes. It parses the program once and writes `verifier.uprog`, its consensus encoding, and `verifier.wnames`, the order of its witness nodes.

2. On a node set up as `tools/regtest.sh` describes, get the address and fund it:

   ```sh
   $D address $P elementsregtest                  # the address and its script_pubkey
   elements-cli sendtoaddress <address> 1.0        # the txid
   elements-cli getrawtransaction <txid> true      # the vout whose scriptPubKey hex is that script_pubkey
   ```

3. Compute the sighash of the transaction that will spend it. Here it pays 1.0 minus a fee of 100,000 sats to `<dest>`, an unconfidential address; `<asset>` is `elements-cli dumpassetlabels`'s `bitcoin`.

   ```sh
   G=$(elements-cli getblockhash 0)
   $D sighash $P elementsregtest <txid> <vout> 100000000 <asset> <dest> 100000 --genesis $G
   ```

4. Prove the statement for that sighash. This checks the proof and writes the verifier's witness:

   ```sh
   python3 tools/demo.py prove --out build/multiplier --sighash <sighash> --a 3 --b 7
   ```

5. Build the transaction and send it:

   ```sh
   $D spend $P build/multiplier/verifier.w0.json elementsregtest <txid> <vout> 100000000 <asset> <dest> 100000 --genesis $G > spend.hex
   elements-cli -stdin sendrawtransaction < spend.hex
   ```

`deploy spend` prunes the program against this transaction and executes it, so a wrong witness fails before anything is sent. It also refuses a spend that a node would not take: one above the consensus cap on the Bit Machine's cells, one whose budget does not cover its cost, or one above the standard weight.

`tools/regtest.sh build/multiplier` runs steps 2 to 5 as a script. It then shows that the same proof is rejected in a transaction paying someone else, and spends a second output of the same leaf through a key path. The fflonk and Noir toy circuits run the same way:

```sh
python3 tools/demo.py setup --protocol fflonk --transcript sha256 --out build/fflonk    # or --transcript keccak
python3 tools/demo.py setup --frontend noir --out build/noir
```

## On Liquid testnet and Liquid

Simplicity is active on Liquid, [since July 2025](https://blog.blockstream.com/simplicity-launches-on-liquid-mainnet/), and on Liquid testnet. The verifiers run there unchanged: only the address and the transaction depend on the network, and `deploy` knows both networks' parameters. `tools/liquid.py` spends a verifier's output on either network, or on a regtest node. It reads the chain through an Esplora server (Blockstream's by default) or your own node (`--node "elements-cli ..."`), and builds every transaction with `deploy`. It needs only Python and the harness.

```sh
L="python3 tools/liquid.py"; P=build/multiplier/verifier.uprog; N="--network liquidtestnet"   # or liquid
$L address $P $N              # the verifier's address, to fund with an explicit output
$L faucet <address>           # Liquid testnet only: test coins from liquidtestnet.com
$L utxos $P $N                # the outputs that pay the verifier
$L prove $P <txid>:<vout> <your address> $N \
   --prove "python3 tools/demo.py prove --out build/multiplier --sighash {sighash}" \
   --witness build/multiplier/verifier.w0.json --broadcast
```

The proof binds the spending transaction, fee included, so the fee is fixed before proving. `prove` runs your prover with the sighash in place of `{sighash}`, builds the transaction, and proves again if the size it measures needs a higher fee. The fee rate is 0.1 sat/vB, Liquid's minimum relay feerate, unless you give `--fee-rate`. Pass `--vsize` from an earlier spend of the same verifier to prove once. With a prover the tool should not run, use two steps: `sighash` prints the sighash for a fee, and `spend` builds the transaction from your witness file. For your own verifier, give its `.uprog` and a prover that ends with the witness command of its binding ([Your circuit](#your-circuit)).

Nothing is sent without `--broadcast`. The transaction is printed, or written with `--out`. `deploy` executes it first, and refuses a transaction whose cost its budget does not cover, that needs more Bit Machine cells than consensus allows, or that is above the standard weight. With `--node`, testmempoolaccept checks it as well. `python3 tools/liquid.py --help` has every command, including `keyspend` and `broadcast`.

Fund the verifier with an explicit output of L-BTC, which pays the fee. Its address is unconfidential, so a wallet that pays it writes the amount in the clear, which the program's sighash needs. A wallet that pays only confidential addresses can pay `deploy wallet`'s address instead, and `deploy send` then moves the coins to the verifier. At 0.1 sat/vB the fee is about 1,300 sat for the Groth16 toy spend and 4,600 sat for fflonk with Keccak. Each toy verifier has been spent this way on Liquid testnet ([docs/benchmarks.md](docs/benchmarks.md) lists the transactions).

> ⚠️ The toy statements are public: anyone can prove a·b = c for their own transaction. Once your funding transaction is seen, anyone can race you to the output. Fund a toy verifier on Liquid only with what you would give away. A verifier for your own circuit is as safe as that circuit's statement and setup.

## Your circuit

The program binds the proof to the spending transaction in one of three ways, and each expects the circuit to expose the sighash in its own way:

| verifier | the circuit | program | witness |
|---|---|---|---|
| Groth16, circom | includes `circuits/public_merkle.circom`, takes `sighash[2]` and feeds its public values into `PublicMerkleRoot(n)`, whose `root` is its only public signal | `groth16_snarkjs.py program vk.json --values n` | `groth16_snarkjs.py witness vk.json proof.json public.json --leaves leaves.json` |
| Groth16, Noir (or any circuit that cannot hash) | takes the sighash, with its top three bits cleared, as its first public input | `groth16_snarkjs.py program vk.json --sighash-input` | `... --sighash-input --sighash <hex>` |
| fflonk | takes the sighash as its first two public inputs, two 128-bit limbs, high then low | `fflonk_snarkjs.py program vk.json --transcript keccak --bind` | `fflonk_snarkjs.py witness vk.json proof.json public.json --transcript keccak --bind` |

All the tools live in `tools/`, and every command takes `--out build/x`. For the Merkle binding, `leaves.json` is `{"sighash": "<64 hex digits>", "values": ["<decimal>", ...]}`, with the sighash from `deploy sighash` and the values in circuit order. `n` may be 0, which gives `PublicMerkleRoot(0)`, a tree that holds only the sighash. A Noir circuit goes through `tools/noir_r1cs.py` first ([docs/noir.md](docs/noir.md)).

The program checks only the binding input. The spender chooses every other public input, and each one is published in the spend. So the circuit must fix the statement's constants itself: the program does not pin them. In the Merkle binding the program sees only the root, not the values behind it.

A circuit that follows none of these conventions needs `--unbound`. Each of its public signals is then a verifier input; with Groth16, each costs about 6 M mWU and 12 to 14 kB. Nothing binds the proof to the transaction: anyone who sees the spend can reuse its witness in another transaction to the same output.

## Repository

| | |
|---|---|
| `groth/core/` | what both verifiers use: `bn254.py` (the plain-Python reference), `sym.py` and `dsl.py` (the two backends and the Simplicity text), `fp.py` (F_p and F_r), `poly.py`, `curve.py`, `pairing.py`, `msm.py`, `frprog.py` (F_r straight-line code), `keccak.py`, `snarkjs.py` (snarkjs's files), `binding.py` (the transaction bindings), `budget.py` |
| `groth/groth16/` | the Groth16 verifier |
| `groth/fflonk/` | the fflonk verifier, and `reference.py`, a port of snarkjs's fflonk verifier |
| `circuits/` | `public_merkle.circom` (the Merkle binding), the toy `multiplier.circom`, `multiplier_fflonk.circom` for fflonk, and `noir/multiplier`, the toy statement in Noir |
| `tools/` | `groth16_snarkjs.py` and `fflonk_snarkjs.py` (from a snarkjs key and proof to the program and its witness), `noir_r1cs.py` (a Noir circuit as R1CS), `snarkjs_sha256.mjs` (fflonk proofs with a SHA-256 transcript), `demo.py` (the toy circuits end to end), `regtest.sh` (the toy circuits on a regtest node) and `liquid.py` (spending a verifier on Liquid, Liquid testnet or regtest) |
| `tools/harness/` | Rust: `hand` runs generated programs for the tests, `costs` and `sizes` profile them, `deploy` builds addresses and transactions |
| `tests/` | one test per layer, plus `test_bn254_ref.py` against py_ecc |
| `examples/` | generated programs and the test fixtures ([examples/README.md](examples/README.md)) |
| `docs/` | `groth16.md`, `fflonk.md` and `noir.md` (how each part works), `benchmarks.md` |
| `ci/`, `.github/` | CI, and the hash-pinned Python requirements it installs |

## Development

`make lint` runs what CI checks besides the tests: ruff, mypy, `cargo fmt --check` and clippy. To install the same linters CI uses, run `pip install --require-hashes -r ci/requirements-lint.txt`. `make fmt` formats the code. `make example` checks that the files in `examples/` regenerate byte for byte, so a change that alters a generated program shows up there.

## Credits and references

- [Simplicity](https://github.com/BlockstreamResearch/simplicity), rust-simplicity and libsimplicity (Blockstream Research): the language, and the parser and cost model the harness uses. [Elements](https://github.com/ElementsProject/elements) and Liquid: the chain the programs run on. [Esplora](https://github.com/Blockstream/esplora) (Blockstream) and the [Liquid testnet faucet](https://liquidtestnet.com/faucet) (Valerio Vaccaro), which `tools/liquid.py` uses.
- [circom, circomlib](https://github.com/iden3/circom) and [snarkjs](https://github.com/iden3/snarkjs) (iden3): circuits, setups and proofs. `groth/fflonk/reference.py` ports snarkjs's fflonk verifier.
- [Noir](https://noir-lang.org) (Aztec), and [Noir-Groth16](https://github.com/jamesbachini/Noir-Groth16) (James Bachini), whose `noir-cli` converts Noir's ACIR to R1CS.
- The [perpetual powers of tau](https://github.com/privacy-scaling-explorations/perpetualpowersoftau) ceremony (Privacy & Scaling Explorations), whose files the demo's setups use.
- Novakovic and Eagen, [On Proving Pairings](https://eprint.iacr.org/2024/640) (2024): the residue witness, and the relations combined into one quotient.
- [Garaga](https://hackmd.io/@feltroidprime/B1eyHHXNT): randomized arithmetic in F_p12.
- Gabizon and Williamson, [fflonk](https://eprint.iacr.org/2021/1167) (2021).
- Gallant, Lambert and Vanstone (2001): the GLV decomposition in the fflonk MSM. Bajard, Didier and Kornerup, [RNS Montgomery multiplication](https://doi.org/10.1109/12.709376) (1998). Bertoni, Daemen, Peeters and Van Assche: Keccak.
- [py_ecc](https://github.com/ethereum/py_ecc) (Ethereum Foundation): the cross-check of the reference code.

## License

[MIT](LICENSE)
