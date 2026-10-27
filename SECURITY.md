# Security Policy

Simple Groth16 is experimental research code. It has not been independently audited, so don't use it with funds you cannot lose.

## Scope

The scope is the generators of both verifiers, Groth16 and fflonk, the programs they write, and the tools in `tools/`. Reports we are most interested in:

- a witness that a generated program accepts although no valid proof exists for its key and public inputs;
- a proof that a bound program accepts in a transaction other than the one whose sighash it commits to;
- a static bound in the generator that is wrong, so that an intermediate value can wrap around;
- a check of `tools/noir_r1cs.py` that lets through an opcode the R1CS does not constrain;
- a tool that builds a different program, witness or transaction from the one it reports.

Out of scope:

- the trusted setup of your own circuit, and the soundness of the circuit itself;
- the toy circuits `circuits/multiplier.circom`, `circuits/multiplier_fflonk.circom` and `circuits/noir/multiplier`, and their demo setups (one phase-2 contribution for Groth16, none for fflonk), which anyone with the proving key can satisfy for any `c`;
- programs compiled with `--unbound`, whose witness anyone can reuse in another transaction to the same output (the tools say so);
- bugs in Simplicity, rust-simplicity, Elements, snarkjs, circom, nargo or noir-cli (report those to their projects).

## How to contact us

Email m.j.thatch@proton.me.
