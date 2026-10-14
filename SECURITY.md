# Security Policy

Simple Groth16 is experimental and has not been audited.

## Scope

Reports we are most interested in:

* a witness that a generated program accepts although no valid Groth16 proof exists for its key and public input;
* a proof that a generated program accepts in a transaction other than the one whose sighash it commits to;
* a static bound in the generator that is wrong, so that an intermediate value can wrap around;
* a tool that builds a different program, witness or transaction from the one it reports.

Out of scope: 
1. the trusted setup of your own circuit;
2. the toy circuit `circuits/multiplier.circom`, which anyone with its proving key can satisfy for any `c`; 
3. bugs in Simplicity, rust-simplicity or Elements (report such bugs to those projects).

## How to Contact Us

Email m.j.thatch@proton.me