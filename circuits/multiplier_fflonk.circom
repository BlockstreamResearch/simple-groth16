pragma circom 2.0.0;

// The toy statement for the fflonk verifier (groth/fflonk.py): the prover knows a and b with a * b = c.
//
// The public inputs are the sighash of the spending transaction, as two 128-bit limbs (high, then low),
// then c.  The verifier compares the first two with its sig_all_hash jet, so a proof is valid for one
// transaction only.  fflonk's verifier pays little per public input (a Lagrange evaluation and a
// product), so the sighash is bound directly, without the Merkle root of public_merkle.circom that the
// Groth16 verifier uses to keep to one public input.
template Multiplier() {
    signal input sighash[2];
    signal input a;
    signal input b;
    signal input c;
    a * b === c;
    // the sighash in a constraint of its own, so that it is a wire of the circuit like c
    signal s;
    s <== sighash[0] * sighash[1];
}

component main {public [sighash, c]} = Multiplier();
