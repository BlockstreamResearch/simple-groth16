pragma circom 2.0.0;

// Toy statement: the prover knows a and b with a * b = c.  The public signal is the root of the sighash
// and c, with `bits` bits (253, or fewer for a verifier compiled with --signal-bits).
include "public_merkle.circom";

template Multiplier(bits) {
    signal input a;
    signal input b;
    signal input c;
    signal input sighash[2];
    signal output root;

    a * b === c;

    component m = PublicMerkleRootBits(1, bits);
    m.sighash[0] <== sighash[0];
    m.sighash[1] <== sighash[1];
    m.values[0] <== c;
    root <== m.root;
}

component main = Multiplier(253);
