pragma circom 2.0.0;

// Toy statement: the prover knows a and b with a * b = c
include "public_merkle.circom";

template Multiplier() {
    signal input a;
    signal input b;
    signal input c;
    signal input sighash[2];
    signal output root;

    a * b === c;

    component m = PublicMerkleRoot(1);
    m.sighash[0] <== sighash[0];
    m.sighash[1] <== sighash[1];
    m.values[0] <== c;
    root <== m.root;
}

component main = Multiplier();
