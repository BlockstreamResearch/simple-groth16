pragma circom 2.0.0;

// The public-signal convention of circuits for the Simplicity verifier (groth/merkle.py computes the
// same root in Python).  The circuit has one public signal, the SHA-256 Merkle root of its public
// values, so the verifier's cost does not depend on how many there are.  Leaf 0 is the sighash of the
// spending transaction, which the verifier compares with its sig_all_hash jet.
//
//   leaves:  leaf 0 = the sighash (two 128-bit limbs: high, low)
//            leaf i = the i-th public value as a 32-byte big-endian word (a field element, < r)
//            2^depth leaves, depth = max(1, ceil(log2(n + 1))), the missing leaves are zero
//   nodes:   SHA-256(left || right)
//   root:    the 32-byte root with its top three bits cleared: the public signal
//
// Each hashed node costs about 59 k constraints.
include "circomlib/circuits/sha256/sha256.circom";
include "circomlib/circuits/bitify.circom";

function log2ceil(x) {
    var d = 0;
    while ((1 << d) < x) {
        d++;
    }
    return d;
}

// SHA-256(left || right): 256-bit words as bits in message order (bit 0 is the most significant bit
// of the first byte, the order of circomlib's Sha256)
template HashNode() {
    signal input left[256];
    signal input right[256];
    signal output out[256];
    component h = Sha256(512);
    for (var i = 0; i < 256; i++) {
        h.in[i] <== left[i];
        h.in[256 + i] <== right[i];
    }
    for (var i = 0; i < 256; i++) {
        out[i] <== h.out[i];
    }
}

// a field element as the bits of its 32-byte big-endian encoding, in message order
template WordBits() {
    signal input in;
    signal output out[256];
    component n = Num2Bits_strict();
    n.in <== in;
    out[0] <== 0;
    out[1] <== 0;
    for (var i = 0; i < 254; i++) {
        out[255 - i] <== n.out[i];
    }
}

// a 32-byte value given as two 128-bit limbs (high, low), as bits in message order
template LimbsBits() {
    signal input in[2];
    signal output out[256];
    component hi = Num2Bits(128);
    component lo = Num2Bits(128);
    hi.in <== in[0];
    lo.in <== in[1];
    for (var i = 0; i < 128; i++) {
        out[127 - i] <== hi.out[i];
        out[255 - i] <== lo.out[i];
    }
}

// the root of the tree of the sighash and n public values, as a field element
template PublicMerkleRoot(n) {
    signal input sighash[2];
    signal input values[n];
    signal output root;

    var depth = log2ceil(n + 1);
    if (depth < 1) {
        depth = 1;
    }
    var width = 1 << depth;
    // node[k] for k = 1 .. 2 width - 1 is a heap: node[1] the root, node[2k] and node[2k + 1] the
    // children of node[k], node[width + j] leaf j
    signal node[2 * width][256];

    component sh = LimbsBits();
    sh.in[0] <== sighash[0];
    sh.in[1] <== sighash[1];
    for (var i = 0; i < 256; i++) {
        node[width][i] <== sh.out[i];
    }
    component wb[n];
    for (var j = 0; j < n; j++) {
        wb[j] = WordBits();
        wb[j].in <== values[j];
        for (var i = 0; i < 256; i++) {
            node[width + 1 + j][i] <== wb[j].out[i];
        }
    }
    for (var j = n + 1; j < width; j++) {
        for (var i = 0; i < 256; i++) {
            node[width + j][i] <== 0;
        }
    }
    component hn[width];
    for (var k = width - 1; k >= 1; k--) {
        hn[k] = HashNode();
        for (var i = 0; i < 256; i++) {
            hn[k].left[i] <== node[2 * k][i];
            hn[k].right[i] <== node[2 * k + 1][i];
        }
        for (var i = 0; i < 256; i++) {
            node[k][i] <== hn[k].out[i];
        }
    }
    // the root word without its three top bits
    var acc = 0;
    var pw = 1;
    for (var i = 255; i >= 3; i--) {
        acc += node[1][i] * pw;
        pw = pw * 2;
    }
    root <== acc;
}
