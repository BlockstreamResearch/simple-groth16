// The toy statement, in Noir: the prover knows a and b with a * b = c.
//
// The first public input is the sighash of the spending transaction, with its top three bits cleared so
// that it is below r (as the Merkle root of circuits/public_merkle.circom is); the verifier compares it
// with its sig_all_hash jet, so a proof is valid for one transaction only (tools/groth16_snarkjs.py
// --sighash-input).  The circuit does not hash: noir-cli's R1CS cannot hold every hash soundly
// (tools/noir_r1cs.py).  The sighash needs no constraint of its own: snarkjs's setup ties every public
// input to the proof.
fn main(sighash: pub Field, c: pub Field, a: Field, b: Field) {
    let _ = sighash;
    assert(a * b == c);
}
