"""Generators of Simplicity programs that verify SNARKs on BN254, for Liquid.

groth.core     the shared parts: the BN254 reference (bn254), the expression builders (sym, dsl),
               F_p and F_r (fp), the curves (curve), the pairing check (pairing, poly), G1 MSMs
               (msm), F_r straight-line code (frprog), Keccak (keccak), snarkjs's files (snarkjs),
               the transaction bindings (binding) and the input's budget (budget)
groth.groth16  the Groth16 verifier
groth.fflonk   the fflonk verifier, with a plain-Python port of snarkjs's (reference)
"""
