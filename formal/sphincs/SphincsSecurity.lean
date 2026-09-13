import SphincsSecurity.Statement
import SphincsSecurity.Proof.Seeded.Security

namespace SphincsSecurity

/-- The SPHINCS scheme with a 256-bit master seed has 127 bits of classical security. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Seeded.scheme_has_127_bits_of_classical_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'SphincsSecurity.sphincs_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_has_127_bits_of_classical_security

end SphincsSecurity
