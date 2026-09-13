import XmssSecurity.Statement
import XmssSecurity.Proof.Seeded.Security

namespace XmssSecurity

/-- XMSS with a 256-bit master seed has 127 bits of classical security. -/
theorem xmss_has_127_bits_of_classical_security : XmssSecurityStatement :=
  Seeded.scheme_has_127_bits_of_classical_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.xmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_has_127_bits_of_classical_security

end XmssSecurity
