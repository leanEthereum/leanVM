import LeanXmss.Statement
import XmssSecurity.Proof.Bridge.Security

namespace XmssSecurity

/-- leanXMSS has 127 bits of classical security. -/
theorem leanXmss_has_127_bits_of_classical_security : LeanXmss.LeanXmssSecurityStatement :=
  Bridge.leanXmss_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.leanXmss_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_has_127_bits_of_classical_security

end XmssSecurity
