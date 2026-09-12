import SphincsSecurity.Statement
import SphincsSecurity.Proof

namespace SphincsSecurity

/-!
The main result. Its statement lives entirely in the single module `SphincsSecurity.Statement`; the modules under `SphincsSecurity/Proof/` only contribute to the proof, which splits the whole-experiment hash budget at `3 * 2^114`: larger budgets are bounded by the retained residual certificate monitor, and smaller budgets reduce the remaining near-certificate event to forced FTS guess games that are bounded slot by slot.
-/

/-- `127` bits of classical strong unforgeability in the random-oracle model for the concrete SPHINCS instance, at `2^24` signing requests per key pair. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Concrete.security127

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'SphincsSecurity.sphincs_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sphincs_has_127_bits_of_classical_security

end SphincsSecurity
