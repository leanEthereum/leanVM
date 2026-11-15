import Quantum.Model

/-! Security against quantum adversaries in the quantum random-permutation model (`Quantum.Model`),
on VCVio's quantum oracle programs (`VCVio.Quantum`). The build fails if the axiom footprint of
the main theorems ever grows beyond Lean's three standard axioms. -/

/-- info: 'Quantum.qrpmEvalDist_apply_univ_of_lossless' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quantum.qrpmEvalDist_apply_univ_of_lossless
