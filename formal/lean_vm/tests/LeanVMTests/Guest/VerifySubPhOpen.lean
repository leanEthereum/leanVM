import LeanVM.Guest.B1.VerifySub.PhOpen

/-!
# `verify_sub`'s stacked opening, pinned

The opening phase from the out-of-domain phase, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VerifySub.phOpen_of_ood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phOpen_of_ood

/-- info: 'LeanVM.Guest.B1.VerifySub.subSoundW_of_ood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.subSoundW_of_ood
