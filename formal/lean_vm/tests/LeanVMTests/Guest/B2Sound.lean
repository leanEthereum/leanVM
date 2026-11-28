import LeanVM.Guest.EndSound

/-!
# B2's soundness, pinned

The compiled guest against its core IR for Hotwire's guest (`LeanVM.Guest.End.b2SoundL_of`), from
the kernel-checked certificates, given `verify_sub`'s kappas and stack log (`VsKapsKnown`,
`VsGmvKnown`) and the walks' cut obligations (`WalkKnown`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.End.b2SoundL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.b2SoundL_of

/-- info: 'LeanVM.Guest.End.vsTabsKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.vsTabsKnown_proved

/-- The end theorem's hypotheses, pinned. -/
example : LeanVM.Guest.End.VsKapsKnown → LeanVM.Guest.End.VsGmvKnown → LeanVM.Guest.End.WalkKnown →
    LeanVM.Guest.End.B2SoundL :=
  LeanVM.Guest.End.b2SoundL_of
