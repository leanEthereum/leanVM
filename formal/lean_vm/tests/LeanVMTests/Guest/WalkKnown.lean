import LeanVM.Guest.WalkKnownAll
import LeanVM.Guest.EndSound

/-!
# The walks' cut obligations, pinned

`WalkKnown`, B2's hypothesis on the windowed functions other than `main` and `verify_sub`
(`open_stacked`'s arms, `level_queries`' and `opening_queries`' specializations and its loops),
proved from B1's walk facts and the kernel-checked certificates (`walkKnown_proved`), on Lean's
three axioms.
-/

/-- info: 'LeanVM.Guest.End.walkKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.walkKnown_proved

example : LeanVM.Guest.End.WalkKnown := LeanVM.Guest.End.walkKnown_proved

/-- B2's end theorem with the walks discharged. -/
example : LeanVM.Guest.End.VsKapsKnown → LeanVM.Guest.End.VsGmvKnown → LeanVM.Guest.End.B2SoundL :=
  fun hkaps hgmv ↦ LeanVM.Guest.End.b2SoundL_of hkaps hgmv LeanVM.Guest.End.walkKnown_proved
