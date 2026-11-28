import LeanVM.Guest.B1.VerifySub.PhLink
import LeanVM.Cost.GuestKnowledgeHolds

/-!
# `verify_sub`'s link phase, pinned

`PhLink` (`Phases.lean`) proved, and its pieces, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VerifySub.VsRun.shapeOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VsRun.shapeOk

/-- info: 'LeanVM.Guest.B1.VerifySub.VsRun.linkRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.VsRun.linkRun

/-- info: 'LeanVM.Guest.B1.VerifySub.end_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.end_pieces

/-- info: 'LeanVM.Guest.B1.VerifySub.phLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phLink

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_holds

example : LeanVM.Node.GuestKnowledgeSoundness LeanVM.Cost.compiledGuestWitnessDecoder :=
  LeanVM.Cost.guestKnowledgeSoundness_holds
