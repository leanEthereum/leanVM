import LeanVM.Guest.B1.VerifySub.Chain
import LeanVM.Guest.B1.VerifySub.Reads
import LeanVM.Guest.B1.VerifySub.Export
import LeanVM.Guest.B1.VerifySub.Sizes
import LeanVM.Guest.B1.VerifySub.Sound
import LeanVM.Guest.VsKaps
import LeanVM.Cost.GuestKnowledgeVs

/-!
# `verify_sub` in the circuit, pinned

`verify_sub`'s phases chained into the deferring verifier's acceptance of the decoded child proof,
on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VerifySub.subSoundW_of_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.subSoundW_of_phases

/-- info: 'LeanVM.Guest.B1.VerifySub.phSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phSeed

/-- info: 'LeanVM.Guest.B1.VerifySub.phRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phRoot

/-- info: 'LeanVM.Guest.B1.VerifySub.phExport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phExport

/-- info: 'LeanVM.Guest.B1.VerifySub.phSizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phSizes

/-- info: 'LeanVM.Guest.B1.VerifySub.phKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phKeccak

/-- info: 'LeanVM.Guest.B1.VerifySub.subSoundW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.subSoundW_of

/-- info: 'LeanVM.Guest.End.vsKapsKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.vsKapsKnown_proved

/-- info: 'LeanVM.Guest.End.vsGmvKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.vsGmvKnown_proved

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_of_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_of_phases
