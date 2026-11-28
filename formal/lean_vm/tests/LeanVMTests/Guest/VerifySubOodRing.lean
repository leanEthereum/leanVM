import LeanVM.Guest.B1.VerifySub.PhOodRingOod
import LeanVM.Guest.B1.VerifySub.PhOodRingRing

/-!
# `verify_sub`'s out-of-domain and ring switch phases, pinned

`PhOod` and `PhRing` (`Phases.lean`) proved, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.gcInlineAt_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.gcInlineAt_sound

/-- info: 'LeanVM.Guest.B1.VerifySub.phOod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phOod

/-- info: 'LeanVM.Guest.B1.VerifySub.ct_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.ct_reads

/-- info: 'LeanVM.Guest.B1.VerifySub.runsTo_grindPacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.runsTo_grindPacked

/-- info: 'LeanVM.Guest.B1.VerifySub.phRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.phRing
