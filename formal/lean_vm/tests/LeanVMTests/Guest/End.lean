import LeanVM.Guest.EndSound
import LeanVM.Guest.EndComplete
import LeanVM.Guest.EndFinal
import LeanVM.Guest.EndFinalComplete

/-!
# Tests: the end theorems' axioms

The end theorems from their pieces (`LeanVM.Guest.End`, `LeanVM.Guest.EndSound`) rest on Lean's
three standard axioms only.
-/

/-- info: 'LeanVM.Guest.End.guest_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound_of

/-- info: 'LeanVM.Guest.End.guest_complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete_of

/-- info: 'LeanVM.Guest.End.aggregate_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_of

/-- info: 'LeanVM.Guest.End.aggregate_complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete_of

/-- info: 'LeanVM.Guest.End.guest_sound_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound_of_parts

/-- info: 'LeanVM.Guest.End.aggregate_sound_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_of_parts

/-- info: 'LeanVM.Guest.End.guest_complete_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete_within

/-- info: 'LeanVM.Guest.End.b1Sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.b1Sound

/-- info: 'LeanVM.Guest.End.guest_sound_of_b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound_of_b2

/-- info: 'LeanVM.Guest.End.aggregate_sound_of_b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_of_b2

/-- info: 'LeanVM.Guest.End.vsKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.vsKnown_proved

/-- info: 'LeanVM.Guest.End.honest_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.honest_of_main

/-- info: 'LeanVM.Guest.End.guest_complete_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete_of_parts

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-- info: 'LeanVM.Guest.End.aggregate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound

/-- info: 'LeanVM.Guest.End.guest_complete_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete_of_open

/-- info: 'LeanVM.Guest.End.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_complete

/-- info: 'LeanVM.Guest.End.aggregate_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete
