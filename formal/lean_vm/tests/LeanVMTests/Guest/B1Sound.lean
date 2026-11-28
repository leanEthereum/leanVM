import LeanVM.Guest.B1.Main.SoundV

/-!
# B1's soundness, pinned

`main`'s soundness for Hotwire's guest given `verify_sub`'s statement
(`LeanVM.Guest.B1.Main.main_sound_V_of_sub`), `aggregate_claims`' and `exponent_tables`' statements
proved, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.Main.main_sound_V_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Main.main_sound_V_of_sub

/-- info: 'LeanVM.Guest.B1.Main.aggregate_claims_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Main.aggregate_claims_holds

/-- info: 'LeanVM.Guest.B1.exponent_tables_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.exponent_tables_holds
