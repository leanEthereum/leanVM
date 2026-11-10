/-
  LeanVM.Guest.B1.Opening.WalkBody2

  The bodies of a third of `walk_path`'s specializations are the template (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L5`. -/
theorem wpBody_L10_L5 : Data.core1035.body = wpBodyT ⟨0, 0, 10, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L5`. -/
theorem wpBody_L11_L5 : Data.core1038.body = wpBodyT ⟨0, 0, 11, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L8`. -/
theorem wpBody_L11_L8 : Data.core948.body = wpBodyT ⟨0, 0, 11, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7`. -/
theorem wpBody_L12_L7 : Data.core976.body = wpBodyT ⟨0, 0, 12, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L6`. -/
theorem wpBody_L13_L6 : Data.core1041.body = wpBodyT ⟨0, 0, 13, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L4`. -/
theorem wpBody_L14_L4 : Data.core1046.body = wpBodyT ⟨0, 0, 14, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L7`. -/
theorem wpBody_L14_L7 : Data.core982.body = wpBodyT ⟨0, 0, 14, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L5`. -/
theorem wpBody_L15_L5 : Data.core1044.body = wpBodyT ⟨0, 0, 15, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L8`. -/
theorem wpBody_L15_L8 : Data.core968.body = wpBodyT ⟨0, 0, 15, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L6`. -/
theorem wpBody_L16_L6 : Data.core1015.body = wpBodyT ⟨0, 0, 16, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L5`. -/
theorem wpBody_L17_L5 : Data.core1047.body = wpBodyT ⟨0, 0, 17, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4`. -/
theorem wpBody_L18_L4 : Data.core1054.body = wpBodyT ⟨0, 0, 18, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7`. -/
theorem wpBody_L18_L7 : Data.core1003.body = wpBodyT ⟨0, 0, 18, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L5`. -/
theorem wpBody_L20_L5 : Data.core1053.body = wpBodyT ⟨0, 0, 20, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
