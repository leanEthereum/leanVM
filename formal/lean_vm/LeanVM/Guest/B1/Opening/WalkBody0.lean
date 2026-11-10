/-
  LeanVM.Guest.B1.Opening.WalkBody0

  The bodies of a third of `walk_path`'s specializations are the template (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L5`. -/
theorem wpBody_L9_L5 : Data.core1036.body = wpBodyT ⟨0, 0, 9, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L6`. -/
theorem wpBody_L10_L6 : Data.core1034.body = wpBodyT ⟨0, 0, 10, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L6`. -/
theorem wpBody_L11_L6 : Data.core1037.body = wpBodyT ⟨0, 0, 11, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5`. -/
theorem wpBody_L12_L5 : Data.core1040.body = wpBodyT ⟨0, 0, 12, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8`. -/
theorem wpBody_L12_L8 : Data.core953.body = wpBodyT ⟨0, 0, 12, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L7`. -/
theorem wpBody_L13_L7 : Data.core979.body = wpBodyT ⟨0, 0, 13, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L5`. -/
theorem wpBody_L14_L5 : Data.core1043.body = wpBodyT ⟨0, 0, 14, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L8`. -/
theorem wpBody_L14_L8 : Data.core963.body = wpBodyT ⟨0, 0, 14, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L6`. -/
theorem wpBody_L15_L6 : Data.core1012.body = wpBodyT ⟨0, 0, 15, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L4`. -/
theorem wpBody_L16_L4 : Data.core1048.body = wpBodyT ⟨0, 0, 16, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L7`. -/
theorem wpBody_L16_L7 : Data.core988.body = wpBodyT ⟨0, 0, 16, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L6`. -/
theorem wpBody_L17_L6 : Data.core1018.body = wpBodyT ⟨0, 0, 17, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5`. -/
theorem wpBody_L18_L5 : Data.core1050.body = wpBodyT ⟨0, 0, 18, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L5`. -/
theorem wpBody_L19_L5 : Data.core1052.body = wpBodyT ⟨0, 0, 19, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L6`. -/
theorem wpBody_L20_L6 : Data.core1028.body = wpBodyT ⟨0, 0, 20, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
