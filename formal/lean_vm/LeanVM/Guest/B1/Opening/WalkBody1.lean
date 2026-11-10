/-
  LeanVM.Guest.B1.Opening.WalkBody1

  The bodies of a third of `walk_path`'s specializations are the template (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L8`. -/
theorem wpBody_L9_L8 : Data.core1033.body = wpBodyT ⟨0, 0, 9, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L8`. -/
theorem wpBody_L10_L8 : Data.core943.body = wpBodyT ⟨0, 0, 10, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L7`. -/
theorem wpBody_L11_L7 : Data.core973.body = wpBodyT ⟨0, 0, 11, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6`. -/
theorem wpBody_L12_L6 : Data.core1039.body = wpBodyT ⟨0, 0, 12, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L5`. -/
theorem wpBody_L13_L5 : Data.core1042.body = wpBodyT ⟨0, 0, 13, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L8`. -/
theorem wpBody_L13_L8 : Data.core958.body = wpBodyT ⟨0, 0, 13, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L6`. -/
theorem wpBody_L14_L6 : Data.core1009.body = wpBodyT ⟨0, 0, 14, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L4`. -/
theorem wpBody_L15_L4 : Data.core1049.body = wpBodyT ⟨0, 0, 15, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L7`. -/
theorem wpBody_L15_L7 : Data.core985.body = wpBodyT ⟨0, 0, 15, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L5`. -/
theorem wpBody_L16_L5 : Data.core1045.body = wpBodyT ⟨0, 0, 16, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L4`. -/
theorem wpBody_L17_L4 : Data.core1051.body = wpBodyT ⟨0, 0, 17, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L7`. -/
theorem wpBody_L17_L7 : Data.core991.body = wpBodyT ⟨0, 0, 17, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6`. -/
theorem wpBody_L18_L6 : Data.core1021.body = wpBodyT ⟨0, 0, 18, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L6`. -/
theorem wpBody_L19_L6 : Data.core1024.body = wpBodyT ⟨0, 0, 19, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
