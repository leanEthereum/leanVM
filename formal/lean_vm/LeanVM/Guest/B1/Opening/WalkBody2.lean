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
/-- `walk_path__L12_L2`. -/
theorem wpBody_L12_L2 : Data.core1597.body = wpBodyT ⟨0, 0, 12, 2, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5`. -/
theorem wpBody_L12_L5 : Data.core1511.body = wpBodyT ⟨0, 0, 12, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8`. -/
theorem wpBody_L12_L8 : Data.core1600.body = wpBodyT ⟨0, 0, 12, 8, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4`. -/
theorem wpBody_L18_L4 : Data.core1549.body = wpBodyT ⟨0, 0, 18, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7`. -/
theorem wpBody_L18_L7 : Data.core1570.body = wpBodyT ⟨0, 0, 18, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L4`. -/
theorem wpBody_L24_L4 : Data.core1591.body = wpBodyT ⟨0, 0, 24, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
