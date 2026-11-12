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
/-- `walk_path__L6_L6`. -/
theorem wpBody_L6_L6 : Data.core1599.body = wpBodyT ⟨0, 0, 6, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L3`. -/
theorem wpBody_L12_L3 : Data.core1507.body = wpBodyT ⟨0, 0, 12, 3, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6`. -/
theorem wpBody_L12_L6 : Data.core1513.body = wpBodyT ⟨0, 0, 12, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L2`. -/
theorem wpBody_L18_L2 : Data.core1533.body = wpBodyT ⟨0, 0, 18, 2, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5`. -/
theorem wpBody_L18_L5 : Data.core1556.body = wpBodyT ⟨0, 0, 18, 5, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L2`. -/
theorem wpBody_L24_L2 : Data.core1577.body = wpBodyT ⟨0, 0, 24, 2, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
