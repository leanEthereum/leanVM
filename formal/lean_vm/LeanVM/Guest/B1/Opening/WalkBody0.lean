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
theorem wpBody_1749 : Data.core1749.body = wpBodyT ⟨0, 0, 6, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L7`. -/
theorem wpBody_1748 : Data.core1748.body = wpBodyT ⟨0, 0, 6, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L2`. -/
theorem wpBody_1747 : Data.core1747.body = wpBodyT ⟨0, 0, 12, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L3`. -/
theorem wpBody_1642 : Data.core1642.body = wpBodyT ⟨0, 0, 12, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4`. -/
theorem wpBody_1662 : Data.core1662.body = wpBodyT ⟨0, 0, 12, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5`. -/
theorem wpBody_1645 : Data.core1645.body = wpBodyT ⟨0, 0, 12, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6`. -/
theorem wpBody_1665 : Data.core1665.body = wpBodyT ⟨0, 0, 12, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
