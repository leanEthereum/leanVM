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
/-- `walk_path__L12_L7`. -/
theorem wpBody_1674 : Data.core1674.body = wpBodyT ⟨0, 0, 12, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8`. -/
theorem wpBody_1750 : Data.core1750.body = wpBodyT ⟨0, 0, 12, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L2`. -/
theorem wpBody_1683 : Data.core1683.body = wpBodyT ⟨0, 0, 18, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L3`. -/
theorem wpBody_1692 : Data.core1692.body = wpBodyT ⟨0, 0, 18, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4`. -/
theorem wpBody_1700 : Data.core1700.body = wpBodyT ⟨0, 0, 18, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5`. -/
theorem wpBody_1706 : Data.core1706.body = wpBodyT ⟨0, 0, 18, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6`. -/
theorem wpBody_1712 : Data.core1712.body = wpBodyT ⟨0, 0, 18, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
