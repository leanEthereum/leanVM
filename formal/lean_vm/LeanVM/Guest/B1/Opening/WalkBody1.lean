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
/-- `walk_path__L12_L4`. -/
theorem wpBody_1692 : Data.core1692.body = wpBodyT ⟨0, 0, 12, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6`. -/
theorem wpBody_1719 : Data.core1719.body = wpBodyT ⟨0, 0, 12, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L3`. -/
theorem wpBody_1743 : Data.core1743.body = wpBodyT ⟨0, 0, 18, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6`. -/
theorem wpBody_1763 : Data.core1763.body = wpBodyT ⟨0, 0, 18, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L3`. -/
theorem wpBody_1777 : Data.core1777.body = wpBodyT ⟨0, 0, 24, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L6`. -/
theorem wpBody_1794 : Data.core1794.body = wpBodyT ⟨0, 0, 24, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L6`. -/
theorem wpBody_1800 : Data.core1800.body = wpBodyT ⟨0, 0, 6, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
