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
/-- `walk_path__L12_L3`. -/
theorem wpBody_1707 : Data.core1707.body = wpBodyT ⟨0, 0, 12, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7`. -/
theorem wpBody_1728 : Data.core1728.body = wpBodyT ⟨0, 0, 12, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4`. -/
theorem wpBody_1751 : Data.core1751.body = wpBodyT ⟨0, 0, 18, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7`. -/
theorem wpBody_1769 : Data.core1769.body = wpBodyT ⟨0, 0, 18, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L4`. -/
theorem wpBody_1782 : Data.core1782.body = wpBodyT ⟨0, 0, 24, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L7`. -/
theorem wpBody_1798 : Data.core1798.body = wpBodyT ⟨0, 0, 6, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8`. -/
theorem wpBody_1801 : Data.core1801.body = wpBodyT ⟨0, 0, 12, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
