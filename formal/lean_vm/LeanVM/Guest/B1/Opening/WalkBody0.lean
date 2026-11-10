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
/-- `walk_path__L6_L8`. -/
theorem wpBody_1689 : Data.core1689.body = wpBodyT ⟨0, 0, 6, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5`. -/
theorem wpBody_1710 : Data.core1710.body = wpBodyT ⟨0, 0, 12, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L2`. -/
theorem wpBody_1737 : Data.core1737.body = wpBodyT ⟨0, 0, 18, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5`. -/
theorem wpBody_1757 : Data.core1757.body = wpBodyT ⟨0, 0, 18, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L2`. -/
theorem wpBody_1775 : Data.core1775.body = wpBodyT ⟨0, 0, 24, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L5`. -/
theorem wpBody_1789 : Data.core1789.body = wpBodyT ⟨0, 0, 24, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L2`. -/
theorem wpBody_1799 : Data.core1799.body = wpBodyT ⟨0, 0, 12, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L8`. -/
theorem wpBody_1802 : Data.core1802.body = wpBodyT ⟨0, 0, 18, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
