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
/-- `walk_path__L18_L7`. -/
theorem wpBody_1718 : Data.core1514.body = wpBodyT ⟨0, 0, 18, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L2`. -/
theorem wpBody_1724 : Data.core1520.body = wpBodyT ⟨0, 0, 24, 2⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L3`. -/
theorem wpBody_1726 : Data.core1522.body = wpBodyT ⟨0, 0, 24, 3⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L4`. -/
theorem wpBody_1731 : Data.core1527.body = wpBodyT ⟨0, 0, 24, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
