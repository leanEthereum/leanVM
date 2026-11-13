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
/-- `walk_path__L6_L7`. -/
theorem wpBody_L6_L7 : (fn% «walk_path__L6_L7»).body = wpBodyT ⟨0, 0, 6, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4`. -/
theorem wpBody_L12_L4 : (fn% «walk_path__L12_L4»).body = wpBodyT ⟨0, 0, 12, 4, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7`. -/
theorem wpBody_L12_L7 : (fn% «walk_path__L12_L7»).body = wpBodyT ⟨0, 0, 12, 7, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L3`. -/
theorem wpBody_L18_L3 : (fn% «walk_path__L18_L3»).body = wpBodyT ⟨0, 0, 18, 3, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6`. -/
theorem wpBody_L18_L6 : (fn% «walk_path__L18_L6»).body = wpBodyT ⟨0, 0, 18, 6, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L3`. -/
theorem wpBody_L24_L3 : (fn% «walk_path__L24_L3»).body = wpBodyT ⟨0, 0, 24, 3, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
