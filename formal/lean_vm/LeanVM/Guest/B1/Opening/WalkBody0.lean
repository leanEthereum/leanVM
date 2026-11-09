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
/-- `walk_path__L14_L8`. -/
theorem wpBody_878 : Data.core878.body = wpBodyT ⟨0, 0, 14, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L8`. -/
theorem wpBody_885 : Data.core885.body = wpBodyT ⟨0, 0, 15, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7`. -/
theorem wpBody_919 : Data.core919.body = wpBodyT ⟨0, 0, 12, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L7`. -/
theorem wpBody_921 : Data.core921.body = wpBodyT ⟨0, 0, 13, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L7`. -/
theorem wpBody_923 : Data.core923.body = wpBodyT ⟨0, 0, 14, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L7`. -/
theorem wpBody_925 : Data.core925.body = wpBodyT ⟨0, 0, 15, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L7`. -/
theorem wpBody_927 : Data.core927.body = wpBodyT ⟨0, 0, 16, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L7`. -/
theorem wpBody_929 : Data.core929.body = wpBodyT ⟨0, 0, 17, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7`. -/
theorem wpBody_932 : Data.core932.body = wpBodyT ⟨0, 0, 18, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L8`. -/
theorem wpBody_955 : Data.core955.body = wpBodyT ⟨0, 0, 9, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L6`. -/
theorem wpBody_956 : Data.core956.body = wpBodyT ⟨0, 0, 10, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L5`. -/
theorem wpBody_957 : Data.core957.body = wpBodyT ⟨0, 0, 10, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L5`. -/
theorem wpBody_958 : Data.core958.body = wpBodyT ⟨0, 0, 9, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L8`. -/
theorem wpBody_959 : Data.core959.body = wpBodyT ⟨0, 0, 10, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L6`. -/
theorem wpBody_960 : Data.core960.body = wpBodyT ⟨0, 0, 11, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
