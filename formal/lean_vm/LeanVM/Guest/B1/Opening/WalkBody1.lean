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
/-- `walk_path__L11_L5`. -/
theorem wpBody_961 : Data.core961.body = wpBodyT ⟨0, 0, 11, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L8`. -/
theorem wpBody_962 : Data.core962.body = wpBodyT ⟨0, 0, 11, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6`. -/
theorem wpBody_963 : Data.core963.body = wpBodyT ⟨0, 0, 12, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5`. -/
theorem wpBody_964 : Data.core964.body = wpBodyT ⟨0, 0, 12, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8`. -/
theorem wpBody_965 : Data.core965.body = wpBodyT ⟨0, 0, 12, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L6`. -/
theorem wpBody_966 : Data.core966.body = wpBodyT ⟨0, 0, 13, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L5`. -/
theorem wpBody_967 : Data.core967.body = wpBodyT ⟨0, 0, 13, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L8`. -/
theorem wpBody_968 : Data.core968.body = wpBodyT ⟨0, 0, 13, 8⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L6`. -/
theorem wpBody_969 : Data.core969.body = wpBodyT ⟨0, 0, 14, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L5`. -/
theorem wpBody_970 : Data.core970.body = wpBodyT ⟨0, 0, 14, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L6`. -/
theorem wpBody_971 : Data.core971.body = wpBodyT ⟨0, 0, 15, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L5`. -/
theorem wpBody_972 : Data.core972.body = wpBodyT ⟨0, 0, 15, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L6`. -/
theorem wpBody_973 : Data.core973.body = wpBodyT ⟨0, 0, 16, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L5`. -/
theorem wpBody_974 : Data.core974.body = wpBodyT ⟨0, 0, 16, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L4`. -/
theorem wpBody_975 : Data.core975.body = wpBodyT ⟨0, 0, 14, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
