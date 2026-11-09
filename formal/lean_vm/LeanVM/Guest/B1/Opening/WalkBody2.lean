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
/-- `walk_path__L11_L7`. -/
theorem wpBody_976 : Data.core976.body = wpBodyT ⟨0, 0, 11, 7⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4`. -/
theorem wpBody_977 : Data.core977.body = wpBodyT ⟨0, 0, 12, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L4`. -/
theorem wpBody_978 : Data.core978.body = wpBodyT ⟨0, 0, 13, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L4`. -/
theorem wpBody_979 : Data.core979.body = wpBodyT ⟨0, 0, 15, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L6`. -/
theorem wpBody_980 : Data.core980.body = wpBodyT ⟨0, 0, 17, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L5`. -/
theorem wpBody_981 : Data.core981.body = wpBodyT ⟨0, 0, 17, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L4`. -/
theorem wpBody_982 : Data.core982.body = wpBodyT ⟨0, 0, 16, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6`. -/
theorem wpBody_983 : Data.core983.body = wpBodyT ⟨0, 0, 18, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5`. -/
theorem wpBody_984 : Data.core984.body = wpBodyT ⟨0, 0, 18, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L4`. -/
theorem wpBody_985 : Data.core985.body = wpBodyT ⟨0, 0, 17, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L6`. -/
theorem wpBody_986 : Data.core986.body = wpBodyT ⟨0, 0, 19, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L5`. -/
theorem wpBody_987 : Data.core987.body = wpBodyT ⟨0, 0, 19, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L6`. -/
theorem wpBody_988 : Data.core988.body = wpBodyT ⟨0, 0, 20, 6⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L5`. -/
theorem wpBody_989 : Data.core989.body = wpBodyT ⟨0, 0, 20, 5⟩ :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4`. -/
theorem wpBody_990 : Data.core990.body = wpBodyT ⟨0, 0, 18, 4⟩ :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
