/-
  LeanVM.Guest.Lift.SpWotsLeaf

  `sp_wots`'s body is a leaf body that loads nothing: atoms, branches and arms, placing nothing,
  no load (kernel checks on ranges of its statements, those of its well-formedness check).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

namespace LeanVM.Guest.Lift

open LeanVM.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom that is not a load. -/
def noLoad : Atom → Bool
  | .load .. => false
  | _ => true

set_option maxRecDepth 100000 in
theorem spWotsLeaf_0 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 0).take 84) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_84 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 84).take 11) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_95 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 95).take 11) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_106 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 106).take 83) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`sp_wots`'s body is a leaf loading nothing.** -/
theorem spWots_leafOk : Stmt.leafOkList noLoad (fn% «sp_wots»).body = true := by
  have h189 : Stmt.leafOkList noLoad ((fn% «sp_wots»).body.drop 189) = true :=
    leafOk_end (l := (fn% «sp_wots»).body) (by decide +kernel)
  have h106 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 106) (n := 83) spWotsLeaf_106 h189
  have h95 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 95) (n := 11) spWotsLeaf_95 h106
  have h84 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 84) (n := 11) spWotsLeaf_84 h95
  have h0 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 0) (n := 84) spWotsLeaf_0 h84
  simpa using h0

end
end LeanVM.Guest.Lift
