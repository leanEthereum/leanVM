/-
  LeanVM.Guest.Lift.SpWotsLeaf

  `sp_wots`'s body is a leaf body that loads nothing: atoms, branches and arms, placing nothing,
  no load (kernel checks on ranges of its statements, those of its well-formedness check).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom that is not a load. -/
def noLoad : Atom → Bool
  | .load .. => false
  | _ => true

set_option maxRecDepth 100000 in
theorem spWotsLeaf_0 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 0).take 60) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_60 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 60).take 50) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spWotsLeaf_110 : Stmt.leafOkList noLoad (((fn% «sp_wots»).body.drop 110).take 100) = true
    := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`sp_wots`'s body is a leaf loading nothing.** -/
theorem spWots_leafOk : Stmt.leafOkList noLoad (fn% «sp_wots»).body = true := by
  have h210 : Stmt.leafOkList noLoad ((fn% «sp_wots»).body.drop 210) = true :=
    leafOk_end (l := (fn% «sp_wots»).body) (by decide +kernel)
  have h110 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 110) (n := 100) spWotsLeaf_110 h210
  have h60 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 60) (n := 50) spWotsLeaf_60 h110
  have h0 := leafOk_drop (l := (fn% «sp_wots»).body) (a := 0) (n := 60) spWotsLeaf_0 h60
  simpa using h0

end
end LeanVM.Guest.Lift
