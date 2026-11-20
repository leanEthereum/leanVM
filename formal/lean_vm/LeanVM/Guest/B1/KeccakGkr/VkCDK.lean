/-
  LeanVM.Guest.B1.KeccakGkr.VkCDK

  What the kernel checks of `verify_keccak`'s openings.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK

/-!
# The openings' blocks

`vkOutKer`: of the committed outputs' opening, the loads that are not stores and the residual
loads' pointers of its lane weights (`vkOutSL`) and their dot product (`vkOutDL`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The committed outputs' lane weights. -/
abbrev vkOutSL : List Stmt := slotLanesT 916 929 930 1 1

/-- The committed outputs' dot product. -/
abbrev vkOutDL : List Stmt := dotLoadsT ((List.range 25).map (slotLaneV 930 1)) (.n 229) 30 1113

theorem vkOut_ker :
    noneIn [.load (.n 926) (.n 924) 0] vkSt = true ∧
    vkOutSL.all isAtom = true ∧
    (resid (atomsL vkOutSL)).all (ldR [(.n 916, 0, 6), (.n 929, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkOutSL)) vkSt = true ∧
    vkOutDL.all isAtom = true ∧
    (resid (atomsL vkOutDL)).all (ldR [(.n 229, 30, 55)]) = true ∧
    noneIn (resid (atomsL vkOutDL)) vkSt = true := by
  decide +kernel

/-- The inputs' pairs: the low point's weights and the last claim's `μ`. -/
abbrev vkInPD : List Stmt := pairsDotT (.n 1205) (.n 156) (consecOffs 14 270 16) 1260

theorem vkIn_ker :
    noneIn [.load (.n 1195) (.n 156) 264] vkSt = true ∧
    noneIn (eqtreeReads (.n 9) (.n 1205) 39 1206 4) vkSt = true ∧
    vkInPD.all isAtom = true ∧
    (resid (atomsL vkInPD)).all (ldR [(.n 1205, 14, 30), (.n 156, 270, 286)]) = true ∧
    noneIn (resid (atomsL vkInPD)) vkSt = true := by
  decide +kernel

/-- A residual atom of the slices: a read at the cursor, or the store of a read. -/
def slRes (a : Atom) : Bool := match a with
  | .load d p off => (p == .n 1333 && decide (off < 64) && !vkSt.contains a) ||
      (p == .n 10 && decide (off < 64) && d == .n (slB 1340 off) && vkSt.contains a)
  | _ => false

theorem vkSlices_ker :
    (slicesT (.n 1333) 1335 1340).all isAtom = true ∧
    (resid (atomsL (slicesT (.n 1333) 1335 1340))).all slRes = true := by
  decide +kernel

/-- The inputs' lane weights. -/
abbrev vkFinSL : List Stmt := slotLanesT 1325 1741 1742 0 2

/-- The shifts of the slices. -/
abbrev vkFinFT : List Stmt := foldT (fun j ↦ 1976 + j) 2040 (.n 1975)

/-- `keccak_form`. -/
abbrev vkFinFA : List Stmt := (formAll (.n 3138) vkSh (slotLaneV 1742 2) 3139).1

theorem vkFin_ker :
    noneIn ([.load (.n 1740) (.n 156) 266, .load (.n 1975) (.n 156) 268,
      .load (.n 3138) (.n 156) 267] ++ (List.range 64).map fun z ↦ .load (.n (1976 + z)) (.n 10) z)
      vkSt = true ∧
    vkFinSL.all isAtom = true ∧
    (resid (atomsL vkFinSL)).all (ldR [(.n 1325, 0, 6), (.n 1741, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkFinSL)) vkSt = true ∧
    vkFinFT.all isAtom = true ∧
    (resid (atomsL vkFinFT)).all (ldR [(.n 1975, 0, 6)]) = true ∧
    noneIn (resid (atomsL vkFinFT)) vkSt = true ∧
    vkFinFA.all isAtom = true ∧
    (resid (atomsL vkFinFA)).all (ldR [(.n 3138, 0, 25)]) = true ∧
    noneIn (resid (atomsL vkFinFA)) vkSt = true ∧
    (formAll (.n 3138) vkSh (slotLaneV 1742 2) 3139).2.2 = 3352 := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
