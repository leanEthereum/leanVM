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
abbrev vkOutSL : List Stmt := slotLanesT 921 934 935 1 1

/-- The committed outputs' dot product. -/
abbrev vkOutDL : List Stmt := dotLoadsT ((List.range 25).map (slotLaneV 935 1)) (.n 234) 30 1118

theorem vkOut_ker :
    noneIn [.load (.n 931) (.n 929) 0] vkSt = true ∧
    vkOutSL.all isAtom = true ∧
    (resid (atomsL vkOutSL)).all (ldR [(.n 921, 0, 6), (.n 934, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkOutSL)) vkSt = true ∧
    vkOutDL.all isAtom = true ∧
    (resid (atomsL vkOutDL)).all (ldR [(.n 234, 30, 55)]) = true ∧
    noneIn (resid (atomsL vkOutDL)) vkSt = true := by
  decide +kernel

/-- The inputs' pairs: the low point's weights and the last claim's `μ`. -/
abbrev vkInPD : List Stmt := pairsDotT (.n 1210) (.n 161) (consecOffs 14 270 16) 1265

theorem vkIn_ker :
    noneIn [.load (.n 1200) (.n 161) 264] vkSt = true ∧
    noneIn (eqtreeReads (.n 9) (.n 1210) 39 1211 4) vkSt = true ∧
    vkInPD.all isAtom = true ∧
    (resid (atomsL vkInPD)).all (ldR [(.n 1210, 14, 30), (.n 161, 270, 286)]) = true ∧
    noneIn (resid (atomsL vkInPD)) vkSt = true := by
  decide +kernel

/-- A residual atom of the slices: a read at the cursor, or the store of a read. -/
def slRes (a : Atom) : Bool := match a with
  | .load d p off => (p == .n 1338 && decide (off < 64) && !vkSt.contains a) ||
      (p == .n 10 && decide (off < 64) && d == .n (slB 1345 off) && vkSt.contains a)
  | _ => false

theorem vkSlices_ker :
    (slicesT (.n 1338) 1340 1345).all isAtom = true ∧
    (resid (atomsL (slicesT (.n 1338) 1340 1345))).all slRes = true := by
  decide +kernel

/-- The inputs' lane weights. -/
abbrev vkFinSL : List Stmt := slotLanesT 1330 1746 1747 0 2

/-- The shifts of the slices. -/
abbrev vkFinFT : List Stmt := foldT (fun j ↦ 1981 + j) 2045 (.n 1980)

/-- `keccak_form`. -/
abbrev vkFinFA : List Stmt := (formAll (.n 3143) vkSh (slotLaneV 1747 2) 3144).1

theorem vkFin_ker :
    noneIn ([.load (.n 1745) (.n 161) 266, .load (.n 1980) (.n 161) 268,
      .load (.n 3143) (.n 161) 267] ++ (List.range 64).map fun z ↦ .load (.n (1981 + z)) (.n 10) z)
      vkSt = true ∧
    vkFinSL.all isAtom = true ∧
    (resid (atomsL vkFinSL)).all (ldR [(.n 1330, 0, 6), (.n 1746, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkFinSL)) vkSt = true ∧
    vkFinFT.all isAtom = true ∧
    (resid (atomsL vkFinFT)).all (ldR [(.n 1980, 0, 6)]) = true ∧
    noneIn (resid (atomsL vkFinFT)) vkSt = true ∧
    vkFinFA.all isAtom = true ∧
    (resid (atomsL vkFinFA)).all (ldR [(.n 3143, 0, 25)]) = true ∧
    noneIn (resid (atomsL vkFinFA)) vkSt = true ∧
    (formAll (.n 3143) vkSh (slotLaneV 1747 2) 3144).2.2 = 3357 := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
