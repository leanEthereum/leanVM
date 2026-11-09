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
abbrev vkOutSL : List Stmt := slotLanesT 963 983 984 1 1

/-- The committed outputs' dot product. -/
abbrev vkOutDL : List Stmt := dotLoadsT ((List.range 25).map (slotLaneV 984 1)) (.n 276) 30 1167

theorem vkOut_ker :
    noneIn [.load (.n 973) (.n 971) 0] vkSt = true ∧
    vkOutSL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutSL)) = true ∧
    (resid (atomsL vkOutSL)).all (ldR [(.n 963, 0, 6), (.n 983, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkOutSL)) vkSt = true ∧
    vkOutDL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkOutDL)) = true ∧
    (resid (atomsL vkOutDL)).all (ldR [(.n 276, 30, 55)]) = true ∧
    noneIn (resid (atomsL vkOutDL)) vkSt = true := by
  decide +kernel

/-- The inputs' pairs: the low point's weights and the last claim's `μ`. -/
abbrev vkInPD : List Stmt := pairsDotT (.n 1259) (.n 203) (consecOffs 14 270 16) 1314

theorem vkIn_ker :
    noneIn [.load (.n 1249) (.n 203) 264] vkSt = true ∧
    noneIn (eqtreeReads (.n 9) (.n 1259) 39 1260 4) vkSt = true ∧
    vkInPD.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkInPD)) = true ∧
    (resid (atomsL vkInPD)).all (ldR [(.n 1259, 14, 30), (.n 203, 270, 286)]) = true ∧
    noneIn (resid (atomsL vkInPD)) vkSt = true := by
  decide +kernel

/-- The slices but the ring map's first challenge. -/
def slicesPre (cur : V) (capb b : ℕ) : List Stmt :=
  ((List.range 16).map fun g ↦
    (if g = 0 then [] else
      [keccakA (slCells b (g - 1) ++ cap5 (slCap capb b (g - 1)))
        ((List.range 13).map fun k ↦ .n (slP b g + k))]) ++
    ((List.range 4).map fun j ↦
      fsNextT cur (4 * g + j) (slB b (4 * g + j)) ++
        [.atom (.load (.n (slB b (4 * g + j))) (.n 10) (4 * g + j))]).flatten).flatten ++
  [keccakA (slCells b 15 ++ cap5 (slCap capb b 15)) ((List.range 13).map fun k ↦ .n (b + 835 + k))]

theorem slicesT_pre (cur : V) (capb b : ℕ) :
    slicesT cur capb b = slicesPre cur capb b ++ challengeT (.n (b + 835)) (.n (b + 836)) (b + 848) :=
  rfl

/-- The canonical values of the slices' permutations' inputs: the capacity, the reads' cells. -/
def slA : List ℕ :=
  [1389, 1390, 1391, 1392, 1393] ++ (List.range 64).flatMap fun z ↦ [slB 1394 z + 7, slB 1394 z + 9]

/-- A residual atom of the slices: a read at the cursor, or the store of a read. -/
def slRes (a : Atom) : Bool := match a with
  | .load d p off => (p == .n 1387 && decide (off < 64) && !vkSt.contains a) ||
      (p == .n 10 && decide (off < 64) && d == .n (slB 1394 off) && vkSt.contains a)
  | _ => false

theorem vkSlices_ker :
    (slicesPre (.n 1387) 1389 1394).all isAtom = true ∧
    canonChk slA (atomsL ([] ++ slicesPre (.n 1387) 1389 1394)) = true ∧
    (resid (atomsL (slicesPre (.n 1387) 1389 1394))).all slRes = true := by
  decide +kernel

/-- The inputs' lane weights. -/
abbrev vkFinSL : List Stmt := slotLanesT 1379 2250 2251 0 2

/-- The shifts of the slices. -/
abbrev vkFinFT : List Stmt := foldT (fun j ↦ 2485 + j) 2549 (.n 2484)

/-- `keccak_form`. -/
abbrev vkFinFA : List Stmt := (formAll (.n 3647) vkSh (slotLaneV 2251 2) 3648).1

theorem vkFin_ker :
    noneIn ([.load (.n 2249) (.n 203) 266, .load (.n 2484) (.n 203) 268,
      .load (.n 3647) (.n 203) 267] ++ (List.range 64).map fun z ↦ .load (.n (2485 + z)) (.n 10) z)
      vkSt = true ∧
    vkFinSL.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinSL)) = true ∧
    (resid (atomsL vkFinSL)).all (ldR [(.n 1379, 0, 6), (.n 2250, 0, 1)]) = true ∧
    noneIn (resid (atomsL vkFinSL)) vkSt = true ∧
    vkFinFT.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinFT)) = true ∧
    (resid (atomsL vkFinFT)).all (ldR [(.n 2484, 0, 6)]) = true ∧
    noneIn (resid (atomsL vkFinFT)) vkSt = true ∧
    vkFinFA.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFinFA)) = true ∧
    (resid (atomsL vkFinFA)).all (ldR [(.n 3647, 0, 25)]) = true ∧
    noneIn (resid (atomsL vkFinFA)) vkSt = true ∧
    (formAll (.n 3647) vkSh (slotLaneV 2251 2) 3648).2.2 = 3861 := by
  decide +kernel

end
end LeanVM.Guest.B1.VerifySub
