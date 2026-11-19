module

public import NativeVm.Code.Phase3.FormsModel

/-!
# The bus forms of a side: `sideFold` a block at a time

`sideFold` is a fold of `sfStep` over the blocks with their selectors and padding weights
(`sideFold_eq`); `accI i` is the fold over the first `i` (`accI_succ`, `accI_all`). A step changes
only the owner's form on the side (`sfStep_getD`) and keeps the forms' shape (`FormsOk`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model

/-- `sideFold`'s step. -/
def sfStep (side : Nat) (ws : Array EW) (β : EW) (acc : Array (Array FormW) × EW)
    (x : (EW × EW) × BusBlockW) : Array (Array FormW) × EW :=
  (acc.1.modify x.2.owner fun row ↦ row.modify side fun f ↦ f.addScaled (blockForm x.2 ws β) x.1.1,
    acc.2 + x.1.1 * x.1.2 *
      ((blockForm x.2 ws β).evaluate (tablesW.getD x.2.owner default).padding + 1))

theorem sideFold_eq (forms : Array (Array FormW)) (side : Nat) (blocks : Array BusBlockW)
    (sels pws ws : Array EW) (β : EW) :
    sideFold forms side blocks sels pws ws β =
      ((sels.zip pws).zip blocks).toList.foldl (sfStep side ws β) (forms, 0) := by
  unfold sideFold
  rw [← Array.foldl_toList]
  rfl

/-- The fold over the first `i` blocks. -/
def accI (forms : Array (Array FormW)) (side : Nat) (blocks : Array BusBlockW) (sels pws ws : Array EW)
    (β : EW) (i : Nat) : Array (Array FormW) × EW :=
  (((sels.zip pws).zip blocks).toList.take i).foldl (sfStep side ws β) (forms, 0)

variable {forms : Array (Array FormW)} {side : Nat} {blocks : Array BusBlockW} {sels pws ws : Array EW}
  {β : EW}

theorem accI_zero : accI forms side blocks sels pws ws β 0 = (forms, 0) := rfl

theorem accI_succ {i : Nat} (hs : sels.size = blocks.size) (hp : pws.size = blocks.size)
    (hi : i < blocks.size) :
    accI forms side blocks sels pws ws β (i + 1) =
      sfStep side ws β (accI forms side blocks sels pws ws β i)
        ((sels[i]'(by omega), pws[i]'(by omega)), blocks[i]) := by
  have hl : i < ((sels.zip pws).zip blocks).toList.length := by simp; omega
  rw [accI, accI, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some,
    List.foldl_append]
  simp

theorem accI_all (hs : sels.size = blocks.size) (hp : pws.size = blocks.size) :
    accI forms side blocks sels pws ws β blocks.size = sideFold forms side blocks sels pws ws β := by
  rw [sideFold_eq, accI, List.take_of_length_le (by simp [hs, hp])]

theorem getD_modify {α : Type} (A : Array α) {o t : Nat} (f : α → α) (d : α) (ho : o < A.size) :
    (A.modify o f).getD t d = if o = t then f (A.getD t d) else A.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?]
  split
  · subst t; rw [Array.getElem?_eq_getElem ho]; rfl
  · rfl

/-- The forms' shape: six tables, three sides each. -/
def FormsOk (A : Array (Array FormW)) : Prop := A.size = nTables ∧ ∀ t < nTables, (A.getD t #[]).size = 3

/-- A step: the owner's form on the side gets the block's form; the rest is kept. -/
theorem sfStep_getD {acc : Array (Array FormW) × EW} {x : (EW × EW) × BusBlockW}
    (hA : FormsOk acc.1) (ho : x.2.owner < nTables) (hside : side < 3) {t s' : Nat} :
    (((sfStep side ws β acc x).1).getD t #[]).getD s' #[] =
      if x.2.owner = t ∧ s' = side then ((acc.1.getD t #[]).getD s' #[]).addScaled
        (blockForm x.2 ws β) x.1.1 else (acc.1.getD t #[]).getD s' #[] := by
  unfold sfStep
  simp only
  rw [getD_modify _ _ _ (by rw [hA.1]; exact ho)]
  by_cases h : x.2.owner = t
  · subst t
    rw [iteT rfl, getD_modify _ _ _ (by rw [hA.2 _ ho]; omega)]
    by_cases h' : s' = side
    · subst s'; rw [iteT rfl, iteT ⟨rfl, rfl⟩]
    · rw [iteF (Ne.symm h'), iteF (fun e ↦ h' e.2)]
  · rw [iteF h, iteF (fun e ↦ h e.1)]

theorem sfStep_ok {acc : Array (Array FormW) × EW} {x : (EW × EW) × BusBlockW}
    (hA : FormsOk acc.1) (ho : x.2.owner < nTables) : FormsOk (sfStep side ws β acc x).1 := by
  refine ⟨by unfold sfStep; rw [Array.size_modify]; exact hA.1, fun t ht ↦ ?_⟩
  unfold sfStep
  simp only
  rw [getD_modify _ _ _ (by rw [hA.1]; exact ho)]
  split
  · rw [Array.size_modify]; exact hA.2 t ht
  · exact hA.2 t ht

theorem sfStep_snd (acc : Array (Array FormW) × EW) (x : (EW × EW) × BusBlockW) :
    (sfStep side ws β acc x).2 = acc.2 + x.1.1 * x.1.2 *
      ((blockForm x.2 ws β).evaluate (tablesW.getD x.2.owner default).padding + 1) := rfl

end NativeVm.Code.P3
