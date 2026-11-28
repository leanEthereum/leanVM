module

public import NativeRustcVm.Bus.Blocks
public import NativeRustcVm.Bus.FitsModel

/-!
# The bus's sides fit

The data's blocks of a side have the statement's tuples' monomials (`keys_blocks`), so
`accumulateSide` on a side whose slots are empty, the other sides' slots fitting, fits
(`sideFits_of_empty`), and leaves the side's slots fitting (`fits_accumulateSide`).
-/

namespace NativeRustcVm.Bus

open NativeVm.Model LeanVM.Protocol.Verifier NativeRustcVm.Data

@[expose] public section

/-- Every slot's form fits, but those of the sides `≥ k`, which are empty. -/
def FitsUpTo (F : Array (Array FormW)) (k : Nat) : Prop :=
  Shape F ∧ ∀ o < nTables, ∀ s < 3,
    (s < k → (colsL (slot F o s)).length ≤ formCapW) ∧ (k ≤ s → colsL (slot F o s) = [])

/-- A side's data blocks. -/
def sideBlocks (side : Nat) : List Block :=
  if side = 0 then pushBlocks else if side = 1 then pullBlocks else countBlocks

end

public section

/-! ## The blocks' monomials -/

theorem colsL_ofForm (f : Form) : colsL (FormW.ofForm f) = f.terms.map (·.1) := by
  simp [colsL, FormW.ofForm, Function.comp_def]

/-- **The data's blocks have the statement's tuples' monomials.** -/
theorem keys_blocks (h r : Array Nat) {side : Nat} (hs : side < 3) :
    (sideBlocks side).map (blockKey ∘ blockW h r) = sideTuples side := by
  have hb := busBlocks_eq h r
  rw [← List.map_map]
  obtain rfl | rfl | rfl : side = 0 ∨ side = 1 ∨ side = 2 := by omega
  · have := congrArg (fun p ↦ p.1.toList) hb
    simp only [sideBlocks, ↓reduceIte] at this ⊢
    rw [← this]
    simp only [NativeVm.Model.busBlocks, sideTuples, tablesW, Array.toList_flatMap,
      Array.toList_map, List.map_flatMap, List.flatMap_map, List.map_map, ↓reduceIte]
    congr 1
    funext t
    simp only [TableW.ofTable, Function.comp_def, Array.toList_map, List.map_map]
    simp [blockKey, colsL_ofForm, Function.comp_def]
  · have := congrArg (fun p ↦ p.2.1.toList) hb
    simp only [sideBlocks, show (1 : Nat) ≠ 0 from by decide, ↓reduceIte] at this ⊢
    rw [← this]
    simp only [NativeVm.Model.busBlocks, sideTuples, tablesW, Array.toList_flatMap,
      Array.toList_map, List.map_flatMap, List.flatMap_map, List.map_map, ↓reduceIte]
    congr 1
    funext t
    simp only [TableW.ofTable, Function.comp_def, Array.toList_map, List.map_map]
    simp [blockKey, colsL_ofForm, Function.comp_def]
  · have := congrArg (fun p ↦ p.2.2.toList) hb
    simp only [sideBlocks, show (2 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 1 from by decide,
      ↓reduceIte] at this ⊢
    rw [← this]
    simp only [NativeVm.Model.busBlocks, sideTuples, tablesW, Array.toList_flatMap,
      Array.toList_map, List.map_flatMap, List.flatMap_map, List.map_map]
    congr 1
    funext t
    simp only [TableW.ofTable, Function.comp_def]
    simp [blockKey, colsL_ofForm, Function.comp_def]

/-! ## `accumulateSide`'s forms -/

theorem foldl_fst {α β γ : Type} (f : α → γ → α) (g : α × β → γ → β) (l : List γ) (a : α) (b : β) :
    (l.foldl (fun acc x ↦ (f acc.1 x, g acc x)) (a, b)).1 = l.foldl f a := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => exact ih _ _

theorem accumulateSide_fst (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW)
    (SL : BusLayoutW) (fps w : Array EW) (beta : EW) (point : Array EW) (tree : EW) :
    (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 =
      ((SL.tables.map (eqAbove · point)).toList.zip B.toList).foldl (formsStep side w beta) F := by
  unfold NativeVm.Model.accumulateSide
  simp only
  rw [← Array.foldl_toList, Array.toList_zip]
  exact foldl_fst (β := EW) (formsStep side w beta) _ _ F 0

theorem slotFold_eq (bs : List BusBlockW) (o : Nat) :
    (colsL #[] |> fun L ↦ (bs.filter (·.owner == o)).foldl
      (fun L b ↦ mergeAll L (blockCols (b.coordinates.toList.map colsL))) L) =
      slotCols (bs.map blockKey) o := by
  simp only [slotCols, List.filter_map, List.foldl_map, colsL, List.map_nil]
  rfl

/-- **A side on empty slots fits**, and leaves its slots fitting. -/
theorem fits_accumulateSide {F : Array (Array FormW)} {side : Nat} (hs : side < 3)
    (hF : FitsUpTo F side) (h r : Array Nat) (SL : BusLayoutW) (hSL : (sideBlocks side).length ≤ SL.tables.size)
    (fps w : Array EW) (beta : EW) (point : Array EW) (tree : EW) :
    let B := ((sideBlocks side).map (blockW h r)).toArray
    SideFits F side B SL fps w beta point tree ∧
      FitsUpTo (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 (side + 1) := by
  intro B
  have hkeys := keys_blocks h r hs
  have hBk : B.toList.map blockKey = sideTuples side := by
    simp only [B, List.map_map]; exact hkeys
  have hzip : ((SL.tables.map (eqAbove · point)).toList.zip B.toList).map (·.2) = B.toList :=
    List.map_snd_zip (by simp [B]; exact hSL)
  have hres := accumulateSide_fst F side B SL fps w beta point tree
  have hslot : ∀ o < nTables, ∀ s < 3,
      Shape (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 ∧
      colsL (slot (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 o s) =
        if side = s then slotCols (sideTuples side) o else colsL (slot F o s) := by
    intro o ho s hs'
    rw [hres]
    obtain ⟨h1, h2⟩ := slot_foldl ((SL.tables.map (eqAbove · point)).toList.zip B.toList) hF.1
      side w beta ho hs'
    refine ⟨h1, ?_⟩
    rw [h2, hzip]
    split
    · rename_i he
      subst he
      rw [(hF.2 o ho side hs).2 le_rfl, ← hBk]
      exact slotFold_eq B.toList o
    · rfl
  have hshape : Shape (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 :=
    (hslot 0 (by decide) 0 (by decide)).1
  refine ⟨⟨fun b hb ↦ ?_, fun row hrow f hf ↦ ?_⟩, hshape, fun o ho s hs' ↦ ⟨fun hlt ↦ ?_, fun hle ↦ ?_⟩⟩
  · rw [blockForm_size]
    have hk : blockKey b ∈ sideTuples side := by
      rw [← hBk]; exact List.mem_map_of_mem (Array.mem_toList_iff.mpr hb)
    exact blockCols_le hs hk
  · obtain ⟨o, ho, rfl⟩ := Array.mem_iff_getElem.mp hrow
    obtain ⟨s, hs', rfl⟩ := Array.mem_iff_getElem.mp hf
    have ho6 : o < nTables := hshape.1 ▸ ho
    have hs3 : s < 3 := (hshape.2 _ (Array.getElem_mem ho)) ▸ hs'
    have := (hslot o ho6 s hs3).2
    have hsz : (colsL (slot (NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1 o s)).length =
        ((NativeVm.Model.accumulateSide F side B SL fps w beta point tree).1[o])[s].size := by
      simp [slot, colsL, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ho,
        Array.getElem?_eq_getElem hs']
    rw [← hsz, this]
    split
    · exact slotCols_le hs o
    · rename_i hne
      by_cases hlt : s < side
      · exact (hF.2 o ho6 s hs3).1 hlt
      · rw [(hF.2 o ho6 s hs3).2 (by omega)]; exact Nat.zero_le _
  · rw [(hslot o ho s hs').2]
    split
    · exact slotCols_le hs o
    · exact (hF.2 o ho s hs').1 (by omega)
  · rw [(hslot o ho s hs').2, ite_eq_right_iff.mpr (fun h ↦ absurd h (by omega))]
    exact (hF.2 o ho s hs').2 (by omega)

end

end NativeRustcVm.Bus
