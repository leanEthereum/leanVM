module

public import NativeRustcVm.Bus.Fits

/-!
# The forms' monomials through the model

`colsL` of the model's form operations: `addTerm` (`colsL_addTerm`), `addScaled`
(`colsL_addScaled`), `blockForm` (`colsL_blockForm`, `blockCols` of its coordinates'). A table's
slot of the forms (`slot F o s`) after `accumulateSide`: unchanged off the side, the side's blocks
of the table merged in on it (`slot_accumulateSide`).
-/

namespace NativeRustcVm.Bus

open NativeVm.Model LeanVM.Protocol.Verifier

@[expose] public section

/-- Table `o`'s form of side `s`. -/
def slot (F : Array (Array FormW)) (o s : Nat) : FormW := (F.getD o #[]).getD s #[]

/-- A side's forms fit their `FormBuf`s (at most `148` terms): each block's form, and every form
after the side. -/
def SideFits (F : Array (Array FormW)) (side : Nat) (B : Array BusBlockW) (SL : BusLayoutW)
    (fps w : Array EW) (beta : EW) (point : Array EW) (tree : EW) : Prop :=
  (∀ b ∈ B, (NativeVm.Model.blockForm b w beta).size ≤ formCapW) ∧
    ∀ row ∈ (accumulateSide F side B SL fps w beta point tree).1, ∀ f ∈ row, f.size ≤ formCapW

/-- The tables' forms' shape: `6` tables, `3` sides each. -/
def Shape (F : Array (Array FormW)) : Prop := F.size = nTables ∧ ∀ row ∈ F, row.size = 3

/-- A block's owner and its coordinates' monomials. -/
def blockKey (b : BusBlockW) : Nat × List (List (List Nat)) :=
  (b.owner, b.coordinates.toList.map colsL)

end
public section

/-! ## Forms -/

theorem colsL_push (f : FormW) (t : TermW) : colsL (f.push t) = colsL f ++ [t.cols.toList] := by
  simp [colsL]

theorem mem_colsL {f : FormW} {m : List Nat} : m ∈ colsL f ↔ ∃ t ∈ f, t.cols.toList = m := by
  simp [colsL]

theorem colsL_addTerm (f : FormW) (m : Array Nat) (c : EW) :
    colsL (f.addTerm m c) = mergeOne (colsL f) m.toList := by
  unfold FormW.addTerm mergeOne
  cases h : f.findIdx? (·.cols == m) with
  | none =>
    rw [Array.findIdx?_eq_none_iff] at h
    have hn : m.toList ∉ colsL f := by
      rw [mem_colsL]
      rintro ⟨t, ht, he⟩
      have := h t ht
      rw [show t.cols = m from Array.toList_inj.mp he] at this
      simp at this
    simp only [hn, ↓reduceIte, colsL_push]
  | some i =>
    obtain ⟨hi, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
    have hm : m.toList ∈ colsL f := by
      rw [mem_colsL]
      exact ⟨f[i], Array.getElem_mem hi, by rw [beq_iff_eq.mp hp]⟩
    simp only [hm, ↓reduceIte]
    simp only [colsL, Array.toList_modify]
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_modify]
    split <;> rfl

theorem colsL_addScaled (f other : FormW) (w : EW) :
    colsL (f.addScaled other w) = mergeAll (colsL f) (colsL other) := by
  unfold FormW.addScaled mergeAll colsL
  rw [← Array.foldl_toList, List.foldl_map]
  generalize other.toList = l
  induction l generalizing f with
  | nil => rfl
  | cons t l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    exact colsL_addTerm f t.cols _

theorem colsL_const (v : EW) : colsL (FormW.const v) = [[]] := rfl

theorem colsL_blockForm (b : BusBlockW) (w : Array EW) (beta : EW) :
    colsL (NativeVm.Model.blockForm b w beta) = blockCols (b.coordinates.toList.map colsL) := by
  unfold NativeVm.Model.blockForm blockCols
  rw [← Array.foldl_toList, Array.toList_zipIdx, ← colsL_const beta]
  generalize FormW.const beta = f0
  generalize b.coordinates.toList = l
  suffices ∀ k f0, colsL (List.foldl (fun form (x : FormW × Nat) ↦ form.addScaled x.1
      (w.getD x.2 0)) f0 (l.zipIdx k)) = (l.map colsL).foldl mergeAll (colsL f0) from this 0 f0
  induction l with
  | nil => intro k f0; rfl
  | cons c l ih =>
    intro k f0
    simp only [List.zipIdx_cons, List.foldl_cons, List.map_cons]
    rw [ih, colsL_addScaled]

theorem blockForm_size (b : BusBlockW) (w : Array EW) (beta : EW) :
    (NativeVm.Model.blockForm b w beta).size =
      (blockCols (b.coordinates.toList.map colsL)).length := by
  rw [← colsL_blockForm b w beta]
  simp [colsL]

/-! ## A side's fold -/

/-- One step of `accumulateSide`'s fold on the forms. -/
@[expose] def formsStep (side : Nat) (w : Array EW) (beta : EW) (F : Array (Array FormW))
    (x : EW × BusBlockW) : Array (Array FormW) :=
  F.modify x.2.owner fun row ↦ row.modify side fun f ↦
    f.addScaled (NativeVm.Model.blockForm x.2 w beta) x.1

theorem shape_formsStep {F : Array (Array FormW)} (h : Shape F) (side : Nat) (w : Array EW)
    (beta : EW) (x : EW × BusBlockW) : Shape (formsStep side w beta F x) := by
  refine ⟨by simp [formsStep, h.1], fun row hr ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  simp only [formsStep, Array.getElem_modify]
  split
  · simp only [Array.size_modify]
    exact h.2 _ (Array.getElem_mem _)
  · exact h.2 _ (Array.getElem_mem _)

theorem slot_formsStep {F : Array (Array FormW)} (h : Shape F) (side : Nat) (w : Array EW)
    (beta : EW) (x : EW × BusBlockW) {o s : Nat} (ho : o < nTables) (hs : s < 3) :
    colsL (slot (formsStep side w beta F x) o s) =
      if x.2.owner = o ∧ side = s then
        mergeAll (colsL (slot F o s)) (blockCols (x.2.coordinates.toList.map colsL))
      else colsL (slot F o s) := by
  have hoF : o < F.size := h.1 ▸ ho
  have hrow : F[o].size = 3 := h.2 _ (Array.getElem_mem hoF)
  simp only [slot, formsStep, Array.getD_eq_getD_getElem?, Array.getElem?_modify,
    Array.getElem?_eq_getElem hoF, Array.getElem?_eq_getElem (show s < F[o].size by omega),
    Option.getD_some]
  by_cases h1 : x.2.owner = o
  · simp only [h1, ↓reduceIte, Option.map_some, Option.getD_some, Array.getElem?_modify,
      Array.getElem?_eq_getElem (show s < F[o].size by omega), true_and]
    by_cases h2 : side = s
    · simp only [h2, ↓reduceIte, Option.getD_some, colsL_addScaled, colsL_blockForm]
    · simp only [h2, ↓reduceIte, Option.getD_some]
  · simp only [h1, ↓reduceIte, false_and, Option.getD_some,
      Array.getElem?_eq_getElem (show s < F[o].size by omega)]

/-- The forms after a side's blocks, table `o`'s slot `s`: the side's blocks of the table merged
in. -/
theorem slot_foldl (l : List (EW × BusBlockW)) {F : Array (Array FormW)} (h : Shape F)
    (side : Nat) (w : Array EW) (beta : EW) {o s : Nat} (ho : o < nTables) (hs : s < 3) :
    Shape (l.foldl (formsStep side w beta) F) ∧
      colsL (slot (l.foldl (formsStep side w beta) F) o s) =
        if side = s then
          ((l.map (·.2)).filter (·.owner == o)).foldl
            (fun L b ↦ mergeAll L (blockCols (b.coordinates.toList.map colsL))) (colsL (slot F o s))
        else colsL (slot F o s) := by
  induction l generalizing F with
  | nil => exact ⟨h, by split <;> rfl⟩
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih (shape_formsStep h side w beta x)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, slot_formsStep h side w beta x ho hs]
    by_cases hside : side = s
    · simp only [hside, and_true, ↓reduceIte, List.map_cons, List.filter_cons, beq_iff_eq]
      by_cases hx : x.2.owner = o
      · simp [hx]
      · simp [hx]
    · simp [hside]

end

end NativeRustcVm.Bus
