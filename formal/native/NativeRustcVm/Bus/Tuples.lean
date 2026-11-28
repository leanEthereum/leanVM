module

public import NativeRustcVm.Layout.Forms
public import NativeRustcVm.Bus.FitsModel
public import NativeRustcVm.Bus.Blocks

/-!
# `TUPLES` in memory, and a tuple's block form as a fold

`TUPLES` (`Data.tuples`) holds `147` spans of `16` bytes (`tuples_length`, `length_tuples_bytes`),
each inside `FORMS` (`tuples_end_le`); span `tu`'s words are its start and length
(`tuples_words`). `block_form` folds the span's forms one slot at a time (`bf`): the model's
`blockForm` of the tuple is `bf` of the span's length (`blockForm_eq_bf`), and the fold never
shrinks the form (`size_le_bf`).
-/

namespace NativeRustcVm.Bus

open NativeVm.Model NativeRustcVm.Data NativeRustcVm.Layout

@[expose] public section

set_option Elab.async false in
theorem tuples_length : Data.tuples.length = 147 := by decide +kernel

set_option Elab.async false in
/-- Every span of `TUPLES` lies in `FORMS`. -/
theorem tuples_end_le : (Data.tuples.all fun sp ↦ decide (sp.start + sp.len ≤ 593)) = true := by
  decide +kernel

theorem tuple_end_le (tu : Nat) (h : tu < Data.tuples.length) :
    Data.tuples[tu].start + Data.tuples[tu].len ≤ 593 := by
  have := List.all_eq_true.mp tuples_end_le _ (List.getElem_mem h)
  simpa using this

/-- `TUPLES`' bytes: `147` spans of `16` bytes. -/
theorem length_tuples_bytes : (Data.tuples.flatMap Span.bytes).length = 2352 := by
  rw [length_flatMap_const (k := 16) (fun s ↦ by simp [Span.bytes, natBytes, length_wordBytes]),
    tuples_length]

/-- Span `tu`'s words: its start, then its length. -/
theorem tuples_words {d : Mem 64} {a : BitVec 64} (h : BytesAt d a (Data.tuples.flatMap Span.bytes))
    (tu : Nat) (hi : tu < Data.tuples.length) :
    WordAt d (a + BitVec.ofNat 64 (16 * tu)) Data.tuples[tu].start.toUInt64 ∧
      WordAt d (a + BitVec.ofNat 64 (16 * tu) + BitVec.ofNat 64 8) Data.tuples[tu].len.toUInt64 := by
  have hb := h.flatMap_getElem (k := 16) (fun s ↦ by simp [Span.bytes, natBytes, length_wordBytes])
    (i := tu) hi
  simp only [Span.bytes, natBytes] at hb
  exact ⟨by simpa [WordAt] using hb.left, by simpa [WordAt, length_wordBytes] using hb.right⟩

/-- `tupleOf` of a span of `TUPLES`. -/
theorem tupleOf_getElem (tu : Nat) (h : tu < Data.tuples.length) :
    tupleOf tu = ((List.range Data.tuples[tu].len).map fun i ↦
      formAt (Data.tuples[tu].start + i)).toArray := by
  rw [tupleOf, List.getElem?_eq_getElem h]

set_option Elab.async false in
/-- Every form of the data has a term. -/
theorem allForms_pos : (Data.allForms.all fun f ↦ decide (0 < f.terms.length)) = true := by
  decide +kernel

/-- A form of the data's span has a term. -/
theorem size_formAt_pos {i : Nat} (h : i < 593) : 0 < (formAt i).size := by
  have hi : i < Data.allForms.length := by rw [allForms_length]; exact h
  have := List.all_eq_true.mp allForms_pos _ (List.getElem_mem hi)
  simp only [decide_eq_true_eq] at this
  simpa [formAt, List.getElem?_eq_getElem hi, FormW.ofForm] using this

/-! ## The block form, slot by slot -/

/-- The block form after `j` slots of the span `s`, `len`: the constant, then each slot's form
scaled by its weight. -/
def bf (s : Nat) (w : Array EW) (beta : EW) (j : Nat) : FormW :=
  (List.range j).foldl (fun g i ↦ g.addScaled (formAt (s + i)) (w.getD i 0)) (FormW.const beta)

theorem bf_succ (s : Nat) (w : Array EW) (beta : EW) (j : Nat) :
    bf s w beta (j + 1) = (bf s w beta j).addScaled (formAt (s + j)) (w.getD j 0) := by
  simp [bf, List.range_succ, List.foldl_append]

theorem bf_zero (s : Nat) (w : Array EW) (beta : EW) : bf s w beta 0 = FormW.const beta := rfl

theorem foldl_zipIdx_range' {γ : Type} (F : Nat → FormW) (g : γ → FormW × Nat → γ) :
    ∀ (n k : Nat) (init : γ), (((List.range' k n).map F).zipIdx k).foldl g init =
      (List.range' k n).foldl (fun acc i ↦ g acc (F i, i)) init
  | 0, _, _ => rfl
  | n + 1, k, init => by
    simp only [List.range'_succ, List.map_cons, List.zipIdx_cons, List.foldl_cons]
    exact foldl_zipIdx_range' F g n (k + 1) _

/-- **The tuple's block form** is the fold over its span. -/
theorem blockForm_eq_bf (tu : Nat) (h : tu < Data.tuples.length) (w : Array EW) (beta : EW) :
    NativeVm.Model.blockForm ⟨0, 0, tupleOf tu, 0⟩ w beta =
      bf Data.tuples[tu].start w beta Data.tuples[tu].len := by
  unfold NativeVm.Model.blockForm bf
  rw [tupleOf_getElem tu h, ← Array.foldl_toList, Array.toList_zipIdx, List.range_eq_range',
    foldl_zipIdx_range']

theorem size_le_addScaled (f other : FormW) (w : EW) : f.size ≤ (f.addScaled other w).size := by
  have h1 : (f.addScaled other w).size = (colsL (f.addScaled other w)).length := by simp [colsL]
  have h2 : f.size = (colsL f).length := by simp [colsL]
  rw [h1, h2, colsL_addScaled]
  generalize colsL f = L
  generalize colsL other = M
  induction M generalizing L with
  | nil => exact Nat.le_refl _
  | cons x M ih =>
    refine Nat.le_trans ?_ (ih (mergeOne L x))
    unfold mergeOne; split <;> simp

/-- The fold never shrinks the form. -/
theorem size_le_bf (s : Nat) (w : Array EW) (beta : EW) {j l : Nat} (h : j ≤ l) :
    (bf s w beta j).size ≤ (bf s w beta l).size := by
  induction l with
  | zero => rw [Nat.le_zero.mp h]
  | succ l ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [bf_succ]
      exact Nat.le_trans (ih (by omega)) (size_le_addScaled _ _ _)
    · rw [h]

end

end NativeRustcVm.Bus
