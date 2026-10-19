/-
  LeanVM.Guest.B1.Tables.VerifyTablesSegs

  A side's blocks owned by one table are a contiguous run of the side: the sum over the side,
  filtered by owner, is the sum over the table's own flushes.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesForms
public import LeanVM.Guest.B1.Tables.VerifyTablesSpec

/-!
# A table's run of blocks

`vt_side_sum`: over a side whose owners are a run per table (`O`, the runs starting at `st`) and
whose coordinates are the tables' lists `fl`, the selector-weighted sum of the blocks a table owns
is the sum over that table's list, weighted by the selectors of its run.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_sumE_zero {α : Type} (l : List α) : sumE (l.map fun _ => (0 : E)) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, vt_sumE_cons, ih, add_zero]

theorem vt_zip_map_range {α β γ : Type} (l1 : List α) (l2 : List β) (d1 : α) (d2 : β)
    (f : α × β → γ) {n : ℕ} (h1 : l1.length = n) (h2 : l2.length = n) :
    (List.zip l1 l2).map f = (List.range n).map fun j => f (l1.getD j d1, l2.getD j d2) := by
  apply List.ext_getElem (by simp [h1, h2])
  intro j hj1 hj2
  simp only [List.length_map, List.length_range] at hj2
  simp only [List.getElem_map, List.getElem_zip, List.getElem_range,
    List.getD_eq_getElem _ _ (show j < l1.length by omega),
    List.getD_eq_getElem _ _ (show j < l2.length by omega)]

/-- The sum over a run `[a, a + c)` of the indices where `O` is `t`. -/
theorem vt_seg_sum (O : List ℕ) (F : ℕ → E) {t a c n : ℕ} (hac : a + c ≤ n)
    (hO : ∀ j < n, (O.getD j 0 = t ↔ a ≤ j ∧ j < a + c)) :
    sumE ((List.range n).map fun j => if O.getD j 0 = t then F j else 0) =
      sumE ((List.range c).map fun k => F (a + k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = a + c + m := ⟨n - (a + c), by omega⟩
  rw [List.range_add, List.range_add]
  simp only [List.map_append, List.map_map, vt_sumE_append]
  have h1 : ((List.range a).map fun j => if O.getD j 0 = t then F j else 0) =
      (List.range a).map fun _ => (0 : E) := List.map_congr_left fun j hj => by
    have := List.mem_range.mp hj
    rw [ite_neg' (fun h => by have := (hO j (by omega)).mp h; omega)]
  have h2 : ((List.range c).map ((fun j => if O.getD j 0 = t then F j else 0) ∘ (a + ·))) =
      (List.range c).map fun k => F (a + k) := List.map_congr_left fun k hk => by
    have := List.mem_range.mp hk
    simp only [Function.comp_apply]
    rw [ite_pos' ((hO (a + k) (by omega)).mpr (by omega))]
  have h3 : ((List.range m).map ((fun j => if O.getD j 0 = t then F j else 0) ∘
      ((a + c) + ·))) = (List.range m).map fun _ => (0 : E) := List.map_congr_left fun j hj => by
    have := List.mem_range.mp hj
    simp only [Function.comp_apply]
    rw [ite_neg' (fun h => by have := (hO (a + c + j) (by omega)).mp h; omega)]
  rw [h1, h2, h3, vt_sumE_zero, vt_sumE_zero, zero_add, add_zero]

theorem vt_flatMap_getD {α β : Type} [Inhabited α] (f : α → List β) (d : β) :
    ∀ (L : List α) (t k : ℕ), t < L.length → k < (f (L.getD t default)).length →
      (L.flatMap f).getD (((L.take t).map fun x => (f x).length).sum + k) d =
        (f (L.getD t default)).getD k d
  | [], _, _, h, _ => absurd h (by simp)
  | x :: L, 0, k, _, hk => by
    simp only [List.getD_cons_zero] at hk ⊢
    simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatMap_cons,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  | x :: L, t + 1, k, ht, hk => by
    simp only [List.getD_cons_succ, List.length_cons] at hk ht ⊢
    have ih := vt_flatMap_getD f d L t k (by omega) hk
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons]
    rw [List.getD_eq_getElem?_getD, show (f x).length + ((L.take t).map fun x => (f x).length).sum
      + k = (f x).length + (((L.take t).map fun x => (f x).length).sum + k) by omega,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD,
      ih]

/-- **A table's run of blocks**: the blocks of table `t`, weighted by their selectors, are the
table's list `fl`, weighted by the selectors of its run (`ρ` at `eqh`). -/
theorem vt_side_sum (O st : List ℕ) (fl : Table → List (List Form)) {n : ℕ}
    (hO : ∀ t < 6, ∀ j < n, (O.getD j 0 = t ↔
      st.getD t 0 ≤ j ∧ j < st.getD t 0 + (fl (tables.getD t default)).length))
    (hst : ∀ t < 6, st.getD t 0 = ((tables.take t).map fun x => (fl x).length).sum)
    (hn : ∀ t < 6, st.getD t 0 + (fl (tables.getD t default)).length ≤ n)
    {blocks : List BusBlock} {sels : List E} (hbl : blocks.length = n) (hsl : sels.length = n)
    (hown : blocks.map (·.owner) = O) (hcoord : blocks.map (·.coordinates) = tables.flatMap fl)
    (G : List Form → E) (ρ : ℕ → E) {t : ℕ} (ht : t < 6) {eqh : List ℕ}
    (hel : eqh.length = (fl (tables.getD t default)).length)
    (heq : ∀ k < eqh.length, ρ (eqh.getD k 0) = sels.getD (st.getD t 0 + k) 0) :
    sumE ((List.zip sels blocks).map fun p =>
        if p.2.owner = t then p.1 * G p.2.coordinates else 0) =
      sumE ((List.zip eqh (fl (tables.getD t default))).map fun p => ρ p.1 * G p.2) := by
  rw [vt_zip_map_range _ _ 0 default _ hsl hbl, vt_zip_map_range _ _ 0 default _ rfl hel.symm]
  have ho : ∀ j < n, (blocks.getD j default).owner = O.getD j 0 := fun j hj => by
    rw [← hown, List.getD_eq_getElem _ _ (by simpa using (show j < blocks.length by omega)),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  have hc : ∀ j < n, (blocks.getD j default).coordinates = (tables.flatMap fl).getD j default :=
    fun j hj => by
    rw [← hcoord, List.getD_eq_getElem _ _ (by simpa using (show j < blocks.length by omega)),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  have e : ((List.range n).map fun j => (fun p : E × BusBlock =>
      if p.2.owner = t then p.1 * G p.2.coordinates else 0) (sels.getD j 0, blocks.getD j default)) =
      (List.range n).map fun j => if O.getD j 0 = t then
        sels.getD j 0 * G ((tables.flatMap fl).getD j default) else 0 :=
    List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      simp only [ho j this, hc j this]
  rw [e, vt_seg_sum O _ (hn t ht) (hO t ht), hel]
  refine congrArg sumE (List.map_congr_left fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  rw [hst t ht, vt_flatMap_getD fl default tables t k (by simp [tables_length']; omega) hk', ← hst t ht,
    ← heq k (by omega)]

end
end LeanVM.Guest.B1.VerifySub
