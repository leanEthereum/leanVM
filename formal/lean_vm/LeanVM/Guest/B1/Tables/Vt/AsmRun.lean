/-
  LeanVM.Guest.B1.Tables.Vt.AsmRun

  Helpers of `verify_tables`' assembly: the words the run reads lie end to end from the cursor,
  the round count is the tables' largest height, the heights as a list.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.AsmTotals

/-!
# Assembly helpers

* `vt_readsAt_append`: words at `p`, then words right after them;
* `vt_foldl_max`: six heights, each at most `n`, one of them `n`, have the largest `n`;
* `vt_tableHeights_eq`: the heights of six row counts are `vtTauList (vtHt rows)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_readsAt_append {rd : Reader} {p : E} {a b : List E} (ha : TbReadsAt rd p a)
    (hb : TbReadsAt rd (p * gen ^ a.length) b) : TbReadsAt rd p (a ++ b) := by
  intro k hk
  rcases Nat.lt_or_ge k a.length with h1 | h1
  · rw [List.getElem_append_left h1]; exact ha k h1
  · rw [List.getElem_append_right h1]
    have := hb (k - a.length) (by simp at hk; omega)
    rw [tb_loadHolds_mul_gen_pow] at this
    rwa [show a.length + (k - a.length) = k by omega] at this

theorem vt_six {α : Type} (l : List α) (h : l.length = 6) (d : α) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d, l.getD 3 d, l.getD 4 d, l.getD 5 d] := by
  match l, h with
  | [_, _, _, _, _, _], _ => rfl

theorem vt_tableHeights_length {rows : List ℕ} (hr : rows.length = 6) :
    (tableHeightsOf rows).length = 6 := by
  simp [tableHeightsOf, hr, tableLogFloors]

theorem vt_tableHeights_eq {rows : List ℕ} (hr : rows.length = 6) :
    tableHeightsOf rows = vtTauList (vtHt rows) := by
  rw [vt_six _ (vt_tableHeights_length hr) 0]
  rfl

theorem vt_foldl_max {rows : List ℕ} (hr : rows.length = 6) {n : ℕ}
    (hle : ∀ t < 6, vtHt rows t ≤ n) (hex : ∃ t < 6, vtHt rows t = n) :
    (tableHeightsOf rows).foldl max 0 = n := by
  rw [vt_tableHeights_eq hr, show vtTauList (vtHt rows) = [vtHt rows 0, vtHt rows 1, vtHt rows 2,
    vtHt rows 3, vtHt rows 4, vtHt rows 5] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  have h0 := hle 0 (by norm_num); have h1 := hle 1 (by norm_num)
  have h2 := hle 2 (by norm_num); have h3 := hle 3 (by norm_num)
  have h4 := hle 4 (by norm_num); have h5 := hle 5 (by norm_num)
  obtain ⟨t, ht, he⟩ := hex
  interval_cases t <;> omega

theorem vt_powers5 (ξ : E) : powers ξ 5 = [1, ξ, ξ ^ 2, ξ ^ 3, ξ ^ 4] := by
  simp only [powers, powersFrom, List.cons.injEq, and_true]
  refine ⟨trivial, by ring, by ring, by ring, by ring⟩

theorem vt_nConstraints : (tables.map Table.nConstraints).sum = 2 := by
  rw [LeanVM.Protocol.EndToEnd.Complete.refNConstraints]; rfl

end
end LeanVM.Guest.B1.Tables
