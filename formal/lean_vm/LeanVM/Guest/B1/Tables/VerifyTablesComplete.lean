/-
  LeanVM.Guest.B1.Tables.VerifyTablesComplete

  `verify_tables` is complete, placed (`CompleteTablesAt`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCHelp
public import LeanVM.Guest.B1.Tables.VerifyTablesCTail
public import LeanVM.Guest.B1.Tables.VerifyTablesSound
public import LeanVM.Guest.B1.Tables.VtCKids
public import LeanVM.Guest.B1.Tables.VtCAir
public import LeanVM.Guest.B1.Tables.VtSortC
public import LeanVM.Guest.B1.Tables.VtZcC
public import LeanVM.Guest.B1.Tables.VtCEv
public import LeanVM.Guest.B1.Tables.VtCGlue4
public import LeanVM.Protocol.Whir.Sound.Weights

/-!
# `verify_tables`, placed

From the run of `tablesSeg` read back (`tablesSeg_trace`), the honest buffers (`vtOwnW`) and the
callees (`vtKids`), the windows chained over the whole body give the valuation `completeAt_flatD`
asks for.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem vtPre_flat : vtPre.all Stmt.flat = true := by decide +kernel

theorem vtPre_addrs : vtPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vtPre_length : vtPre.length = 7899 := by decide +kernel

theorem vt_not_loop : coreProgram.loop "verify_tables" = false := by decide +kernel

theorem exists_eq_foldl_max (f : ℕ → ℕ) : ∀ m, 0 < m → ∃ t < m, f t = ((List.range m).map f).foldl max 0
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, _ => by
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨t, ht, he⟩ := exists_eq_foldl_max f m hm
      rcases le_total (((List.range m).map f).foldl max 0) (f m) with h | h
      · exact ⟨m, by omega, by rw [max_eq_right h]⟩
      · exact ⟨t, by omega, by rw [max_eq_left h, he]⟩

theorem prodE_take_map (ch : ℕ → E) {n j : ℕ} (hj : j ≤ n) :
    prodE (((List.range n).map ch).take j) = ∏ i ∈ Finset.range j, ch i := by
  rw [prodE_eq_prod, List.length_take, List.length_map, List.length_range, min_eq_left hj]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_map, List.getElem_range]

theorem eqEval_take {point chis : List E} {k : ℕ} (hp : k ≤ point.length) (hc : k ≤ chis.length) :
    eqEval (point.take k) (chis.take k) = ∏ j ∈ Finset.range k, (1 + point.getD j 0 + chis.getD j 0) := by
  rw [LeanVM.Protocol.Whir.Sound.eqEval_eq_prod _ _ (by simp [List.length_take]; omega), Fin.prod_univ_eq_prod_range
    (fun j => 1 + (point.take k).getD j 0 + (chis.take k).getD j 0)]
  rw [List.length_take, min_eq_left hp]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj', ↓reduceIte]

/-- The alloc values' positions: the first five, the two index chains, the table sumcheck's three,
and the selectors' three each. -/
def selIdx (i : ℕ) : ℕ := if i < 8 then 0 else if i < 11 then 1 else if i < 15 then 2 else (i - 16) / 3 + 3
def selK (i : ℕ) : ℕ := if i < 8 then i - 5 else if i < 11 then i - 8 else if i < 15 then i - 12 else (i - 16) % 3

theorem vt_alloc_cover : ∀ i < 205, (i < 5 ∨ i = 11 ∨ i = 15 ∨ 202 ≤ i) ∨
    (selIdx i < 65 ∧ selK i < 3 ∧ selBuf (selIdx i) + selK i = i) := by decide +kernel

theorem vt_alloc_sel : ∀ j < 65, ∀ k < 3, vtAllocVar.getD (selBuf j + k) 0 =
    selVal.getD j 0 + [12, 15, 16].getD k 0 := by decide +kernel

end
end LeanVM.Guest.B1.VerifySub
