/-
  LeanVM.Guest.EndExecHSlots

  The advised sizes the deployed guest pops by function (`advSlots`) are `Memory.heapSlots`, from the
  kernel's checks (`EndExecHChk`).
-/

module

public import LeanVM.Guest.EndExecA
public import LeanVM.Guest.EndExecHChk

/-!
# The advised slots by name

`slotsOf_nil`: a function without `allocAdvice` hints has no advised buffer. `advSlots_eq`: from
`noAdv_all` and the five functions' checks, `advSlots` is `heapSlots` on the program's functions, so
a valid tree pops the same advised sizes under both (`heapPops_advSlots`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (FnAl alignA alignA_of fnAl adviceOf isAdv bufsOf allocHints)

@[expose] public section

theorem advIdx_eq : ∀ (k : ℕ) (l : List (ℕ × Prover.Exec.Hint)), advIdx k l = advAtFrom k l
  | _, [] => rfl
  | k, q :: l => by rw [advIdx, advAtFrom, advIdx_eq (k + 1) l]

theorem advIdx_nil : ∀ (k : ℕ) (l : List (ℕ × Prover.Exec.Hint)), l.all (fun q ↦ !isAdv q.2) = true →
    advIdx k l = []
  | _, [], _ => rfl
  | k, q :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    rw [advIdx, ite_eq_right (by rw [h.1]; decide)]
    exact advIdx_nil (k + 1) l h.2

/-- A function without `allocAdvice` hints has no advised buffer. -/
theorem slotsOf_nil {F : FnAl} (h : (allocHints F.d).all (fun q ↦ !isAdv q.2) = true) : slotsOf F = [] :=
  advIdx_nil 0 _ (by
    rw [List.all_eq_true] at h ⊢
    exact fun q hq ↦ h q (List.mem_filter.mp hq).1)

theorem heapSlots_other {f : String} (h1 : f ≠ "main") (h2 : f ≠ "claim_list_digest") (h3 : f ≠ "da_verify")
    (h4 : f ≠ "verify_sub") (h5 : f ≠ "verify_tables") : heapSlots f = [] := by
  unfold heapSlots
  split <;> simp_all

/-- **`advSlots` is `heapSlots` on the program's functions.** -/
theorem advSlots_eq {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) : advSlots f = heapSlots f := by
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  rw [advSlots, alignA_of hj, slotsOf, advIdx_eq]
  by_cases h1 : f = "main"
  · subst h1; rw [idx_main] at hj; cases hj; exact advAt_main
  by_cases h2 : f = "claim_list_digest"
  · subst h2; rw [idx_cld] at hj; cases hj; exact advAt_cld
  by_cases h3 : f = "da_verify"
  · subst h3; rw [idx_dv] at hj; cases hj; exact advAt_dv
  by_cases h4 : f = "verify_sub"
  · subst h4; rw [idx_vs] at hj; cases hj; exact advAt_vs
  by_cases h5 : f = "verify_tables"
  · subst h5; rw [idx_vt] at hj; cases hj; exact advAt_vt
  rw [heapSlots_other h1 h2 h3 h4 h5, ← advIdx_eq, ← slotsOf]
  obtain ⟨i, rfl, hi, hn, -, -, -, -, -, h2'⟩ := B2C.fn_of_idx hj
  refine slotsOf_nil (noAdv_all (i + 1) h2' fun hm ↦ ?_)
  have e : ∀ g, B2C.idxOf g = some (i + 1) → g = f := fun g hg ↦ by
    obtain ⟨i', e', hi', hn', -⟩ := B2C.fn_of_idx hg
    obtain rfl : i' = i := by omega
    exact hn'.symm.trans hn
  simp only [advFns, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm
  · exact h1 (e _ (by rw [hm]; exact idx_main)).symm
  · exact h2 (e _ (by rw [hm]; exact idx_cld)).symm
  · exact h3 (e _ (by rw [hm]; exact idx_dv)).symm
  · exact h4 (e _ (by rw [hm]; exact idx_vs)).symm
  · exact h5 (e _ (by rw [hm]; exact idx_vt)).symm

/-- **A valid tree pops the same advised sizes under `advSlots` and `heapSlots`.** -/
theorem heapPops_advSlots {rd : Reader} {t : Tree} {args rets : List E} (hv : t.Valid coreProgram rd args rets) :
    t.heapPops advSlots = t.heapPops heapSlots :=
  heapPops_congr (fun _ _ hf ↦ advSlots_eq hf) t hv

end

end LeanVM.Guest.EndExec
