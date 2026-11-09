/-
  LeanVM.Guest.B1.Tables.VtC.BStack

  `stackOffsets`' offsets are aligned to their blocks' sizes, and inside any power of two the
  blocks fit in.
-/

module

public import LeanVM.Guest.B1.Placement.Common

/-!
# Aligned stacks

`vtB_stack_aligned`: block `b`'s offset is a multiple of `2^size b` (the blocks before it in the
order are at least as large). `vtB_stack_lt`: it is below any `2^m` holding all the blocks.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

theorem vtB_stack_order (sizes : List ℕ) {b : ℕ} (hb : b < sizes.length) :
    ∃ r < sizes.length,
      ((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))).getD r 0 = b ∧
      (stackOffsets sizes).1.getD b 0 = tbPrefixSize (sizes.getD · 0)
        ((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))) r ∧
      ∀ k < r, sizes.getD b 0 ≤ sizes.getD
        (((List.range sizes.length).mergeSort (stackLe (sizes.getD · 0))).getD k 0) 0 := by
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)) with hord
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
  have hmem : b ∈ ord := hperm.mem_iff.mpr (List.mem_range.mpr hb)
  obtain ⟨r, hr, hrb⟩ := List.getElem_of_mem hmem
  have htrans : ∀ a b c, stackLe (sizes.getD · 0) a b = true → stackLe (sizes.getD · 0) b c = true →
      stackLe (sizes.getD · 0) a c = true := by
    intro a b c hab hbc
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
    omega
  have htotal : ∀ a b, (stackLe (sizes.getD · 0) a b || stackLe (sizes.getD · 0) b a) = true := by
    intro a b
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega
  have hsorted := List.pairwise_mergeSort htrans htotal (List.range sizes.length)
  rw [← hord] at hsorted
  have hrd : ord.getD r 0 = b := by rw [List.getD_eq_getElem _ _ hr, hrb]
  refine ⟨r, by omega, hrd, ?_, fun k hk ↦ ?_⟩
  · have := tb_stackOffsets_fst sizes r (by omega)
    rw [hrd] at this; exact this
  · have := List.pairwise_iff_getElem.mp hsorted k r (by omega) hr hk
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at this
    rw [hrb] at this
    rw [List.getD_eq_getElem ord 0 (by omega : k < ord.length)]
    omega

/-- **Block `b`'s offset is aligned to its size.** -/
theorem vtB_stack_aligned (sizes : List ℕ) {b : ℕ} (hb : b < sizes.length) :
    2 ^ sizes.getD b 0 ∣ (stackOffsets sizes).1.getD b 0 := by
  obtain ⟨r, hr, -, ho, hle⟩ := vtB_stack_order sizes hb
  rw [ho, tbPrefixSize]
  apply List.dvd_sum
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
  simp only [List.length_take] at hk
  have := hle k (by omega)
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0] at *
  exact Nat.pow_dvd_pow 2 this

/-- **Block `b`'s offset is below any `2^m` the blocks fit in.** -/
theorem vtB_stack_lt (sizes : List ℕ) {b : ℕ} (hb : b < sizes.length) {m : ℕ}
    (hfit : (sizes.map (2 ^ ·)).sum ≤ 2 ^ m) : (stackOffsets sizes).1.getD b 0 < 2 ^ m := by
  obtain ⟨r, hr, hrb, ho, -⟩ := vtB_stack_order sizes hb
  set ord := (List.range sizes.length).mergeSort (stackLe (sizes.getD · 0)) with hord
  have hperm : ord.Perm (List.range sizes.length) := List.mergeSort_perm _ _
  have hlen : ord.length = sizes.length := by rw [hperm.length_eq, List.length_range]
  rw [ho, tbPrefixSize]
  have htot : (ord.map fun i ↦ 2 ^ sizes.getD i 0).sum = (sizes.map (2 ^ ·)).sum := by
    rw [(hperm.map _).sum_eq]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  have hsplit := congrArg List.sum (List.map_append (f := fun i ↦ 2 ^ sizes.getD i 0)
    (l₁ := ord.take (r + 1)) (l₂ := ord.drop (r + 1)))
  rw [List.take_append_drop, List.sum_append] at hsplit
  have htake : ((ord.take (r + 1)).map fun i ↦ 2 ^ sizes.getD i 0).sum =
      ((ord.take r).map fun i ↦ 2 ^ sizes.getD i 0).sum + 2 ^ sizes.getD b 0 := by
    rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [← List.getD_eq_getElem _ 0, hrb]
  have hpos : 0 < 2 ^ sizes.getD b 0 := Nat.two_pow_pos _
  omega

end
end LeanVM.Guest.B1.Tables
