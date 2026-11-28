module

public import NativeVm.Equiv.KeccakPure

/-!
# Phase 6's arithmetic as sums

The model's sums of `E` elements (`sumE`, `dot`, the masked sums) as `Finset` sums over an index
range of their elements' values (`EW.toE`), the form the code's sums compute.
-/

@[expose] public section

namespace NativeVm.Math.Keccak

open NativeVm.Model LeanVM.Parameters Finset

/-- A left sum of a list is the sum of its entries. -/
theorem foldl_add_range (l : List LeanVM.Parameters.E) :
    l.foldl (· + ·) 0 = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.length_append,
      List.length_singleton, sum_range_succ]
    congr 1
    · refine sum_congr rfl fun i hi ↦ ?_
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (mem_range.1 hi)]
    · simp [List.getD_eq_getElem?_getD]

theorem getD_map_toE' (a : Array EW) (i : Nat) :
    (a.toList.map EW.toE).getD i 0 = (a.getD i 0).toE := by
  rw [← NativeVm.Equiv.Keccak.toE_getD]

/-- **`sumE` as a sum.** -/
theorem toE_sumE_range (a : Array EW) : (sumE a).toE = ∑ i ∈ range a.size, (a.getD i 0).toE := by
  rw [NativeVm.Equiv.toE_sumE, LeanVM.Protocol.Verifier.sumE, foldl_add_range, List.length_map,
    Array.length_toList]
  exact sum_congr rfl fun i _ ↦ getD_map_toE' a i

/-- **`dot` as a sum.** -/
theorem toE_dot_range (a b : Array EW) :
    (dot a b).toE = ∑ i ∈ range (min a.size b.size), (a.getD i 0).toE * (b.getD i 0).toE := by
  rw [NativeVm.Equiv.toE_dot, LeanVM.Protocol.Verifier.dot, foldl_add_range, List.length_zipWith,
    List.length_map, List.length_map, Array.length_toList, Array.length_toList]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [mem_range] at hi
  rw [← getD_map_toE', ← getD_map_toE']
  have ha : i < a.size := by omega
  have hb : i < b.size := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, Array.getElem?_eq_getElem ha,
    Array.getElem?_eq_getElem hb]

/-- **A masked sum over a range.** -/
theorem toE_sumE_filterMap (n : Nat) (p : Nat → Bool) (g : Nat → EW) :
    (sumE ((Array.range n).filterMap fun z ↦ if p z then some (g z) else none)).toE =
      ∑ z ∈ range n, if p z then (g z).toE else 0 := by
  rw [NativeVm.Equiv.toE_sumE, LeanVM.Protocol.Verifier.sumE, Array.toList_filterMap,
    Array.toList_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filterMap_append, List.map_append, List.foldl_append, ih,
      sum_range_succ]
    by_cases h : p n <;> simp [h]

end NativeVm.Math.Keccak
