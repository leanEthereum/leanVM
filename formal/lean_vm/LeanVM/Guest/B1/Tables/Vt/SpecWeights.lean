/-
  LeanVM.Guest.B1.Tables.Vt.SpecWeights

  The specification's table weights (`tableWeights`, V:658-662) are the guest's: the running
  product of the high challenges times the prefix equality weight of the low ones.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecPad
public import LeanVM.Protocol.EndToEnd.Complete.TableMath

/-!
# The table weights (V:658-662)

The table sumcheck's point is its challenges `pts` reversed. A table of height `h ≤ n` weighs
`Π_{v<h} (1 + e_v + r_v) · Π_{h≤v<n} r_v` (`getD_tableWeights`); the guest computes the product of
the first `n - h` challenges (`cprod`) times the prefix weight `Π_{v<h} (r_v + (1 + e_v))` (`peq`):
`vt_weight`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (weightFactor getD_tableWeights)
open Finset

@[expose] public section

theorem vt_list_prod_range : ∀ l : List E, l.prod = ∏ i ∈ range l.length, l.getD i 0
  | [] => by simp
  | a :: l => by
    rw [List.prod_cons, vt_list_prod_range l, List.length_cons, prod_range_succ']
    simp [mul_comm]

theorem vt_foldl_mul (l : List E) (s : E) : l.foldl (· * ·) s = s * l.prod := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, List.prod_cons]; ring

/-- The prefix weight of `r` against `1 + e`. -/
theorem vt_prefixProd (r e : List E) {n h : ℕ} (hr : r.length = n) (he : n ≤ e.length)
    (hh : h ≤ n) :
    prefixProd 1 r ((e.map (1 + ·)).take n) h =
      ∏ v ∈ range h, (1 + e.getD v 0 + r.getD v 0) := by
  rw [prefixProd, vt_foldl_mul, one_mul, vt_list_prod_range]
  have hl : (List.zipWith (· + ·) (r.take h) (((e.map (1 + ·)).take n).take h)).length = h := by
    simp; omega
  rw [hl]
  refine prod_congr rfl fun v hv ↦ ?_
  have hv' := mem_range.mp hv
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_zipWith, List.getElem_take, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  ring

/-- The running product of the first `n - h` challenges. -/
theorem vt_cprod (pts : List E) {n h : ℕ} (hn : pts.length = n) (hh : h ≤ n) :
    (pts.take (n - h)).prod = ∏ k ∈ range (n - h), pts.reverse.getD (h + k) 0 := by
  rw [vt_list_prod_range, List.length_take, show min (n - h) pts.length = n - h by omega,
    ← prod_range_reflect]
  refine prod_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_take, List.getElem_reverse]
  congr 1
  omega

/-- **A table's weight** at the reversed challenges is the guest's `cprod · peq`. -/
theorem vt_weight (heights : List ℕ) (e pts : List E) {n t : ℕ} (hn : pts.length = n)
    (he : n ≤ e.length) (ht : t < heights.length) (hh : heights.getD t 0 ≤ n) :
    (tableWeights heights e pts.reverse).getD t 0 =
      (pts.take (n - heights.getD t 0)).prod *
        prefixProd 1 pts.reverse ((e.map (1 + ·)).take n) (heights.getD t 0) := by
  rw [getD_tableWeights _ _ _ _ ht, List.length_reverse, hn,
    vt_prefixProd _ _ (by simp [hn]) he hh, vt_cprod pts hn hh]
  set h := heights.getD t 0
  rw [show n = h + (n - h) by omega, prod_range_add, mul_comm]
  rw [show h + (n - h) - h = n - h by omega]
  congr 1
  · refine prod_congr rfl fun k _ ↦ ?_
    simp [weightFactor]
  · refine prod_congr rfl fun v hv ↦ ?_
    simp [weightFactor, mem_range.mp hv]

end
end LeanVM.Guest.B1.Tables
