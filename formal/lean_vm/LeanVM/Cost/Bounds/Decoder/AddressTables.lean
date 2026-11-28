module

public import LeanVM.Cost.Bounds.DecoderExtra
public import LeanVM.Cost.Prices

/-!
# Bounds: the address tables

The decoder's address tables (`Extraction.Fast.powTable`, compiled as `powTableC` in
`Cost/Decoder/Base.lean`): `2^κ` powers of `g` and their lanes, merge-sorted.

* **`powTable_cost`**: the address table of `2^κ` words, `(74κ + 121)·2^κ + 17`;
* `powTable_size`, `wordTable_powTable`: its size, and its pairs word-sized.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

section Tables
open Auto.LeanVM.Extraction.Fast

theorem length_powPairs : ∀ (n i : ℕ) (x : K), (powPairs n i x).length = n
  | 0, _, _ => rfl
  | n + 1, i, x => by rw [powPairs, List.length_cons, length_powPairs n]

theorem mem_powPairs : ∀ (n i : ℕ) (x : K) (e : ℕ × ℕ), e ∈ powPairs n i x →
    e.1 < 2 ^ 64 ∧ e.2 < i + n
  | 0, _, _, e, h => by simp [powPairs] at h
  | n + 1, i, x, e, h => by
    rw [powPairs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨UInt64.toNat_lt _, by dsimp only; omega⟩
    · have := mem_powPairs n (i + 1) (x * LeanVM.Parameters.g) e h
      omega

theorem powTable_size (κ : ℕ) : (powTable κ).size = 2 ^ κ := by
  rw [powTable, List.size_toArray, List.length_mergeSort, length_powPairs]

/-- The address table of `2^κ` words, `κ ≤ 62`, is a table of word-sized pairs. -/
theorem wordTable_powTable {κ : ℕ} (hκ : κ ≤ 62) : WordTable (powTable κ) := by
  refine ⟨by rw [powTable_size]; exact Nat.pow_lt_pow_right (by norm_num) (by omega), ?_⟩
  intro e he
  rw [powTable, List.toList_toArray, List.mem_mergeSort] at he
  have := mem_powPairs _ _ _ e he
  have : 2 ^ κ < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- The pairs `(lane of g^i, i)` (`powPairs.c553`): `52` per pair, `5` at the end. -/
theorem powPairs_cost (hP : Includes P powPairs.c553.costDeps) :
    ∀ (n i : ℕ) (x : K), n + i < 2 ^ 64 →
      machineCost P powPairs.c553.costIdx [encodeValue n, encodeValue i, encodeValue x] ≤ 52 * n + 5
  | 0, i, x, _ => by rw [powPairs.c553.costEq_zero P hP]
  | n + 1, i, x, h => by
    rw [powPairs.c553.costEq_succ P hP, limbs_of_lt (by omega : n + 1 < 2 ^ 64),
      limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i + 1 < 2 ^ 64)]
    have := powPairs_cost hP n (i + 1) (x * LeanVM.Parameters.g) (by omega)
    omega

/-- **The address table** (`powTableC`) of `2^κ` words: `2^κ` powers and their merge sort, at
most `(74κ + 121)·2^κ + 17`. -/
theorem powTable_cost (hP : Includes P powTableC.costDeps) (κ : ℕ) (hκ : κ ≤ 62) :
    machineCost P powTableC.costIdx [encodeValue κ] ≤ (74 * κ + 121) * 2 ^ κ + 17 := by
  rw [powTableC.costEq P hP, limbs_shift (by omega), limbs_of_lt (by omega : κ < 2 ^ 64),
    List.length_mergeSort, length_powPairs]
  have hN : 2 ^ κ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 := powPairs_cost P (by includes) (2 ^ κ) 0 1 (by omega)
  have h2 := mergeSortList_cost P (by includes) _ (.closure powTableC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (powTableC.lam0.costSpec P (by includes) a b)) 7
    (fun e ↦ e.1 < 2 ^ 64)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil]
      rw [powTableC.lam0.costEq P (by includes), limbs_of_lt ha, limbs_of_lt hb]
      omega)
    (powPairs (2 ^ κ) 0 1) (by rw [length_powPairs]; exact hN)
    (fun e he ↦ (mem_powPairs _ _ _ e he).1)
  rw [length_powPairs, Nat.clog_pow 2 κ (by norm_num)] at h2
  have : (74 * κ + 121) * 2 ^ κ = 74 * (2 ^ κ * κ) + 121 * 2 ^ κ := by ring
  omega

end Tables

end

end LeanVM.Cost.Bounds
