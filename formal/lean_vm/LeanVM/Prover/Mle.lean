/-
  LeanVM.Prover.Mle

  The array tables of `Statement/Prover/Mle.lean` are the verifier's lists: the equality table is
  `eqKernel`, a fold is `foldPairs`, the evaluation is `multilinearEval`.
-/

module

public import Statement.Prover.Mle
public import LeanVM.Protocol.Whir.Complete.Tables

/-!
# Array tables

* `toList_eqTable`, `getD_eqTable`: the equality table is `eqKernel`, entry `j` the weight
  `eq(j, p)`;
* `toList_foldPairsA`: a fold on the array is `foldPairs` on its list;
* `mleA_eq`, `mleK_eq`: the evaluation on the array is `multilinearEval` on its list;
* `sumRange_eq`: the loop is the sum;
* `getD_toList`, `toList_ofFn_range`: arrays read as lists.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.EndToEnd

@[expose] public section

/-- An array read at an index is its list read there. -/
theorem getD_toList {α : Type} (a : Array α) (i : ℕ) (d : α) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- An array of a function of the indices, read in range. -/
theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The equality table is the verifier's `eqKernel`. -/
theorem toList_eqTable (p : List E) : (eqTable p).toList = eqKernel p := by
  have h : ∀ (p : List E) (out : Array E),
      (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).toList =
        p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out.toList := by
    intro p
    induction p with
    | nil => intro out; rfl
    | cons r p ih =>
      intro out
      simp only [List.foldl_cons]
      rw [ih]
      simp
  exact h p #[1]

theorem size_eqTable (p : List E) : (eqTable p).size = 2 ^ p.length := by
  rw [← Array.length_toList, toList_eqTable, length_eqKernel]

/-- Entry `j` of the equality table is `eq(j, p)`. -/
theorem getD_eqTable (p : List E) (j : ℕ) (hj : j < 2 ^ p.length) :
    (eqTable p).getD j 0 = eqEval (boolPoint p.length j) p := by
  rw [getD_toList, toList_eqTable, getD_eqKernel p j hj]

/-- A fold on the array is the verifier's fold on its list. -/
theorem toList_foldPairsA (r : E) (t : Array E) :
    (foldPairsA r t).toList = foldPairs r t.toList := by
  apply List.ext_getElem (by simp [foldPairsA, length_foldPairs])
  intro i h1 h2
  have hi : i < t.size / 2 := by simpa [foldPairsA] using h1
  have h := getD_foldPairs r t.toList i (by simp; omega)
  rw [List.getD_eq_getElem _ _ h2] at h
  rw [h]
  simp [foldPairsA, List.getD_eq_getElem?_getD, show 2 * i < t.size by omega,
    show 2 * i + 1 < t.size by omega]

/-- Entry `u` of a fold. -/
theorem getD_foldPairsA (r : E) (t : Array E) {u : ℕ} (hu : u < t.size / 2) :
    (foldPairsA r t).getD u 0 = t.getD (2 * u) 0 * (1 + r) + t.getD (2 * u + 1) 0 * r := by
  simp [foldPairsA, Array.getD_eq_getD_getElem?, hu, show 2 * u < t.size by omega,
    show 2 * u + 1 < t.size by omega]

/-- The evaluation on the array is the verifier's `multilinearEval` on its list. -/
theorem mleA_eq (t : Array E) (p : List E) : mleA t p = multilinearEval t.toList p := by
  have h : ∀ (p : List E) (t : Array E),
      (p.foldl (fun cur r ↦ foldPairsA r cur) t).toList =
        p.foldl (fun cur r ↦ foldPairs r cur) t.toList := by
    intro p
    induction p with
    | nil => intro t; rfl
    | cons r p ih =>
      intro t
      simp only [List.foldl_cons]
      rw [ih, toList_foldPairsA]
  rw [mleA, multilinearEval, getD_toList, h, List.headD_eq_getD]

/-- The evaluation of a table over `K` is the verifier's `multilinearEval` of its lift. -/
theorem mleK_eq (t : Array K) (p : List E) : mleK t p = multilinearEval (t.toList.map ofK) p := by
  rw [mleK, mleA_eq, Array.toList_map]

/-- The loop is the sum. -/
theorem sumRange_eq (n : ℕ) (f : ℕ → E) : sumRange n f = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rw [sumRange, Nat.fold_zero, Finset.sum_range_zero]
  | succ n ih =>
    simp only [sumRange] at ih ⊢
    rw [Nat.fold_succ, ih, Finset.sum_range_succ]

end
end LeanVM.Prover
