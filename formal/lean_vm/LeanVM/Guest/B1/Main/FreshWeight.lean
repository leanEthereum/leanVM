/-
  LeanVM.Guest.B1.Main.FreshWeight

  The weight of a fresh claim (`Node.freshWeight`, N:251) is what `__loop99` computes (`guestU`):
  the Lagrange weights as prefix and suffix products, the lincheck's weights as tensors.
-/

module

public import LeanVM.Guest.B1.Main.Multilinear

/-!
# The fresh weight

`lagrange_getD`: `lagrangeWeights 64 z` (V:750) at `i` is the product of `z + φ(j)` over `j ≠ i`
times `windowDenominator 64`; the data's nodes and `LAGRANGE_INV_S` are those (`Consts`). The row
weights are `eqKernel rowPoint ⊗ lagrangeWeights`, the column weights `eqKernel columnPoint ⊗
slices` (V:1968-1975), so their extensions split (`mle_tensor`), and `guestU_eq` assembles them.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## Products as folds -/

theorem foldl_mul_eq_prod {M : Type} [CommMonoid M] (f : ℕ → M) : ∀ n : ℕ,
    ((List.range n).map f).foldl (· * ·) 1 = ∏ j ∈ Finset.range n, f j
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_mul_eq_prod f n,
      Finset.prod_range_succ]
    rfl

theorem foldl_mul_reverse (a : E) : ∀ l : List E, l.reverse.foldl (· * ·) a = l.foldl (· * ·) a
  | [] => rfl
  | x :: l => by
    rw [List.reverse_cons, List.foldl_append, foldl_mul_reverse a l, List.foldl_cons,
      List.foldl_cons, List.foldl_nil, mul_comm a x, foldl_mul_assoc, mul_comm]

theorem drop_map_range (f : ℕ → E) (n k : ℕ) (_hk : k ≤ n) :
    ((List.range n).map f).drop k = (List.range (n - k)).map fun j => f (k + j) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem take_map_range (f : ℕ → E) (n k : ℕ) (_hk : k ≤ n) :
    ((List.range n).map f).take k = (List.range k).map f := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

/-! ## The Lagrange weights -/

/-- **The Lagrange weights** at `z` are the prefix times the suffix products of `z + φ(j)`, times
the window's denominator. -/
theorem lagrange_getD (z : E) (i : ℕ) (hi : i < 64) :
    (lagrangeWeights 64 z).getD i 0 = (∏ j ∈ Finset.range i, (z + phi j)) *
      (∏ j ∈ Finset.Ico (i + 1) 64, (z + phi j)) * windowDenominator 64 := by
  have hd : ((List.range 64).map fun k ↦ z + phi k).length = 64 := by simp
  simp only [lagrangeWeights]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith, List.getElem_take,
    List.getElem_scanl, List.getElem_drop, List.getElem_reverse, List.getElem_scanl,
    take_map_range _ _ _ (by omega), foldl_mul_eq_prod]
  congr 2
  simp only [List.length_scanl, List.length_reverse, hd]
  rw [show 64 + 1 - 1 - (1 + i) = 63 - i by omega, List.take_reverse, hd,
    show 64 - (63 - i) = i + 1 by omega, foldl_mul_reverse, drop_map_range _ _ _ (by omega),
    foldl_mul_eq_prod, Finset.prod_Ico_eq_prod_range]

theorem phiE_eq (j : ℕ) (hj : j < 64) : phiE j = phi j := by
  rw [phiE, word_eOfNat, eOfNat, phiWords_eq j hj]; rfl

theorem lagInv_eq : word 11666641484232641359 0 0 = windowDenominator 64 := by
  rw [windowDenominator]
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg ofK lagInv_mul
  have hp : ofK (∏ j ∈ Finset.range 63, Flock.phi8 (j + 1)) = ∏ j ∈ Finset.range 63, phi (j + 1) :=
    map_prod (algebraMap K E) _ _
  rw [ofK_mul, ofK_one, foldl_mul_eq_prod (fun k => Flock.phi8 (k + 1)), hp] at h
  rw [word_eOfNat, eOfNat, show 64 - 1 = 63 from rfl, foldl_mul_eq_prod]
  exact h

theorem lagNum_eq (z : E) (i : ℕ) (hi : i < 64) :
    lagNum z i * windowDenominator 64 = (lagrangeWeights 64 z).getD i 0 := by
  rw [lagrange_getD z i hi, lagNum]
  congr 2
  · exact Finset.prod_congr rfl fun j hj => by rw [phiE_eq j (by simp at hj; omega)]
  · exact Finset.prod_congr rfl fun j hj => by rw [phiE_eq j (by simp at hj; omega)]

/-! ## The fresh claims' cells -/

theorem getD_append_left' {l1 l2 : List E} {k : ℕ} (h : k < l1.length) :
    (l1 ++ l2).getD k 0 = l1.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

theorem getD_append_right' {l1 l2 : List E} {k : ℕ} :
    (l1 ++ l2).getD (l1.length + k) 0 = l2.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- The cells of a fresh claim of the guest's shape, by their `FRESH_*` offsets. -/
theorem fixedCells_getD {f : FixedClaims} (hf : FreshShaped f) :
    (fixedCells f).length = 106 ∧
    (∀ k < 22, (fixedCells f).getD k 0 = f.bytecodePoint.getD k 0) ∧
    (fixedCells f).getD 22 0 = f.bytecodeValue ∧ (fixedCells f).getD 23 0 = f.alpha ∧
    (fixedCells f).getD 24 0 = f.zSkip ∧
    (∀ k < 8, (fixedCells f).getD (25 + k) 0 = f.rowPoint.getD k 0) ∧
    (∀ j < 8, (fixedCells f).getD (33 + j) 0 = f.columnPoint.getD (7 - j) 0) ∧
    (∀ i < 64, (fixedCells f).getD (41 + i) 0 = f.slices.getD i 0) ∧
    (fixedCells f).getD 105 0 = f.matrixValue := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hA : (f.bytecodePoint ++ [f.bytecodeValue, f.alpha, f.zSkip]).length = 25 := by simp [h1]
  have hB : (f.bytecodePoint ++ [f.bytecodeValue, f.alpha, f.zSkip] ++ f.rowPoint).length = 33 := by
    simp [h1, h2]
  have hC : (f.bytecodePoint ++ [f.bytecodeValue, f.alpha, f.zSkip] ++ f.rowPoint ++
      f.columnPoint.reverse).length = 41 := by simp [h1, h2, h3]
  have hD : (f.bytecodePoint ++ [f.bytecodeValue, f.alpha, f.zSkip] ++ f.rowPoint ++
      f.columnPoint.reverse ++ f.slices).length = 105 := by simp [h1, h2, h3, h4]
  have key : ∀ i, (fixedCells f).getD i 0 =
      if i < 22 then f.bytecodePoint.getD i 0 else if i = 22 then f.bytecodeValue else
      if i = 23 then f.alpha else if i = 24 then f.zSkip else
      if i < 33 then f.rowPoint.getD (i - 25) 0 else
      if i < 41 then f.columnPoint.reverse.getD (i - 33) 0 else
      if i < 105 then f.slices.getD (i - 41) 0 else if i = 105 then f.matrixValue else 0 := by
    intro i
    simp only [fixedCells, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_append,
      List.length_cons, List.length_nil, h1, h2, h3, h4, List.length_reverse]
    split_ifs <;> first | omega | (simp_all; done) |
      (rw [List.getElem?_eq_none (by simp; omega)]; rfl)
  refine ⟨by simp [fixedCells, h1, h2, h3, h4], fun k hk => ?_, ?_, ?_, ?_, fun k hk => ?_,
    fun j hj => ?_, fun i hi => ?_, ?_⟩
  · rw [key]; simp [hk]
  · rw [key]; simp
  · rw [key]; simp
  · rw [key]; simp
  · rw [key, ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega),
      ite_pos' (by omega), Nat.add_sub_cancel_left]
  · rw [key, ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_pos' (by omega),
      Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega), h3, show 8 - 1 - j = 7 - j by omega]
  · rw [key, ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega),
      ite_pos' (by omega), Nat.add_sub_cancel_left]
  · rw [key]; simp

/-! ## The weight -/

theorem eqEval_prod : ∀ (l m : List E) (n : ℕ), l.length = n → m.length = n →
    eqEval l m = ∏ k ∈ Finset.range n, (1 + l.getD k 0 + m.getD k 0)
  | [], [], 0, _, _ => rfl
  | x :: l, y :: m, n + 1, h1, h2 => by
    rw [eqEval_cons, eqEval_prod l m n (by simpa using h1) (by simpa using h2),
      Finset.prod_range_succ', mul_comm]
    simp
  | [], _ :: _, _, h1, h2 => by simp at h1 h2; omega
  | _ :: _, [], _, h1, h2 => by simp at h1 h2; omega
  | [], [], _ + 1, h1, _ => by simp at h1
  | _ :: _, _ :: _, 0, h1, _ => by simp at h1

theorem length_lagrangeWeights (z : E) : (lagrangeWeights 64 z).length = 64 := by
  simp [lagrangeWeights]

/-- **The guest's weight is the fresh claim's** (`Node.freshWeight`, N:251): at the batched matrix
point `rr`, from the fresh claim's cells and the two `eqtree`s of `rr`'s row and column halves. -/
theorem guestU_eq {f : FixedClaims} (hf : FreshShaped f) {rr : List E} (hr : rr.length = 28) :
    guestU ((fixedCells f).getD 24 0) (fun k => (fixedCells f).getD (25 + k) 0)
      (fun j => (fixedCells f).getD (33 + j) 0) (fun i => (fixedCells f).getD (41 + i) 0)
      (fun i => (eqKernel (rr.take 6)).getD i 0)
      (fun i => (eqKernel ((rr.drop 14).take 6)).getD i 0) (fun k => rr.getD k 0) =
      freshWeight f rr := by
  obtain ⟨-, -, -, -, hz, hrp, hcp, hsl, -⟩ := fixedCells_getD hf
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hlag := length_lagrangeWeights f.zSkip
  -- the row weights
  have hrow : multilinearEval (lincheckRowWeights f.zSkip f.rowPoint) (rr.take blake2sR1csLogSize) =
      (∏ k ∈ Finset.range 8, (1 + f.rowPoint.getD k 0 + rr.getD (6 + k) 0)) *
        (windowDenominator 64 * ∑ i ∈ Finset.range 64, lagNum f.zSkip i *
          (eqKernel (rr.take 6)).getD i 0) := by
    rw [lincheckRowWeights, show blake2sR1csLogSize = 6 + 8 from rfl, List.take_add,
      show kBits = 64 from rfl, mle_tensor (by rw [hlag, List.length_take, hr]; rfl)
        (by rw [length_eqKernel, List.length_take, List.length_drop, hr, h2]; rfl),
      mle_eqKernel _ _ (by simp [h2, hr]), mle_eq_sum _ _ (by rw [hlag, List.length_take, hr]; rfl),
      eqEval_prod _ _ 8 h2 (by simp [hr])]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact Finset.prod_congr rfl fun k hk => by
        have : k < 8 := by simpa using hk
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop, this]
    · rw [List.length_take, hr, show min 6 28 = 6 from rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [← lagNum_eq _ i (by simp at hi; omega)]; ring
  -- the column weights
  have hcol : multilinearEval (lincheckColumnWeights f.columnPoint f.slices)
      (rr.drop blake2sR1csLogSize) =
      (∏ k ∈ Finset.range 8, (1 + f.columnPoint.getD k 0 + rr.getD (20 + k) 0)) *
        ∑ i ∈ Finset.range 64, f.slices.getD i 0 * (eqKernel ((rr.drop 14).take 6)).getD i 0 := by
    have hm : (fun w => f.slices.map (· * w)) = fun w => f.slices.map (w * ·) :=
      funext fun w => List.map_congr_left fun b _ => mul_comm b w
    rw [lincheckColumnWeights, hm, show blake2sR1csLogSize = 14 from rfl,
      ← List.take_append_drop 6 (rr.drop 14),
      mle_tensor (by rw [h4, List.length_take, List.length_drop, hr]; rfl)
        (by rw [length_eqKernel, List.length_drop, List.length_drop, hr, h3]),
      mle_eqKernel _ _ (by simp [h3, hr]),
      mle_eq_sum _ _ (by rw [h4, List.length_take, List.length_drop, hr]; rfl),
      eqEval_prod _ _ 8 h3 (by simp [hr]), List.take_append_drop,
      List.length_take, List.length_drop, hr, show min 6 (28 - 14) = 6 from rfl]
    refine congrArg₂ (· * ·) ?_ rfl
    exact Finset.prod_congr rfl fun k hk => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [freshWeight, hrow, hcol, guestU, hz, lagInv_eq]
  have e1 : ∑ i ∈ Finset.range 64, f.slices.getD i 0 * (eqKernel ((rr.drop 14).take 6)).getD i 0 =
      ∑ i ∈ Finset.range 64, (fixedCells f).getD (41 + i) 0 *
        (eqKernel ((rr.drop 14).take 6)).getD i 0 :=
    Finset.sum_congr rfl fun i hi => by rw [hsl i (by simpa using hi)]
  have e2 : ∏ k ∈ Finset.range 8, (1 + f.rowPoint.getD k 0 + rr.getD (6 + k) 0) =
      ∏ k ∈ Finset.range 8, (1 + (fixedCells f).getD (25 + k) 0 + rr.getD (6 + k) 0) :=
    Finset.prod_congr rfl fun k hk => by rw [hrp k (by simpa using hk)]
  have e3 : ∏ k ∈ Finset.range 8, (1 + f.columnPoint.getD k 0 + rr.getD (20 + k) 0) =
      ∏ j ∈ Finset.range 8, (1 + (fixedCells f).getD (33 + j) 0 + rr.getD (27 - j) 0) := by
    rw [← Finset.prod_range_reflect]
    exact Finset.prod_congr rfl fun j hj => by
      have : j < 8 := by simpa using hj
      rw [hcp j this, show 8 - 1 - j = 7 - j by omega, show 20 + (7 - j) = 27 - j by omega]
  rw [e1, e2, e3]
  ring

end
end LeanVM.Guest.B1.Main
