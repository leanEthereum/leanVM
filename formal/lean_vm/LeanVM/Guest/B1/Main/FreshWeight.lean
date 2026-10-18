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

theorem drop_map_range (f : ℕ → E) (n k : ℕ) (hk : k ≤ n) :
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
  rw [ofK_mul, ofK_one, foldl_mul_eq_prod (fun k => Flock.phi8 (k + 1)), map_prod] at h
  rw [word_eOfNat, eOfNat, show 64 - 1 = 63 from rfl, foldl_mul_eq_prod]
  exact h

theorem lagNum_eq (z : E) (i : ℕ) (hi : i < 64) :
    lagNum z i * windowDenominator 64 = (lagrangeWeights 64 z).getD i 0 := by
  rw [lagrange_getD z i hi, lagNum]
  congr 2
  · exact Finset.prod_congr rfl fun j hj => by rw [phiE_eq j (by simp at hj; omega)]
  · exact Finset.prod_congr rfl fun j hj => by rw [phiE_eq j (by simp at hj; omega)]

end
end LeanVM.Guest.B1.Main
