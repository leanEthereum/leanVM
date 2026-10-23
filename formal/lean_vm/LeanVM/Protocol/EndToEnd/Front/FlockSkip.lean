/-
  LeanVM.Protocol.EndToEnd.Front.FlockSkip

  The program's univariate-skip interpolation equals ArkLib's: the barycentric weights of the
  Python verifier over the nodes `φ_8(0), …, φ_8(127)` are the Lagrange weights, the window
  denominator being every node's Lagrange denominator because the nodes are an `F_2`-subspace.
-/

module

public import LeanVM.Protocol.Flock
public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.EndToEnd.Front.FlockSumcheck

/-!
# The skip interpolation

`lagrangeInterpolate (2·64) (0⁶⁴ ‖ p_coset) z_skip` (`verifier.py:1112-1122, 1140` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) computes the barycentric weights from prefix and
suffix products of `z + φ(k)` and one *window denominator* `(Π_{0 < k < 128} φ(k))⁻¹` shared by
every node. ArkLib's skip round (`skipClaim`) interpolates with each node's own Lagrange
denominator `Π_{j ≠ i} (φ(i) - φ(j))`.

**The fidelity check.** The two agree (`lagrangeInterpolate_eq_skipClaim`): the prefix and suffix
products are the product over the other nodes (`lagrangeWeights_getElem`), and since `φ_8` is
additive on bytes (`phi8_xor`) and `i ↦ i ⊕ j` permutes `[0, 128)`, every node's denominator is
`Π_{0 < k < 128} φ(k)` in characteristic two (`prod_sub_nodes`). The shared denominator is
correct only because the nodes form an `F_2`-subspace. No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Flock CompPoly

@[expose] public section

/-! ## Folds as sums and products -/

/-- A left fold of additions is the start plus the sum. -/
theorem foldl_add_eq (a : E) (l : List E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- A left fold of products is the start times the product. -/
theorem foldl_mul_eq (a : E) (l : List E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- `dot` of two lists of length `n` is the sum of the products. -/
theorem dot_eq_sum : ∀ {n : ℕ} {l₁ l₂ : List E} (h₁ : l₁.length = n) (h₂ : l₂.length = n),
    dot l₁ l₂ = ∑ i : Fin n, l₁[i]'(by omega) * l₂[i]'(by omega)
  | 0, [], [], _, _ => by simp [dot]
  | n + 1, a :: l₁, b :: l₂, h₁, h₂ => by
    have ih := dot_eq_sum (n := n) (l₁ := l₁) (l₂ := l₂) (by simpa using h₁) (by simpa using h₂)
    unfold dot at ih ⊢
    rw [foldl_add_eq] at ih
    rw [List.zipWith_cons_cons, List.foldl_cons, foldl_add_eq, Fin.sum_univ_succ]
    rw [zero_add] at ih
    simp [ih]

/-! ## The barycentric weights -/

/-- The prefix products: entry `i` is the product of the first `i` differences. -/
theorem getElem_scanl_mul (l : List E) (i : ℕ) (h : i < (l.scanl (· * ·) 1).length) :
    (l.scanl (· * ·) 1)[i] = (l.take i).prod := by
  rw [List.getElem_scanl, foldl_mul_eq, one_mul]

/-- The suffix products: entry `i + 1` of the reversed scan of the reversed list is the product
of the entries after `i`. -/
theorem getElem_suffix (l : List E) (i j : ℕ) (hj : j = i + 1) (hi : i < l.length)
    (h : j < ((l.reverse.scanl (· * ·) 1).reverse).length) :
    ((l.reverse.scanl (· * ·) 1).reverse)[j] = (l.drop (i + 1)).prod := by
  subst hj
  have hlen : (l.reverse.scanl (· * ·) 1).length = l.length + 1 := by simp
  rw [List.getElem_reverse, getElem_scanl_mul]
  simp only [hlen]
  rw [List.take_reverse, List.prod_reverse]
  congr 2
  simp
  omega

/-- The product of a list but one entry. -/
theorem prod_take_mul_prod_drop (l : List E) (i : ℕ) :
    (l.take i).prod * (l.drop (i + 1)).prod = (l.eraseIdx i).prod := by
  rw [List.eraseIdx_eq_take_drop_succ, List.prod_append]

/-- The product over `[0, n)`, as a list. -/
theorem prod_map_range (g : ℕ → E) : ∀ n, ((List.range n).map g).prod = ∏ k ∈ Finset.range n, g k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      prod_map_range g n, Finset.prod_range_succ]
    simp

/-- The product over `[0, n)` but `i`, as a list. -/
theorem prod_eraseIdx_map_range (g : ℕ → E) :
    ∀ (n i : ℕ), i < n →
      (((List.range n).map g).eraseIdx i).prod = ∏ k ∈ (Finset.range n).erase i, g k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    by_cases hi : i < n
    · rw [List.eraseIdx_append_of_lt_length (by simpa using hi), List.prod_append,
        prod_eraseIdx_map_range g n i hi, Finset.range_add_one, Finset.erase_insert_of_ne
          (by omega), Finset.prod_insert (by simp)]
      simp [mul_comm]
    · have hin : i = n := by omega
      subst hin
      rw [List.eraseIdx_append_of_length_le (by simp)]
      simp [Finset.range_add_one, prod_map_range]

/-- **The barycentric weight of node `i`** is the product of the differences to the other nodes
times the window denominator. -/
theorem lagrangeWeights_getElem (count : ℕ) (point : E) (i : ℕ) (hi : i < count)
    (h : i < (lagrangeWeights count point).length) :
    (lagrangeWeights count point)[i] =
      (∏ k ∈ (Finset.range count).erase i, (point + phi k)) * windowDenominator count := by
  simp only [lagrangeWeights, List.getElem_zipWith]
  rw [List.getElem_take, getElem_scanl_mul, List.getElem_drop,
    getElem_suffix _ i (1 + i) (by omega) (by simpa using hi), prod_take_mul_prod_drop,
    prod_eraseIdx_map_range _ _ _ hi]

/-- The barycentric weights are one per node. -/
theorem length_lagrangeWeights (count : ℕ) (point : E) :
    (lagrangeWeights count point).length = count := by
  simp [lagrangeWeights]

/-! ## The nodes -/

/-- Xoring twice with the same number cancels. -/
theorem xor_xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Two numbers whose xor is zero are equal. -/
theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have := xor_xor_cancel a b
  rw [h, Nat.xor_zero] at this
  exact this

/-- **Every node's Lagrange denominator is the window's.** The nodes `φ_8(0), …, φ_8(127)` are an
`F_2`-subspace: `φ(i) - φ(j) = φ(i ⊕ j)`, and `j ↦ i ⊕ j` sends the other nodes onto the nonzero
bytes below `128`. -/
theorem prod_sub_nodes (i : Fin 128) :
    ∏ j ∈ Finset.univ.erase i, (ofK (Flock.phi8 i) - ofK (Flock.phi8 j)) =
      ∏ k ∈ Finset.range 127, phi (k + 1) := by
  have hsub : ∀ j : Fin 128, ofK (Flock.phi8 i) - ofK (Flock.phi8 j) =
      ofK (Flock.phi8 (i.val ^^^ j.val)) := fun j ↦ by
    rw [phi8_xor, ofK_add, CharTwo.sub_eq_add]
  simp only [hsub]
  have hlt : ∀ j : Fin 128, i.val ^^^ j.val < 128 := fun j ↦
    Nat.xor_lt_two_pow (n := 7) i.isLt j.isLt
  refine Finset.prod_bij' (fun j _ ↦ (i.val ^^^ j.val) - 1)
    (fun k hk ↦ ⟨i.val ^^^ (k + 1), Nat.xor_lt_two_pow (n := 7) i.isLt
      (by simp at hk; omega)⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    have := hlt j
    simp
    omega
  · intro k hk
    have hk' : k + 1 < 128 := by simp at hk; omega
    refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, Finset.mem_univ _⟩
    have h' := congrArg Fin.val h
    simp only at h'
    have := xor_xor_cancel i.val (k + 1)
    rw [h', Nat.xor_self] at this
    omega
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    apply Fin.ext
    simp only
    rw [Nat.sub_add_cancel (by omega), xor_xor_cancel]
  · intro k hk
    simp only
    rw [xor_xor_cancel]
    rfl
  · intro j hj
    have hne : i.val ^^^ j.val ≠ 0 := fun h ↦
      (Finset.mem_erase.mp hj).1 (Fin.ext (eq_of_xor_eq_zero h).symm)
    rw [Nat.sub_add_cancel (by omega)]
    rfl

/-- The window denominator is the inverse of the product of the nonzero nodes. -/
theorem windowDenominator_eq (count : ℕ) :
    windowDenominator count = (∏ k ∈ Finset.range (count - 1), phi (k + 1))⁻¹ := by
  rw [windowDenominator, foldl_mul_eq, one_mul, prod_map_range]

/-- The inverse Lagrange denominators of the skip nodes are the window denominator. -/
theorem allInv_flockSkipDomain (i : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip)) :
    flockSkipDomain.allInv[i] = windowDenominator 128 := by
  rw [windowDenominator_eq, ← prod_sub_nodes (i : Fin 128)]
  simp [flockSkipDomain, SkipDomain.ofPts, lagrangeInv, flockNodes, Flock.skipNode]
  rfl

/-- The numerator of node `i` at `Y`: the product of the differences to the other nodes. -/
theorem prod_sub_flockNodes (Y : E) (i : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip)) :
    ∏ j ∈ Finset.univ.erase i, (Y - flockSkipDomain.pts[j]) =
      ∏ k ∈ (Finset.range 128).erase i.val, (Y + phi k) := by
  have h128 : 2 ^ Flock.kSkip + 2 ^ Flock.kSkip = 128 := rfl
  refine Finset.prod_bij' (fun j _ ↦ j.val) (fun k hk ↦ ⟨k, by
      have := (Finset.mem_erase.mp hk).2; rw [h128]; simpa using this⟩) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hj).1 (Fin.ext h), by
      have : j.val < 128 := h128 ▸ j.isLt
      simpa using this⟩
  · intro k hk
    exact Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_erase.mp hk).1 (congrArg Fin.val h),
      Finset.mem_univ _⟩
  · intro j _
    rfl
  · intro k _
    rfl
  · intro j _
    simp [flockSkipDomain, SkipDomain.ofPts, flockNodes, Flock.skipNode, phi, CharTwo.sub_eq_add]

/-- **The program's skip interpolation is ArkLib's** (`skipClaim`): the zeros on the skip domain
and the received values on its coset, interpolated at `z_skip`. -/
theorem lagrangeInterpolate_eq_skipClaim (pCoset : List E) (h : pCoset.length = 64) (Y : E) :
    lagrangeInterpolate (2 * LeanVM.Protocol.Verifier.kBits)
        (List.replicate LeanVM.Protocol.Verifier.kBits 0 ++ pCoset) Y =
      skipClaim flockSkipDomain (toVec 64 pCoset) Y := by
  have hk : LeanVM.Protocol.Verifier.kBits = 64 := rfl
  rw [hk, lagrangeInterpolate, dot_eq_sum (n := 128) (by simp [length_lagrangeWeights])
    (by simp [h])]
  rw [skipClaim, interpolateWith]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hw := lagrangeWeights_getElem (2 * 64) Y i.val i.isLt
    (by rw [length_lagrangeWeights]; exact i.isLt)
  simp only [Fin.getElem_fin]
  rw [hw, lagrangeWeightWith, prod_sub_flockNodes, allInv_flockSkipDomain]
  congr 1
  simp only [Vector.getElem_append, Vector.getElem_replicate, toVec, Vector.getElem_ofFn]
  have h64 : (2 : ℕ) ^ Flock.kSkip = 64 := rfl
  split_ifs with hi
  · rw [h64] at hi
    rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate]
  · rw [h64] at hi
    rw [List.getElem_append_right (by simpa using hi)]
    simp only [List.length_replicate, h64]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

end

end LeanVM.Protocol.EndToEnd.Front
