import Sphincs.H0Tensor

/-! **The codeword tables.** The codeword counts `pmf(m) = #{w : lut w = m}` by point increments,
their prefix sums `K(m) = #{w : lut w ≤ m} = 256 H(m)`, and the numerators
`F(u) = Σ_m K(m)^u Δ*K(m)` and `F2(u) = Σ_m K(m)^u Δ*(K^2)(m)`, so that `f(u) = F(u) / 256^(u+1)` and
`f2(u) = F2(u) / 256^(u+2)`. All numerators up to a bound are computed in one pass over the grid. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### Linearity of the forward difference -/

theorem D1_const_mul (c : ℝ) (h : FPos → ℝ) (y : FPos) : D1 (fun y => c * h y) y = c * D1 h y := by
  unfold D1
  split_ifs <;> ring

theorem deltaF_const_mul (c : ℝ) : ∀ (d : ℕ) (g : (Fin d → FPos) → ℝ) (m : Fin d → FPos),
    deltaF d (fun m => c * g m) m = c * deltaF d g m
  | 0, _, _ => rfl
  | d + 1, g, m => by
      simp only [deltaF]
      have h : ∀ y : FPos, deltaF d (fun m' => c * g (Fin.cons y m')) (Fin.tail m) =
          c * deltaF d (fun m' => g (Fin.cons y m')) (Fin.tail m) := fun y => deltaF_const_mul c d _ _
      simp only [h]
      exact D1_const_mul c _ _

/-! ### The codeword counts -/

/-- The codeword counts. -/
def pmfT : NT childChains :=
  (List.finRange 256).foldl (fun t w => incT childChains t (lut w)) (zeroT childChains)

theorem getT_foldl_incT (L : List LutIdx) (t : NT childChains) (m : FChain → FPos) :
    getT childChains (L.foldl (fun t w => incT childChains t (lut w)) t) m =
      getT childChains t m + (L.filter fun w => decide (m = lut w)).length := by
  induction L generalizing t with
  | nil => simp
  | cons w L ih =>
      rw [List.foldl_cons, ih, getT_incT, List.filter_cons]
      by_cases h : m = lut w
      · simp [h]; ring
      · simp [h]

theorem getT_pmfT (m : FChain → FPos) :
    getT childChains pmfT m = (Finset.univ.filter fun w : LutIdx => lut w = m).card := by
  unfold pmfT
  rw [getT_foldl_incT, getT_zeroT, zero_add]
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 256).filter _)]
  congr 1
  ext w
  simp [eq_comm]

/-- The CDF counts `K(m) = #{w : lut w ≤ m}`. -/
def KT : NT childChains := cumT childChains pmfT

theorem getT_KT (m : FChain → FPos) : (getT childChains KT m : ℝ) = 256 * Hm m := by
  unfold KT
  rw [getT_cumT]
  unfold cumF Hm avgR
  simp only [getT_pmfT, Int.cast_natCast, Fintype.card_fin]
  rw [← mul_assoc, show (256 : ℝ) * ((256 : ℕ) : ℝ)⁻¹ = 1 by norm_num, one_mul]
  -- both sides count the codewords below `m`
  have h : ∀ y : FChain → FPos, (if ∀ i, y i ≤ m i then
      ((Finset.univ.filter fun w : LutIdx => lut w = y).card : ℝ) else 0) =
      ∑ w : LutIdx, if lut w = y ∧ ∀ i, y i ≤ m i then (1 : ℝ) else 0 := by
    intro y
    split_ifs with hy
    · rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hy]
    · exact (Finset.sum_eq_zero fun w _ => ite_eq_right (fun h => hy h.2)).symm
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single (lut w)]
  · have hiff : (lut w = lut w ∧ ∀ i, lut w i ≤ m i) ↔ ∀ i, (lut w i).val ≤ (m i).val :=
      ⟨fun h i => Fin.le_iff_val_le_val.1 (h.2 i), fun h => ⟨rfl, fun i => Fin.le_iff_val_le_val.2 (h i)⟩⟩
    by_cases hall : ∀ i, (lut w i).val ≤ (m i).val
    · rw [ite_eq_left (hiff.2 hall), ite_eq_left hall]
    · rw [ite_eq_right (fun h => hall (hiff.1 h)), ite_eq_right hall]
  · intro x _ hx
    rw [ite_eq_right]
    rintro ⟨h1, _⟩
    exact hx h1.symm
  · simp


/-! ### The numerators of `f` and `f2` -/

/-- Forward differences of the CDF counts. -/
def DK : NT childChains := deltaT childChains KT

/-- Forward differences of the squared CDF counts. -/
def DK2 : NT childChains := deltaT childChains (mapT childChains (fun k => k * k) KT)

/-- The numerators, for every `u ≤ U`, in one pass over the grid. -/
def sumTL : (d : ℕ) → (ℤ → ℤ → List ℤ) → NT d → NT d → List ℤ
  | 0, f, a, b => f (show ℤ from a) (show ℤ from b)
  | d + 1, f, a, b =>
      let a' := (show Five (NT d) from a)
      let b' := (show Five (NT d) from b)
      List.zipWith (· + ·) (List.zipWith (· + ·) (List.zipWith (· + ·) (List.zipWith (· + ·)
        (sumTL d f a'.c0 b'.c0) (sumTL d f a'.c1 b'.c1)) (sumTL d f a'.c2 b'.c2)) (sumTL d f a'.c3 b'.c3))
        (sumTL d f a'.c4 b'.c4)

/-- The powers `k^u dk` for `u ≤ U`. -/
def powsL (U : ℕ) (k dk : ℤ) : List ℤ := (List.range (U + 1)).map fun u => k ^ u * dk

theorem length_sumTL (U : ℕ) : ∀ (d : ℕ) (a b : NT d), (sumTL d (powsL U) a b).length = U + 1
  | 0, _, _ => by simp [sumTL, powsL]
  | d + 1, a, b => by
      simp only [sumTL, List.length_zipWith, length_sumTL U d]
      simp

theorem getD_zipWith_add (l l' : List ℤ) (hl : l.length = l'.length) (u : ℕ) :
    (List.zipWith (· + ·) l l').getD u 0 = l.getD u 0 + l'.getD u 0 := by
  rcases lt_or_ge u l.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simp [List.length_zipWith]; omega), List.getD_eq_getElem _ _ h,
      List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
  · rw [List.getD_eq_default _ _ (by simp [List.length_zipWith]; omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]
    ring

theorem getD_sumTL (U u : ℕ) (hu : u ≤ U) : ∀ (d : ℕ) (a b : NT d),
    (sumTL d (powsL U) a b).getD u 0 = sumT2 d (fun k dk => k ^ u * dk) a b
  | 0, a, b => by
      simp only [sumTL, sumT2, powsL]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
  | d + 1, a, b => by
      simp only [sumTL, sumT2]
      rw [getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL])]
      simp only [getD_sumTL U u hu d]

/-! The kernel's cache grows with the number of powers one declaration evaluates, so `H0FTab.lean`
checks the powers `a ≤ u < a + n` in slices (`powsR`) and joins them with `sumTL_powsR_split`. -/

/-- The powers `k^u dk` for `a ≤ u < a + n`. -/
def powsR (a n : ℕ) (k dk : ℤ) : List ℤ := (List.range n).map fun i => k ^ (a + i) * dk

theorem powsL_eq_powsR (U : ℕ) : powsL U = powsR 0 (U + 1) := by
  funext k dk
  simp [powsL, powsR]

theorem length_sumTL_of (f : ℤ → ℤ → List ℤ) (n : ℕ) (hf : ∀ k dk, (f k dk).length = n) :
    ∀ (d : ℕ) (a b : NT d), (sumTL d f a b).length = n
  | 0, _, _ => hf _ _
  | d + 1, a, b => by simp [sumTL, List.length_zipWith, length_sumTL_of f n hf d]

theorem sumTL_append (f g : ℤ → ℤ → List ℤ) (n : ℕ) (hf : ∀ k dk, (f k dk).length = n) :
    ∀ (d : ℕ) (a b : NT d), sumTL d (fun k dk => f k dk ++ g k dk) a b = sumTL d f a b ++ sumTL d g a b
  | 0, _, _ => rfl
  | d + 1, a, b => by
      have hl := length_sumTL_of f n hf d
      simp only [sumTL, sumTL_append f g n hf d]
      rw [List.zipWith_append (by rw [hl, hl]), List.zipWith_append (by simp [List.length_zipWith, hl]),
        List.zipWith_append (by simp [List.length_zipWith, hl]),
        List.zipWith_append (by simp [List.length_zipWith, hl])]

theorem sumTL_powsR_split (a n m : ℕ) {N : ℕ} (h : n + m = N) (d : ℕ) (x y : NT d) :
    sumTL d (powsR a N) x y = sumTL d (powsR a n) x y ++ sumTL d (powsR (a + n) m) x y := by
  subst h
  have : powsR a (n + m) = fun k dk => powsR a n k dk ++ powsR (a + n) m k dk := by
    funext k dk
    simp [powsR, List.range_add, Nat.add_assoc]
  rw [this, sumTL_append _ _ n (fun _ _ => by simp [powsR])]

/-- The numerator of `f(u)`. -/
def fNum (u : ℕ) : ℤ := sumT2 childChains (fun k dk => k ^ u * dk) KT DK

/-- The numerator of `f2(u)`. -/
def f2Num (u : ℕ) : ℤ := sumT2 childChains (fun k dk => k ^ u * dk) KT DK2

theorem fR_num (u : ℕ) : fR u = (fNum u : ℝ) / 256 ^ (u + 1) := by
  rw [fR_grid]
  have hH : Hm = fun m => (1 / 256 : ℝ) * (getT childChains KT m : ℝ) := funext fun m => by rw [getT_KT]; ring
  have hD : ∀ m, deltaF childChains Hm m = (1 / 256 : ℝ) * (getT childChains DK m : ℝ) := by
    intro m
    rw [hH, deltaF_const_mul, DK, getT_deltaT]
  simp only [hD]
  unfold fNum
  rw [sumT2_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hH]
  simp only []
  rw [mul_pow, div_pow, one_pow]
  push_cast
  field_simp
  ring

theorem f2R_num (u : ℕ) : f2R u = (f2Num u : ℝ) / 256 ^ (u + 2) := by
  rw [f2R_grid]
  have hH : Hm = fun m => (1 / 256 : ℝ) * (getT childChains KT m : ℝ) := funext fun m => by rw [getT_KT]; ring
  have hD : ∀ m, deltaF childChains (fun m => Hm m ^ 2) m = (1 / 65536 : ℝ) * (getT childChains DK2 m : ℝ) := by
    intro m
    have hsq : (fun m => Hm m ^ 2) = fun m => (1 / 65536 : ℝ) *
        (getT childChains (mapT childChains (fun k => k * k) KT) m : ℝ) := funext fun m => by
      rw [getT_mapT, hH]
      push_cast
      ring
    rw [hsq, deltaF_const_mul, DK2, getT_deltaT]
  simp only [hD]
  unfold f2Num
  rw [sumT2_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hH]
  simp only []
  rw [mul_pow, div_pow, one_pow]
  push_cast
  field_simp
  ring
end Sphincs.Security.H0
