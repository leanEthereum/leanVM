module

public import LeanVM.Cost.Bounds.PMFFT.MulCost
public import LeanVM.Cost.Bounds.Decoder.Poly
public import LeanVM.Cost.Bounds.PMLane.InterpDefs

/-!
# Bounds of the PM decoder's FFT: Karatsuba's product

`karatsuba fuel p q` (`karatsuba.c415`), both factors of at most `32·2^k` coefficients and
`k ≤ fuel`: at most `karBound k` (`3·karBound k + 1006·32·2^k + 587` a level, the schoolbook
product of `32 × 32` below); `karBound 7 ≈ 2^28.31`, so the schedule's Karatsuba branch (both
factors at most `4096`) is within `karMax = 2^29`.
-/

namespace LeanVM.Cost.Bounds.PMFFT

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-- Karatsuba's price bound at `k` halvings. -/
@[expose] def karBound : ℕ → ℕ
  | 0 => 121598
  | k + 1 => 3 * karBound k + 1006 * (32 * 2 ^ k) + 587

theorem karBound_7 : karBound 7 ≤ karMax := by decide

theorem karBound_mono {a b : ℕ} (h : a ≤ b) : karBound a ≤ karBound b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · have := ih (by omega); rw [karBound]; omega
    · rw [show a = b + 1 by omega]

theorem coeffsBetween_size (p : CompPoly.CPolynomial K) (lo hi : ℕ) :
    (coeffsBetween p lo hi).val.size ≤ hi - lo := by
  unfold coeffsBetween
  refine (FFT.size_ofArray_le _).trans ?_
  simp only [Array.size_extract]
  omega

theorem cpoly_neg_size (x : CompPoly.CPolynomial K) : (-x).val.size ≤ x.val.size := by
  apply FFT.size_le_of_coeff_eq_zero
  intro i hi
  rw [← CompPoly.CPolynomial.toPoly_coeff, CompPoly.CPolynomial.toPoly_neg, Polynomial.coeff_neg,
    CompPoly.CPolynomial.toPoly_coeff, CompPoly.CPolynomial.coeff_eq_zero_of_size_le _ hi, neg_zero]

theorem cpoly_sub_size_le (x y : CompPoly.CPolynomial K) :
    (x - y).val.size ≤ max x.val.size y.val.size := by
  apply FFT.size_le_of_coeff_eq_zero
  intro i hi
  rw [← CompPoly.CPolynomial.toPoly_coeff, CompPoly.CPolynomial.toPoly_sub, Polynomial.coeff_sub,
    CompPoly.CPolynomial.toPoly_coeff, CompPoly.CPolynomial.toPoly_coeff,
    CompPoly.CPolynomial.coeff_eq_zero_of_size_le _ (le_trans (le_max_left _ _) hi),
    CompPoly.CPolynomial.coeff_eq_zero_of_size_le _ (le_trans (le_max_right _ _) hi), sub_zero]

theorem shiftX_size (t : ℕ) (x : CompPoly.CPolynomial K) : (shiftX t x).val.size ≤ t + x.val.size := by
  unfold shiftX
  refine (FFT.size_ofArray_le _).trans ?_
  simp

theorem coeffsBetweenC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.coeffsBetween.c416.costDeps)
    (p : CompPoly.CPolynomial K) (lo hi : ℕ) (hhi : hi < 2 ^ 40) :
    machineCost P Auto.LeanVM.Extraction.Fast.coeffsBetween.c416.costIdx [encodeValue p,
      encodeValue lo, encodeValue hi] ≤ 22 * (hi - lo) + 19 := by
  rw [Auto.LeanVM.Extraction.Fast.coeffsBetween.c416.costEq P hP]
  have hs : (p.val.extract lo hi).size ≤ hi - lo := by simp only [Array.size_extract]; omega
  have := Decoder.ofArray_cost P (by includes) (p.val.extract lo hi) (by omega)
  omega

theorem negMapC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.karatsuba.c415.costDeps) (x : CompPoly.CPolynomial K) :
    machineCost P Auto.List.map.c30.costIdx
      [MachineValue.closure Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costIdx [],
        encodeValue x.val.toList] ≤ 14 * x.val.size + 3 := by
  have := map_cost P (by includes) (fun a : K ↦ -a)
    (.closure Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costSpec P (by includes) a)) 1
    x.val.toList (fun a _ ↦ by
      simp only [appCost_fn, List.nil_append, List.length_nil, Nat.add_zero]
      rw [Auto.CompPoly.CPolynomial.Raw.sub.c49.lam0.costEq P (by includes)])
  simpa using this

theorem schoolbook32_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.mul.c36.costDeps)
    (p q : CompPoly.CPolynomial K) (hp : p.val.size ≤ 32) (hq : q.val.size ≤ 32) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.mul.c36.costIdx [encodeValue p.val, encodeValue q.val] ≤
      121570 := by
  have := Decoder.mulK_cost P hP p.val q.val (by omega) (by omega)
  have h1 : q.val.size * p.val.size ≤ 1024 := by nlinarith
  have h2 : p.val.size * p.val.size ≤ 1024 := by nlinarith
  omega

/-- **Karatsuba's product** (`karatsuba.c415`), factors of at most `32·2^k` coefficients, `k ≤ fuel`:
at most `karBound k`. -/
theorem karatsubaC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.karatsuba.c415.costDeps) :
    ∀ k fuel (p q : CompPoly.CPolynomial K), k ≤ fuel → fuel ≤ 64 → k ≤ 12 → p.val.size ≤ 32 * 2 ^ k →
      q.val.size ≤ 32 * 2 ^ k →
      machineCost P Auto.LeanVM.Extraction.Fast.karatsuba.c415.costIdx [encodeValue fuel, encodeValue p,
        encodeValue q] ≤ karBound k := by
  have hcut : karatsubaCutoff = 32 := rfl
  intro k
  induction k with
  | zero =>
    intro fuel p q _ hf _ hp hq
    have := schoolbook32_cost P (by includes) p q (by simpa using hp) (by simpa using hq)
    cases fuel with
    | zero => rw [Auto.LeanVM.Extraction.Fast.karatsuba.c415.costEq_zero P hP]; rw [karBound]; omega
    | succ n =>
      rw [Auto.LeanVM.Extraction.Fast.karatsuba.c415.costEq_succ P hP, hcut, karBound]
      simp only [pow_zero, Nat.mul_one] at hp hq
      cost_simp
      split_ifs <;> omega
  | succ k ih =>
    intro fuel p q hk hf hk12 hp hq
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hpk : 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hps : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [hps] at hp hq
    rw [Auto.LeanVM.Extraction.Fast.karatsuba.c415.costEq_succ P hP, hcut]
    simp only [karatsuba_eq]
    have hKB := karBound_mono (show 0 ≤ k + 1 by omega)
    rw [show karBound 0 = 121598 from rfl] at hKB
    by_cases hM : max p.val.size q.val.size ≤ 32
    · have := schoolbook32_cost P (by includes) p q (by omega) (by omega)
      cost_simp
      split_ifs <;> omega
    · set M := max p.val.size q.val.size with hMdef
      set H := (M + 1) / 2 with hHdef
      have hH : H ≤ 32 * 2 ^ k := by omega
      have hMH : M - H ≤ H := by omega
      have hp0 := coeffsBetween_size p 0 H
      have hp1 := coeffsBetween_size p H M
      have hq0 := coeffsBetween_size q 0 H
      have hq1 := coeffsBetween_size q H M
      have c1 := coeffsBetweenC_cost P (by includes) p 0 H (by omega)
      have c2 := coeffsBetweenC_cost P (by includes) p H M (by omega)
      have c3 := coeffsBetweenC_cost P (by includes) q 0 H (by omega)
      have c4 := coeffsBetweenC_cost P (by includes) q H M (by omega)
      generalize coeffsBetween p 0 H = p0 at *
      generalize coeffsBetween p H M = p1 at *
      generalize coeffsBetween q 0 H = q0 at *
      generalize coeffsBetween q H M = q1 at *
      have hpp := Decoder.cpoly_add_size_le p0 p1
      have hqq := Decoder.cpoly_add_size_le q0 q1
      have r1 := ih n p0 q0 (by omega) (by omega) (by omega) (by omega) (by omega)
      have r2 := ih n p1 q1 (by omega) (by omega) (by omega) (by omega) (by omega)
      have r3 := ih n (p0 + p1) (q0 + q1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have a1 := Decoder.addK_cost P (by includes) p0.val p1.val (by omega) (by omega)
      have a2 := Decoder.addK_cost P (by includes) q0.val q1.val (by omega) (by omega)
      have z0 := Decoder.cpoly_mul_size_le p0 q0
      have z2 := Decoder.cpoly_mul_size_le p1 q1
      have z1 := Decoder.cpoly_mul_size_le (p0 + p1) (q0 + q1)
      have n0 := cpoly_neg_size (p0 * q0)
      have n2 := cpoly_neg_size (p1 * q1)
      have m0 := negMapC_cost P (by includes) (p0 * q0)
      have m2 := negMapC_cost P (by includes) (p1 * q1)
      have s1 := cpoly_sub_size_le ((p0 + p1) * (q0 + q1)) (p0 * q0)
      have s2 := cpoly_sub_size_le ((p0 + p1) * (q0 + q1) - p0 * q0) (p1 * q1)
      have a3 := Decoder.addK_cost P (by includes) ((p0 + p1) * (q0 + q1)).val (-(p0 * q0)).val
        (by omega) (by omega)
      have a4 := Decoder.addK_cost P (by includes) ((p0 + p1) * (q0 + q1) - p0 * q0).val
        (-(p1 * q1)).val (by omega) (by omega)
      have sh1 := Decoder.shiftXC_cost P (by includes) H
        ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1) (by omega)
      have sz1 := shiftX_size H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)
      have a5 := Decoder.addK_cost P (by includes) (p0 * q0).val
        (shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val (by omega) (by omega)
      have sh2 := Decoder.shiftXC_cost P (by includes) (2 * H) (p1 * q1) (by omega)
      have sz2 := shiftX_size (2 * H) (p1 * q1)
      have sz3 := Decoder.cpoly_add_size_le (p0 * q0)
        (shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1))
      have a6 := Decoder.addK_cost P (by includes)
        (p0 * q0 + shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val
        (shiftX (2 * H) (p1 * q1)).val (by omega) (by omega)
      have ep0 : p0.val.size ≤ H := by omega
      have ep1 : p1.val.size ≤ H := by omega
      have eq0 : q0.val.size ≤ H := by omega
      have eq1 : q1.val.size ≤ H := by omega
      have ez0 : (p0 * q0).val.size ≤ 2 * H := by omega
      have ez2 : (p1 * q1).val.size ≤ 2 * H := by omega
      have epp : (p0 + p1).val.size ≤ H := hpp.trans (max_le ep0 ep1)
      have eqq : (q0 + q1).val.size ≤ H := hqq.trans (max_le eq0 eq1)
      have ez1 : ((p0 + p1) * (q0 + q1)).val.size ≤ 2 * H := by omega
      have es1 : ((p0 + p1) * (q0 + q1) - p0 * q0).val.size ≤ 2 * H := s1.trans (max_le ez1 ez0)
      have es2 : ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1).val.size ≤ 2 * H :=
        s2.trans (max_le es1 ez2)
      have esh1 : (shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val.size ≤ 3 * H := by omega
      have esh2 : (shiftX (2 * H) (p1 * q1)).val.size ≤ 4 * H := by omega
      have es3 : (p0 * q0 + shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val.size ≤ 3 * H :=
        sz3.trans (max_le (by omega) esh1)
      have mx1 : max p0.val.size p1.val.size ≤ H := max_le ep0 ep1
      have mx2 : max q0.val.size q1.val.size ≤ H := max_le eq0 eq1
      have mx3 : max ((p0 + p1) * (q0 + q1)).val.size (-(p0 * q0)).val.size ≤ 2 * H :=
        max_le ez1 (n0.trans ez0)
      have mx4 : max ((p0 + p1) * (q0 + q1) - p0 * q0).val.size (-(p1 * q1)).val.size ≤ 2 * H :=
        max_le es1 (n2.trans ez2)
      have mx5 : max (p0 * q0).val.size
          (shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val.size ≤ 3 * H :=
        max_le (by omega) esh1
      have mx6 : max (p0 * q0 + shiftX H ((p0 + p1) * (q0 + q1) - p0 * q0 - p1 * q1)).val.size
          (shiftX (2 * H) (p1 * q1)).val.size ≤ 4 * H := max_le (by omega) esh2
      have hc2 : M - H ≤ H := hMH
      clear hpp hqq s1 s2 sz1 sz2 sz3 z0 z1 z2 hp0 hp1 hq0 hq1 ih
      rw [karBound, ite_eq_right hM]
      simp only [ite_self, List.length_map, Array.length_toList]
      cost_simp
      have hH32 : H ≤ 32 * 2 ^ k := hH
      simp only [Nat.sub_zero] at c1 c3
      have hc2' : 22 * (M - H) ≤ 22 * H := Nat.mul_le_mul_left _ hc2
      linarith

/-- **The schedule's Karatsuba branch** (fuel `64`, factors of at most `4096` coefficients): at
most `karMax = 2^32`. -/
theorem karatsuba64_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.karatsuba.c415.costDeps)
    (p q : CompPoly.CPolynomial K) (hp : p.val.size ≤ 4096) (hq : q.val.size ≤ 4096) :
    machineCost P Auto.LeanVM.Extraction.Fast.karatsuba.c415.costIdx [encodeValue 64, encodeValue p,
      encodeValue q] ≤ karMax :=
  (karatsubaC_cost P hP 7 64 p q (by norm_num) (by norm_num) (by norm_num) (by simpa using hp)
    (by simpa using hq)).trans karBound_7

/-! ## The product, every branch -/

open LeanVM.Cost.Bounds.PMBasis

/-- A schoolbook product with a factor of at most `32` coefficients folded over: at most
`2581·|g| + 38978`. -/
theorem schoolbookSmall_cost (hP : Includes P Auto.CompPoly.CPolynomial.Raw.mul.c36.costDeps)
    (f g : CompPoly.CPolynomial K) (hf : f.val.size ≤ 32) (hg : g.val.size < 2 ^ 40) :
    machineCost P Auto.CompPoly.CPolynomial.Raw.mul.c36.costIdx [encodeValue f.val, encodeValue g.val] ≤
      2581 * g.val.size + 38978 := by
  have := Decoder.mulK_cost P hP f.val g.val (by omega) (by omega)
  have h1 : g.val.size * f.val.size ≤ g.val.size * 32 := Nat.mul_le_mul_left _ hf
  have h2 : f.val.size * f.val.size ≤ 1024 := by nlinarith
  omega

theorem schoolbook_fit (p : PMPrices) (hp : FFTPricesOK p) {j b : ℕ} (hj : j ≤ 36)
    (hb : b ≤ 2 ^ j + 1) : 2581 * b + 38978 + 20 ≤ polyMulPrice p j + karMax := by
  rcases Nat.lt_or_ge j 9 with h9 | h9
  · have : 2 ^ j ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold karMax polyMulPrice
    omega
  · have hf := (hp.2 j (by omega)).1
    unfold fwdNeed fwdBound at hf
    have hjj : 2 ^ j * 81 ≤ 2 ^ j * (j * j) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have hj1 : 2 ^ j * 9 ≤ 2 ^ j * j := Nat.mul_le_mul_left _ h9
    have h1 : 2 ^ 9 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h9
    unfold polyMulPrice karMax
    omega

/-- **`fftMulContext`'s product, every branch** (`mulViaFFTC`): the schoolbook product over the
small factor, Karatsuba's below `4096`, the transform above; within
`polyMulPrice p (clog2 (|f| + |g| − 1)) + karMax`, `|f| + |g| − 1 ≤ 2^36`. -/
theorem mulViaFFTC_cost (hP : Includes P mulViaFFTC.costDeps) (p : PMPrices) (hp : FFTPricesOK p)
    (f g : CompPoly.CPolynomial K) (hj : f.val.size + g.val.size - 1 ≤ 2 ^ 36) :
    machineCost P mulViaFFTC.costIdx [encodeValue f, encodeValue g] ≤
      polyMulPrice p (clog2 (f.val.size + g.val.size - 1)) + karMax := by
  by_cases hfft : 32 < f.val.size ∧ 32 < g.val.size ∧ (4096 < f.val.size ∨ 4096 < g.val.size)
  · have := mulViaFFTC_cost_fft P hP p hp f g hfft.1 hfft.2.1 hfft.2.2 hj
    omega
  · have hc := PMBasis.le_two_pow_clog2 (f.val.size + g.val.size - 1)
    have hcj : clog2 (f.val.size + g.val.size - 1) ≤ 36 := clog2_le hj
    rw [mulViaFFTC.costEq P hP]
    have hs : FFT.fftSchedule.small = 32 := rfl
    have hm : FFT.fftSchedule.mid = 4096 := rfl
    rw [hs, hm]
    by_cases hg : g.val.size ≤ 32
    · rw [ite_eq_left hg]
      have := schoolbookSmall_cost P (by includes) g f hg (by omega)
      have := schoolbook_fit p hp hcj (b := f.val.size) (by omega)
      cost_simp
      omega
    · rw [ite_eq_right hg]
      by_cases hf : f.val.size ≤ 32
      · rw [ite_eq_left hf]
        have := schoolbookSmall_cost P (by includes) f g hf (by omega)
        have := schoolbook_fit p hp hcj (b := g.val.size) (by omega)
        cost_simp
        omega
      · rw [ite_eq_right hf]
        have hk : f.val.size ≤ 4096 ∧ g.val.size ≤ 4096 := by omega
        rw [ite_eq_left hk]
        have := karatsuba64_cost P (by includes) f g hk.1 hk.2
        have : 1000 ≤ polyMulPrice p (clog2 (f.val.size + g.val.size - 1)) := by
          unfold polyMulPrice; omega
        cost_simp
        split_ifs <;> omega

end

end LeanVM.Cost.Bounds.PMFFT
