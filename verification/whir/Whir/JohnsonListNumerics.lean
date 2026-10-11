import Whir.CodingBounds

/-! Rational Johnson list-size estimates. Production profiles discharge the
rate, slack, and threshold premises; no target list bound is assumed. -/
namespace Whir.JohnsonListNumerics

/-- The relaxed second-moment denominator is positive, and its corresponding
list-size estimate is at most `2^32`, at the minimum admitted rate and slack. -/
theorem johnson_bound_le_two_pow32 (N d t : ℕ) (hN : 0 < N)
    (rho alpha : ℚ) (hrho : rho = (d : ℚ) / N)
    (hrate : (1 / 2^26 : ℚ) ≤ rho) (halpha : 0 ≤ alpha)
    (hgap : rho / 64 ≤ alpha^2 - rho)
    (hthreshold : (N : ℚ) * alpha ≤ t) :
    (N : ℚ) * d < (t : ℚ)^2 ∧
      ((N : ℚ) * (N - (d : ℚ))) / ((t : ℚ)^2 - N * d) ≤ 2^32 := by
  have hNpos : (0 : ℚ) < N := by exact_mod_cast hN
  have hNzero : (N : ℚ) ≠ 0 := ne_of_gt hNpos
  have hr : rho * N = (d : ℚ) := (eq_div_iff hNzero).mp hrho
  have hsquare : ((N : ℚ) * alpha)^2 ≤ (t : ℚ)^2 :=
    pow_le_pow_left₀ (mul_nonneg hNpos.le halpha) hthreshold 2
  have hgapLow : (1 / 2^32 : ℚ) ≤ alpha^2 - rho := by
    norm_num at hrate ⊢
    linarith
  have hscale := mul_le_mul_of_nonneg_left hgapLow (sq_nonneg (N : ℚ))
  have hdenLow : (N : ℚ)^2 / 2^32 ≤ (t : ℚ)^2 - N * d := by
    have hrN : (N : ℚ) * d = rho * N^2 := by rw [← hr]; ring
    rw [hrN]
    nlinarith only [hsquare, hscale]
  have hden : 0 < (t : ℚ)^2 - N * d :=
    lt_of_lt_of_le (div_pos (sq_pos_of_pos hNpos) (by norm_num)) hdenLow
  refine ⟨sub_pos.mp hden, (div_le_iff₀ hden).mpr ?_⟩
  have hdnonneg : (0 : ℚ) ≤ (N : ℚ) * d := by positivity
  nlinarith

/-- Instantiates the proved interleaved RS Johnson bound. All lanes share the
same evaluation domain; there is no extra row-count factor. -/
theorem interleaved_candidates_card_le_two_pow32
    {F : Type*} [Field F] [DecidableEq F] [Fintype F] {lanes k : ℕ}
    (domain : Finset F) (oracle : ↥domain → Fin lanes → F) (t : ℕ)
    (hN : 0 < domain.card) (hk : 0 < k) (hd : k - 1 ≤ domain.card)
    (rho alpha : ℚ) (hrho : rho = ((k - 1 : ℕ) : ℚ) / domain.card)
    (hrate : (1 / 2^26 : ℚ) ≤ rho) (halpha : 0 ≤ alpha)
    (hgap : rho / 64 ≤ alpha^2 - rho)
    (hthreshold : (domain.card : ℚ) * alpha ≤ t) :
    (CodingBounds.candidates
      (fun v : Fin lanes → Fin k → F => fun x : ↥domain =>
        CodingBounds.interleavedEncode v x) oracle t).card ≤ 2^32 := by
  have hnum := johnson_bound_le_two_pow32 domain.card (k-1) t hN
    rho alpha hrho hrate halpha hgap hthreshold
  have hlist := CodingBounds.interleaved_candidates_card domain oracle t hk hd hnum.1
  have hfinal := hlist.trans hnum.2
  exact_mod_cast hfinal

end Whir.JohnsonListNumerics
