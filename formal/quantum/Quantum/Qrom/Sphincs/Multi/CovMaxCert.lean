module

public import Quantum.Qrom.Sphincs.Multi.CovMaxUser
public import Quantum.Qrom.Sphincs.Multi.CovMaxTab
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# From the certificates to the bounds of one user

* `exp_le_expUB`: the rational exponential bound of `CovMaxTab`.
* `tsum_slope_le`: the cut part `Σ_m slope_m · weight_m · ρ^m / m!` of the Poissonized exponential
  moment, through the tables up to the cut and a geometric tail beyond it.
* `loadMean_le_general`: the mean product of the load factors over the uniform index stream is
  at most `e^{K D + 2η}`, from `loadSum_poisson`, the Poisson lower tail
  (`sum_pow_div_factorial_le`, `chernoff_le`) and `e^{-ρ} G ≤ 1 + D`.
* `loadMean_le`, `binomTail_le`: the two constants of a certified parameter set `P`,
  `E Π_idx loadFactor ≤ e^κ` and `2^128 · E[coverProb · 1{load > k0}] ≤ β`.
-/

open Finset Nat
open scoped ENNReal
open Sphincs (signatureLimit indexBits)
open Quantum.Sphincs (coverProb binomMean binomMean_le one_sub_pow_le coverProb_nonneg
  coverProb_le_one)

namespace Quantum.Qrom.Sphincs.Multi

/-! ## Exponential bounds -/

theorem exp_le_expTaylor {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ expTaylor t := by
  have h := Real.exp_bound' (x := (t : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
    (n := 8) (by norm_num)
  refine h.trans (le_of_eq ?_)
  simp only [expTaylor]
  push_cast
  norm_num

theorem exp_le_expUB (a b : ℕ) (hb : 0 < b) : Real.exp ((a : ℝ) / b) ≤ expUB a b := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  set t : ℚ := ((a % b : ℕ) : ℚ) / ((2 * b : ℕ) : ℚ) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    have := Nat.mod_lt a hb
    exact_mod_cast (by omega : a % b ≤ 2 * b)
  have hsplit : (a : ℝ) / b = ((a / b : ℕ) : ℝ) * 1 + ((2 : ℕ) : ℝ) * (t : ℝ) := by
    have h' : ((b * (a / b) + a % b : ℕ) : ℝ) = a := by exact_mod_cast Nat.div_add_mod a b
    rw [← h', ht]
    push_cast
    field_simp
  have he : Real.exp 1 ≤ ((27182818286 / 10 ^ 10 : ℚ) : ℝ) := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  rw [hsplit, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, expUB, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_pow]
  exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le he _)
    (pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_expTaylor ht0 ht1) 2) (by positivity)
    (pow_nonneg (le_trans (Real.exp_pos 1).le he) _)

/-! ## The cut part of the exponential moment -/

/-- **The cut part**: up to the cut through `A ≥ coverProb · ρ^m / m! / loadCap` and
`X ≥ e^{s loadCap}`, beyond it a geometric tail of ratio `ρ / (k0 + 2)`. -/
theorem tsum_slope_le {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) {k0 : ℕ} (hk0 : 1 ≤ k0)
    (hρk : ρ < k0 + 2) {A X : ℕ → ℝ} {gk : ℝ}
    (hA : ∀ m ∈ Ico 1 (k0 + 1), (coverProb m : ℝ) * ρ ^ m / m ! / loadCap m ≤ A m)
    (hX : ∀ m ∈ Ico 1 (k0 + 1), Real.exp (s * loadCap m) ≤ X m)
    (hg : ρ ^ (k0 + 1) / (k0 + 1)! ≤ gk) :
    ∑' m, ENNReal.ofReal (expSlope s (capAt k0 m) * loadWeight k0 m * (ρ ^ m / m !)) ≤
      ENNReal.ofReal (∑ m ∈ Ico 1 (k0 + 1), (X m - 1) * A m +
        (X k0 - 1) * gk / (1 - ρ / (k0 + 2))) := by
  set f : ℕ → ℝ := fun m ↦ expSlope s (capAt k0 m) * loadWeight k0 m * (ρ ^ m / m !) with hf
  have hf0 : ∀ m, 0 ≤ f m := fun m ↦ mul_nonneg (mul_nonneg
    (expSlope_nonneg hs (capAt_nonneg k0 m)) (loadWeight_nonneg k0 m)) (by positivity)
  have hk0mem : k0 ∈ Ico 1 (k0 + 1) := mem_Ico.2 ⟨hk0, Nat.lt_succ_self k0⟩
  have hX1 : ∀ m ∈ Ico 1 (k0 + 1), 1 ≤ X m := fun m hm ↦
    (Real.one_le_exp (mul_nonneg hs (loadCap_nonneg m))).trans (hX m hm)
  -- up to the cut
  have hlow : ∑ m ∈ range (k0 + 1), f m ≤ ∑ m ∈ Ico 1 (k0 + 1), (X m - 1) * A m := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have hc0 : capAt k0 0 = 0 := by
      rw [capAt, show loadCap 0 = 0 by simp [loadCap]]
      exact min_eq_left (loadCap_nonneg k0)
    have hf00 : f 0 = 0 := by simp only [hf, hc0, expSlope, mul_zero, div_zero, zero_mul]
    rw [hf00, zero_add]
    refine Finset.sum_le_sum fun m hm ↦ ?_
    have hmk : m ≤ k0 := Nat.lt_succ_iff.1 (mem_Ico.1 hm).2
    have hu : 0 < loadCap m := by
      have : (0 : ℝ) < m := Nat.cast_pos.2 (mem_Ico.1 hm).1
      unfold loadCap; positivity
    have hcap : capAt k0 m = loadCap m := min_eq_left (loadCap_mono hmk)
    have hw : loadWeight k0 m = coverProb m := by
      unfold loadWeight
      split_ifs
      rfl
    have hfm : f m = (Real.exp (s * loadCap m) - 1) *
        ((coverProb m : ℝ) * ρ ^ m / m ! / loadCap m) := by
      simp only [hf, hcap, hw, expSlope]
      ring
    have hc : (0 : ℝ) ≤ coverProb m := by exact_mod_cast coverProb_nonneg m
    rw [hfm]
    exact mul_le_mul (by linarith [hX m hm]) (hA m hm) (by positivity) (by linarith [hX1 m hm])
  -- beyond the cut
  have hθ : 0 < loadCap k0 := by
    have : (0 : ℝ) < k0 := Nat.cast_pos.2 hk0
    unfold loadCap; positivity
  have hq0 : 0 ≤ ρ / (k0 + 2) := by positivity
  have hq1 : ρ / (k0 + 2) < 1 := (div_lt_one (by positivity)).2 hρk
  have hg0 : 0 ≤ gk := le_trans (by positivity) hg
  have htail : ∀ j, f (j + (k0 + 1)) ≤ (X k0 - 1) * gk * (ρ / (k0 + 2)) ^ j := fun j ↦ by
    have hcap : capAt k0 (j + (k0 + 1)) = loadCap k0 := min_eq_right (loadCap_mono (by omega))
    have hw : loadWeight k0 (j + (k0 + 1)) = loadCap k0 := by
      unfold loadWeight
      split_ifs <;> first | rfl | omega
    have hfac : ((k0 + 1)! : ℝ) * ((k0 : ℝ) + 2) ^ j ≤ ((j + (k0 + 1))! : ℝ) := by
      have h := Nat.factorial_mul_pow_le_factorial (m := k0 + 1) (n := j)
      rw [Nat.add_comm (k0 + 1) j] at h
      exact_mod_cast (by simpa [Nat.add_assoc] using h)
    have hpow : ρ ^ (j + (k0 + 1)) / ((j + (k0 + 1))! : ℝ) ≤ gk * (ρ / (k0 + 2)) ^ j := by
      calc ρ ^ (j + (k0 + 1)) / ((j + (k0 + 1))! : ℝ)
          ≤ ρ ^ (j + (k0 + 1)) / (((k0 + 1)! : ℝ) * ((k0 : ℝ) + 2) ^ j) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
        _ = ρ ^ (k0 + 1) / (k0 + 1)! * (ρ / (k0 + 2)) ^ j := by
            rw [pow_add, div_pow]
            field_simp
        _ ≤ gk * (ρ / (k0 + 2)) ^ j := mul_le_mul_of_nonneg_right hg (by positivity)
    have hfm : f (j + (k0 + 1)) =
        (Real.exp (s * loadCap k0) - 1) * (ρ ^ (j + (k0 + 1)) / ((j + (k0 + 1))! : ℝ)) := by
      simp only [hf, hcap, hw, expSlope]
      rw [div_mul_cancel₀ _ hθ.ne']
    rw [hfm, mul_assoc]
    exact mul_le_mul (by linarith [hX k0 hk0mem]) hpow (by positivity)
      (by linarith [hX1 k0 hk0mem])
  have hsplit := Summable.sum_add_tsum_nat_add' (f := fun m ↦ ENNReal.ofReal (f m)) (k := k0 + 1)
    ENNReal.summable
  calc ∑' m, ENNReal.ofReal (f m)
      = ∑ m ∈ range (k0 + 1), ENNReal.ofReal (f m) +
          ∑' j, ENNReal.ofReal (f (j + (k0 + 1))) := hsplit.symm
    _ ≤ ENNReal.ofReal (∑ m ∈ range (k0 + 1), f m) +
          ∑' j, ENNReal.ofReal ((X k0 - 1) * gk) * ENNReal.ofReal (ρ / (k0 + 2)) ^ j := by
        rw [ENNReal.ofReal_sum_of_nonneg fun m _ ↦ hf0 m]
        gcongr with j
        rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (mul_nonneg
          (by linarith [hX1 k0 hk0mem]) hg0)]
        exact ENNReal.ofReal_le_ofReal (htail j)
    _ = ENNReal.ofReal (∑ m ∈ range (k0 + 1), f m) +
          ENNReal.ofReal ((X k0 - 1) * gk / (1 - ρ / (k0 + 2))) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ hq0, ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (mul_nonneg (by linarith [hX1 k0 hk0mem]) hg0),
          div_eq_mul_inv ((X k0 - 1) * gk)]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add (sum_nonneg fun m _ ↦ hf0 m)
          (div_nonneg (mul_nonneg (by linarith [hX1 k0 hk0mem]) hg0) (by linarith))]
        exact ENNReal.ofReal_le_ofReal (add_le_add hlow le_rfl)

/-- **The Poissonized moment**: `e^{-ρ} Σ_m loadFactor_m ρ^m / m! ≤ 1 + E D` from `e^{-ρ} ≤ E` and
the cut part at most `D`. -/
theorem expMoment_le {s ρ E D : ℝ} (hs : 0 ≤ s) (hρ : 0 ≤ ρ) (k0 : ℕ) (hE : Real.exp (-ρ) ≤ E)
    (hD : 0 ≤ D)
    (hT : ∑' m, ENNReal.ofReal (expSlope s (capAt k0 m) * loadWeight k0 m * (ρ ^ m / m !)) ≤
      ENNReal.ofReal D) :
    ENNReal.ofReal (Real.exp (-ρ)) *
        ∑' m, ENNReal.ofReal (loadFactor s k0 m) * ENNReal.ofReal (ρ ^ m / m !) ≤
      ENNReal.ofReal (1 + E * D) := by
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
  have hpt : ∀ m, ENNReal.ofReal (loadFactor s k0 m) * ENNReal.ofReal (ρ ^ m / m !) =
      ENNReal.ofReal (ρ ^ m / m !) +
        ENNReal.ofReal (expSlope s (capAt k0 m) * loadWeight k0 m * (ρ ^ m / m !)) := fun m ↦ by
    have hq : 0 ≤ ρ ^ m / m ! := by positivity
    have ha : 0 ≤ expSlope s (capAt k0 m) * loadWeight k0 m * (ρ ^ m / m !) :=
      mul_nonneg (mul_nonneg (expSlope_nonneg hs (capAt_nonneg k0 m)) (loadWeight_nonneg k0 m)) hq
    rw [← ENNReal.ofReal_mul' hq, ← ENNReal.ofReal_add hq ha, loadFactor]
    congr 1
    ring
  simp only [hpt]
  rw [ENNReal.tsum_add, tsum_ofReal_pow_div_factorial hρ, mul_add,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    ENNReal.ofReal_add zero_le_one (mul_nonneg hE0 hD), ENNReal.ofReal_mul hE0]
  gcongr

/-! ## The Poisson lower tail -/

theorem exp_neg_mul_one_add_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.exp (-ε) * (1 + ε) ≤ 1 - (ε ^ 2 / 2 - 13 / 18 * ε ^ 3 - 2 / 9 * ε ^ 4) := by
  have h := Real.exp_bound (x := -ε) (by rw [abs_neg, abs_of_nonneg hε0]; exact hε1)
    (n := 3) (by norm_num)
  have h' := (abs_le.1 h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_nonneg hε0] at h'
  norm_num [Nat.factorial] at h'
  have hle : Real.exp (-ε) ≤ 1 - ε + ε ^ 2 / 2 + 2 / 9 * ε ^ 3 := by nlinarith
  calc Real.exp (-ε) * (1 + ε) ≤ (1 - ε + ε ^ 2 / 2 + 2 / 9 * ε ^ 3) * (1 + ε) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
    _ = _ := by ring

/-- **The Poisson lower tail at mean `N (1 + ε)`**. -/
theorem chernoff_le (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.exp (-(N * (1 + ε))) * ((N * (1 + ε) / N) ^ N * Real.exp N) ≤
      Real.exp (-((ε ^ 2 / 2 - 13 / 18 * ε ^ 3 - 2 / 9 * ε ^ 4) * N)) := by
  set ζ := ε ^ 2 / 2 - 13 / 18 * ε ^ 3 - 2 / 9 * ε ^ 4
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hb := exp_neg_mul_one_add_le hε0 hε1
  have hb0 : 0 ≤ Real.exp (-ε) * (1 + ε) := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hζ : 1 - ζ ≤ Real.exp (-ζ) := by linarith [Real.add_one_le_exp (-ζ)]
  have h1 : (N : ℝ) * (1 + ε) / N = 1 + ε := by field_simp
  have h2 : Real.exp (-(N * (1 + ε))) * Real.exp N = Real.exp (-ε) ^ N := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  calc Real.exp (-(N * (1 + ε))) * ((N * (1 + ε) / N) ^ N * Real.exp N)
      = (1 + ε) ^ N * (Real.exp (-(N * (1 + ε))) * Real.exp N) := by rw [h1]; ring
    _ = (Real.exp (-ε) * (1 + ε)) ^ N := by rw [h2, mul_pow, mul_comm]
    _ ≤ (1 - ζ) ^ N := pow_le_pow_left₀ hb0 hb N
    _ ≤ Real.exp (-ζ) ^ N := pow_le_pow_left₀ (hb0.trans hb) hζ N
    _ = Real.exp (-(ζ * N)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **The mean product over the loads**, Poissonized: `≤ e^{K D + 2η}`. -/
theorem loadMean_le_general {H : ℕ → ℝ≥0∞} (hH : Monotone H) {N K : ℕ} (hK : 0 < K)
    (hN : 0 < N) {ρ η D : ℝ} (hρ : 0 ≤ ρ) (hKρ : (N : ℝ) ≤ K * ρ)
    (hη : Real.exp (-(K * ρ)) * ((K * ρ / N) ^ N * Real.exp N) ≤ η) (hη2 : η ≤ 1 / 2)
    (hD : 0 ≤ D)
    (hG : ENNReal.ofReal (Real.exp (-ρ)) * ∑' m, H m * ENNReal.ofReal (ρ ^ m / m !) ≤
      ENNReal.ofReal (1 + D)) :
    loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N ≤ ENNReal.ofReal (Real.exp (K * D + 2 * η)) := by
  have hP := loadSum_poisson H hH N K hK hρ
  have hη0 : Real.exp (-(K * ρ)) * ∑ i ∈ range N, ((K : ℝ) * ρ) ^ i / i ! ≤ η :=
    (mul_le_mul_of_nonneg_left (sum_pow_div_factorial_le hN hKρ) (Real.exp_pos _).le).trans hη
  have hηpos : 0 ≤ η := le_trans (mul_nonneg (Real.exp_pos _).le
    (sum_nonneg fun i _ ↦ by positivity)) hη0
  have hpos : 0 < 1 - η := by linarith
  have h1 : ENNReal.ofReal (1 - η) * (loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N) ≤
      ENNReal.ofReal (Real.exp (K * D)) :=
    calc ENNReal.ofReal (1 - η) * (loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N)
        ≤ ENNReal.ofReal (1 - Real.exp (-(K * ρ)) * ∑ i ∈ range N, ((K : ℝ) * ρ) ^ i / i !) *
            (loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N) := by
          gcongr
      _ ≤ _ := hP
      _ ≤ ENNReal.ofReal (1 + D) ^ K := by gcongr
      _ = ENNReal.ofReal ((1 + D) ^ K) := (ENNReal.ofReal_pow (by linarith) K).symm
      _ ≤ ENNReal.ofReal (Real.exp (K * D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.exp_nat_mul]
          exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp D]) K
  have h2 : loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N ≤
      ENNReal.ofReal (Real.exp (K * D)) / ENNReal.ofReal (1 - η) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h1
  refine h2.trans ?_
  rw [← ENNReal.ofReal_div_of_pos hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hpos, Real.exp_add, mul_assoc]
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * η)) hpos.le
  have h3 : 1 ≤ Real.exp (2 * η) * (1 - η) := by nlinarith
  have hK0 := Real.exp_pos (K * D)
  calc Real.exp (K * D) = Real.exp (K * D) * 1 := (mul_one _).symm
    _ ≤ Real.exp (K * D) * (Real.exp (2 * η) * (1 - η)) := mul_le_mul_of_nonneg_left h3 hK0.le

/-! ## The constants of a certified parameter set -/

theorem cast_two_pow_indexBits : ((2 ^ indexBits : ℕ) : ℝ) = 2 ^ 26 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem poisRate_mul : ((2 ^ indexBits : ℕ) : ℝ) * (poisRate : ℝ) =
    (signatureLimit : ℝ) * (1 + 1 / 2 ^ 13) := by
  rw [cast_two_pow_indexBits, poisRate]
  push_cast
  ring

theorem exp_neg_poisRate_le : Real.exp (-(poisRate : ℝ)) ≤ eHat := by
  have hρ0 : (0 : ℝ) ≤ poisRate := by exact_mod_cast poisRate_pos.le
  have h1 := Real.sum_le_exp_of_nonneg hρ0 60
  have h2 : (0 : ℝ) < ∑ i ∈ range 60, (poisRate : ℝ) ^ i / i ! :=
    Finset.sum_pos' (fun i _ ↦ by positivity) ⟨0, by simp, by simp⟩
  have h3 : ((1 / ∑ i ∈ range 60, poisRate ^ i / (i ! : ℚ) : ℚ) : ℝ) ≤ eHat := by
    exact_mod_cast eHat_cert
  push_cast at h3
  rw [Real.exp_neg]
  calc (Real.exp poisRate)⁻¹ ≤ (∑ i ∈ range 60, (poisRate : ℝ) ^ i / i !)⁻¹ := inv_anti₀ h2 h1
    _ = 1 / ∑ i ∈ range 60, (poisRate : ℝ) ^ i / i ! := (one_div _).symm
    _ ≤ eHat := h3

theorem poisTail_le :
    Real.exp (-(((2 ^ indexBits : ℕ) : ℝ) * poisRate)) *
        ((((2 ^ indexBits : ℕ) : ℝ) * poisRate / signatureLimit) ^ signatureLimit *
          Real.exp signatureLimit) ≤ etaHat := by
  rw [poisRate_mul]
  refine (chernoff_le signatureLimit (by decide) (by positivity) (by norm_num)).trans ?_
  have hc : ((1 : ℝ) / 2 ^ 13) ^ 2 / 2 - 13 / 18 * (1 / 2 ^ 13) ^ 3 - 2 / 9 * (1 / 2 ^ 13) ^ 4 =
      (chernoffRate : ℝ) := by
    rw [chernoffRate]
    push_cast
    ring
  rw [hc]
  have hz0 : (0 : ℝ) ≤ chernoffRate * signatureLimit := by
    have : (0 : ℚ) ≤ chernoffRate := by rw [chernoffRate]; norm_num
    positivity
  have h1 := Real.sum_le_exp_of_nonneg hz0 40
  have h2 : (0 : ℝ) < ∑ i ∈ range 40, ((chernoffRate : ℝ) * signatureLimit) ^ i / i ! :=
    Finset.sum_pos' (fun i _ ↦ by positivity) ⟨0, by simp, by simp⟩
  have h3 : ((1 / ∑ i ∈ range 40, (chernoffRate * signatureLimit) ^ i / (i ! : ℚ) : ℚ) : ℝ) ≤
      etaHat := by
    exact_mod_cast etaHat_cert
  push_cast at h3
  rw [Real.exp_neg]
  calc (Real.exp (chernoffRate * signatureLimit))⁻¹
      ≤ (∑ i ∈ range 40, ((chernoffRate : ℝ) * signatureLimit) ^ i / i !)⁻¹ := inv_anti₀ h2 h1
    _ = 1 / ∑ i ∈ range 40, ((chernoffRate : ℝ) * signatureLimit) ^ i / i ! := (one_div _).symm
    _ ≤ etaHat := h3

theorem etaHat_le_half_real : (etaHat : ℝ) ≤ 1 / 2 := by
  have h : ((etaHat : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 etaHat_le_half
  push_cast at h
  exact h

/-- **The load factors of a certified parameter set**: their mean product over the index stream
of one user is at most `e^κ`. -/
theorem loadMean_le (P : CovParam) (hP : P.Cert) :
    loadSum (fun m ↦ ENNReal.ofReal (loadFactor ((P.lam : ℝ) * 2 ^ 102) P.k0 m))
        (Fin signatureLimit) (2 ^ indexBits) / ((2 ^ indexBits : ℕ) : ℝ≥0∞) ^ signatureLimit ≤
      ENNReal.ofReal (Real.exp P.kap) := by
  obtain ⟨hlam, hk20, hk99, hkap, -⟩ := hP
  have hlamR : (0 : ℝ) < P.lam := by
    rw [CovParam.lam]
    push_cast
    have : (0 : ℝ) < P.lamN := Nat.cast_pos.2 hlam
    positivity
  set s : ℝ := (P.lam : ℝ) * 2 ^ 102 with hsdef
  have hs : 0 ≤ s := by positivity
  have hρ0 : (0 : ℝ) ≤ poisRate := by exact_mod_cast poisRate_pos.le
  have hρk : (poisRate : ℝ) < P.k0 + 2 := by
    have h1 : (poisRate : ℝ) < 22 := by exact_mod_cast poisRate_lt
    have h2 : (20 : ℝ) ≤ P.k0 := by exact_mod_cast hk20
    linarith
  set X : ℕ → ℝ := fun m ↦ expUB (P.lamN * m ^ 24) (2 ^ P.lamE * 2 ^ 138) with hXdef
  have hX : ∀ m ∈ Ico 1 (P.k0 + 1), Real.exp (s * loadCap m) ≤ X m := fun m _ ↦ by
    have he : s * loadCap m =
        ((P.lamN * m ^ 24 : ℕ) : ℝ) / ((2 ^ P.lamE * 2 ^ 138 : ℕ) : ℝ) := by
      rw [hsdef, CovParam.lam, loadCap]
      push_cast
      field_simp
      ring
    rw [he]
    exact exp_le_expUB _ _ (by positivity)
  have hA : ∀ m ∈ Ico 1 (P.k0 + 1),
      (coverProb m : ℝ) * (poisRate : ℝ) ^ m / m ! / loadCap m ≤ aT m := fun m hm ↦ by
    have h := aT_cert m (by have := (mem_Ico.1 hm).2; omega) (mem_Ico.1 hm).1
    have h' : ((coverProb m * poisRate ^ m / (m ! : ℚ) / ((m : ℚ) ^ 24 / 2 ^ 240) : ℚ) : ℝ) ≤
        aT m := by exact_mod_cast h
    push_cast at h'
    rw [loadCap]
    exact h'
  have hg : (poisRate : ℝ) ^ (P.k0 + 1) / (P.k0 + 1)! ≤ gT (P.k0 + 1) := by
    have h := gT_cert (P.k0 + 1) (by omega)
    have h' : ((poisRate ^ (P.k0 + 1) / ((P.k0 + 1)! : ℚ) : ℚ) : ℝ) ≤ gT (P.k0 + 1) := by
      exact_mod_cast h
    push_cast at h'
    exact h'
  have hT := tsum_slope_le hs hρ0 (by omega : 1 ≤ P.k0) hρk hA hX hg
  set D : ℝ := ∑ m ∈ Ico 1 (P.k0 + 1), (X m - 1) * aT m +
    (X P.k0 - 1) * gT (P.k0 + 1) / (1 - (poisRate : ℝ) / (P.k0 + 2)) with hDdef
  have hX1 : ∀ m ∈ Ico 1 (P.k0 + 1), 1 ≤ X m := fun m hm ↦
    (Real.one_le_exp (mul_nonneg hs (loadCap_nonneg m))).trans (hX m hm)
  have hA0 : ∀ m ∈ Ico 1 (P.k0 + 1), (0 : ℝ) ≤ aT m := fun m hm ↦ by
    refine le_trans ?_ (hA m hm)
    have := Quantum.Sphincs.coverProb_nonneg m
    have : (0 : ℝ) ≤ coverProb m := by exact_mod_cast this
    have := loadCap_nonneg m
    positivity
  have hD0 : 0 ≤ D := by
    have hk0mem : P.k0 ∈ Ico 1 (P.k0 + 1) := mem_Ico.2 ⟨by omega, Nat.lt_succ_self _⟩
    have hq : 0 < 1 - (poisRate : ℝ) / (P.k0 + 2) := by
      rw [sub_pos, div_lt_one (by positivity)]
      exact hρk
    have hg0 : (0 : ℝ) ≤ gT (P.k0 + 1) := le_trans (by positivity) hg
    refine add_nonneg (sum_nonneg fun m hm ↦ mul_nonneg (by linarith [hX1 m hm]) (hA0 m hm)) ?_
    exact div_nonneg (mul_nonneg (by linarith [hX1 _ hk0mem]) hg0) hq.le
  have hE0 : (0 : ℝ) ≤ eHat := by
    have : (0 : ℚ) ≤ eHat := by rw [eHat]; norm_num
    exact_mod_cast this
  have hG := expMoment_le hs hρ0 P.k0 exp_neg_poisRate_le hD0 hT
  have hH : Monotone fun m ↦ ENNReal.ofReal (loadFactor s P.k0 m) := fun a b h ↦
    ENNReal.ofReal_le_ofReal (loadFactor_mono hs P.k0 h)
  have hKρ : (signatureLimit : ℝ) ≤ ((2 ^ indexBits : ℕ) : ℝ) * poisRate := by
    rw [poisRate_mul]
    have : (0 : ℝ) ≤ signatureLimit := Nat.cast_nonneg _
    nlinarith
  have hmain := loadMean_le_general hH (N := signatureLimit) (K := 2 ^ indexBits)
    (by positivity) (by decide) hρ0 hKρ poisTail_le etaHat_le_half_real
    (mul_nonneg hE0 hD0) hG
  refine hmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hk : ((P.kapExpr : ℚ) : ℝ) ≤ P.kap := by exact_mod_cast hkap
  have hk' : ((P.kapExpr : ℚ) : ℝ) = 2 ^ 26 * eHat * D + 2 * etaHat := by
    rw [CovParam.kapExpr, hDdef]
    push_cast
    rfl
  rw [cast_two_pow_indexBits]
  linarith

/-- **The binomial tail of a certified parameter set**:
`2^128 · E[coverProb · 1{load > k0}] ≤ β`. -/
theorem binomTail_le (P : CovParam) (hP : P.Cert) :
    ((binomMean signatureLimit (1 / 2 ^ 26) fun m ↦ if P.k0 < m then coverProb m else 0 : ℚ) :
      ℝ) * 2 ^ 128 ≤ P.bet := by
  obtain ⟨-, -, -, -, hbet⟩ := hP
  set c : ℕ → ℚ := fun m ↦ if P.k0 < m then coverProb m else 0 with hc
  have hc0 : ∀ m, 0 ≤ c m := fun m ↦ by
    simp only [hc]
    split_ifs
    · exact coverProb_nonneg m
    · exact le_rfl
  have hc1 : ∀ m, c m ≤ 1 := fun m ↦ by
    simp only [hc]
    split_ifs
    · exact coverProb_le_one m
    · norm_num
  have hp0 : (0 : ℚ) ≤ 1 / 2 ^ 26 := by norm_num
  have hp1 : (1 : ℚ) / 2 ^ 26 ≤ 1 := by norm_num
  have hB := binomMean_le signatureLimit 150 (by decide) hp0 hp1 (r := 1 / 8) (by norm_num)
    (by norm_num) (by norm_num [signatureLimit]) hc0 hc1
  have hF : (1 - 1 / 2 ^ 26 : ℚ) ^ (signatureLimit - 150) ≤ fHat :=
    (one_sub_pow_le _ 60 (by norm_num) (by decide) hp0 hp1).trans fHat_cert
  have hlow : 0 ≤ ∑ m ∈ range 150, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * c m :=
    sum_nonneg fun m _ ↦ mul_nonneg (by positivity) (hc0 m)
  have hsum : 2 ^ 128 * (fHat * ∑ m ∈ range 150,
      (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * c m) ≤
      ∑ m ∈ Ico (P.k0 + 1) 150, bT m := by
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ m ∈ range 150, 2 ^ 128 * (fHat * ((signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m *
          c m))
        ≤ ∑ m ∈ range 150, if P.k0 < m then bT m else 0 := sum_le_sum fun m hm ↦ by
          simp only [hc]
          split_ifs
          · exact bT_cert m (mem_range.1 hm)
          · simp
      _ = ∑ m ∈ Ico (P.k0 + 1) 150, bT m := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr (Finset.ext fun m ↦ ?_) fun _ _ ↦ rfl
          simp only [mem_filter, mem_range, mem_Ico]
          omega
  have hq : binomMean signatureLimit (1 / 2 ^ 26) c * 2 ^ 128 ≤ P.betExpr := by
    rw [CovParam.betExpr]
    have h1 := mul_le_mul_of_nonneg_right hB (show (0 : ℚ) ≤ 2 ^ 128 by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hF hlow
    have h3 := tHat_cert
    generalize (1 - 1 / 2 ^ 26 : ℚ) ^ (signatureLimit - 150) = X at h1 h2
    generalize (∑ m ∈ range 150, (signatureLimit.choose m : ℚ) * (1 / 2 ^ 26) ^ m * c m) = S
      at h1 h2 hsum
    generalize (signatureLimit.choose 150 : ℚ) * (1 / 2 ^ 26) ^ 150 = T at h1 h3
    generalize binomMean signatureLimit (1 / 2 ^ 26) c = B at h1 ⊢
    linarith
  have h := hq.trans hbet
  exact_mod_cast h

end Quantum.Qrom.Sphincs.Multi

end
