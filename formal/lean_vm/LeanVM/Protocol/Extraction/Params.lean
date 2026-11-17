module

public import LeanVM.Protocol.Extraction.Defs
public import ArkLib.Data.CodingTheory.GuruswamiSudan.Correctness
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The natural Johnson threshold and the GS parameter certificate (proofs)

* `ceil_sqrt_eq_ceilSqrt`: `⌈√x⌉₊ = ceilSqrt x`.
* `johnsonThreshold_eq_real`: the natural `johnsonThreshold` equals its real form
  `⌈(√(D/n) + η)·n⌉₊` (`johnsonThresholdReal`, the form of `Statement/Extractor.lean` at
  `8e8e4d2f`, the slack's denominator now `2^30`).
* `gsNumVars_eq`, `gsNumConstraints_eq`, `gsPass_iff`: the closed forms are ArkLib's
  `numVars`, `numConstraints`, and the check is `GSParamCert`.
* `gsParamCert_gsParamsFor`: for message length `k > 1`, agreement `A ≤ n` with `A² > (k−1)·n`,
  the parameters `gsParamsFor k n A` are certified at radius `n − A`.
* `johnsonThreshold_bounds`: at every admissible shape (`16 ≤ μ ≤ 30`, `1 ≤ R ≤ 4`) the threshold
  is at most `n` and its square exceeds `D·n`, `D = 2^κ − 1 + 6` level 0's degree, so the
  decoder's parameters at message length `2^κ + 6` are certified.

Credits: ArkLib (github.com/Verified-zkEVM/ArkLib at `4dae3acff846125521b7b3998010885071746f16`,
Apache-2.0): `GSParamCert`, `paramsPassIntegerChecks_iff` (`GuruswamiSudan/{Executable,
Correctness}.lean`, Valerii Huhnin); `numVars`, `numConstraints`, `numVars_eq_of_gt_one`,
`card_constraintIndices`, `numVars_gt_numConstraints_of_mul_lt` (`GuruswamiSudan/Basic.lean`,
Stefano Rocca).
-/

namespace LeanVM.Extraction

open LeanVM.Parameters.Whir CompPoly.GuruswamiSudan GuruswamiSudan

public section

/-! ## `⌈√x⌉` -/

theorem le_ceilSqrt_mul_self (x : ℕ) : x ≤ ceilSqrt x * ceilSqrt x := by
  unfold ceilSqrt
  split
  · next h => exact h.ge
  · exact (Nat.lt_succ_sqrt x).le

theorem ceilSqrt_le {x y : ℕ} (h : x ≤ y * y) : ceilSqrt x ≤ y := by
  unfold ceilSqrt
  have hs := Nat.sqrt_le x
  split
  · next he =>
    by_contra hlt
    have : y * y < Nat.sqrt x * Nat.sqrt x := Nat.mul_self_lt_mul_self (not_le.mp hlt)
    omega
  · next he =>
    by_contra hlt
    have hle : y ≤ Nat.sqrt x := by omega
    have : y * y ≤ Nat.sqrt x * Nat.sqrt x := Nat.mul_self_le_mul_self hle
    omega

/-- `⌈√x⌉₊ = ceilSqrt x`. -/
theorem ceil_sqrt_eq_ceilSqrt (x : ℕ) : ⌈√(x : ℝ)⌉₊ = ceilSqrt x := by
  apply le_antisymm
  · rw [Nat.ceil_le]
    have h := le_ceilSqrt_mul_self x
    calc √(x : ℝ) ≤ √((ceilSqrt x : ℝ) * ceilSqrt x) := Real.sqrt_le_sqrt (by exact_mod_cast h)
      _ = ceilSqrt x := Real.sqrt_mul_self (Nat.cast_nonneg _)
  · rcases Nat.eq_zero_or_pos (ceilSqrt x) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hlt : (ceilSqrt x - 1) * (ceilSqrt x - 1) < x := by
        by_contra hge
        have := ceilSqrt_le (not_lt.mp hge)
        omega
      have : ceilSqrt x - 1 < ⌈√(x : ℝ)⌉₊ := by
        rw [Nat.lt_ceil, Real.lt_sqrt (Nat.cast_nonneg _), pow_two]
        exact_mod_cast hlt
      omega

/-! ## The threshold, real and natural -/

/-- The real-valued threshold, the statement's form before the extractor became computable
(`Statement/Extractor.lean` at `8e8e4d2f`) with the slack's denominator `2^30`, at level
0's degree `D = 2^κ − 1 + 6`. -/
@[expose] noncomputable def johnsonThresholdReal (μ R : ℕ) : ℕ :=
  let κ := μ - initialFold
  let n : ℕ := 2 ^ (κ + R)
  let D : ℕ := 2 ^ κ - 1 + initialFold
  let η : ℝ := ((johnsonSlack.getD (R - 1) []).getD (μ - minLogStack) 0 : ℝ) / (2 ^ 30 : ℕ)
  ⌈(√((D : ℝ) / n) + η) * n⌉₊

/-- `⌈y / c⌉₊ = ⌈⌈y⌉₊ / c⌉` for a positive natural `c`. -/
theorem ceil_div_natCast (y : ℝ) {c : ℕ} (hc : 0 < c) :
    ⌈y / c⌉₊ = (⌈y⌉₊ + c - 1) / c := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hc']
    have h1 : ⌈y⌉₊ ≤ (⌈y⌉₊ + c - 1) / c * c := by
      have := Nat.div_add_mod (⌈y⌉₊ + c - 1) c
      have := Nat.mod_lt (⌈y⌉₊ + c - 1) hc
      have := Nat.mul_comm c ((⌈y⌉₊ + c - 1) / c)
      omega
    calc y ≤ ⌈y⌉₊ := Nat.le_ceil y
      _ ≤ ((⌈y⌉₊ + c - 1) / c * c : ℕ) := by exact_mod_cast h1
      _ = ((⌈y⌉₊ + c - 1) / c : ℕ) * (c : ℝ) := by push_cast; ring
  · have hM : y ≤ ⌈y / c⌉₊ * c := by
      have := Nat.le_ceil (y / c)
      rwa [div_le_iff₀ hc'] at this
    have hN : ⌈y⌉₊ ≤ ⌈y / c⌉₊ * c := by
      rw [Nat.ceil_le]; exact_mod_cast hM
    rw [Nat.div_le_iff_le_mul_add_pred hc]
    have := Nat.mul_comm c ⌈y / c⌉₊
    omega

/-- The two forms of the threshold, for any slack `e` and `n > 0`. -/
theorem ceil_johnson_eq (D n e : ℕ) (hn : 0 < n) :
    ⌈(√((D : ℝ) / n) + (e : ℝ) / (2 ^ 30 : ℕ)) * n⌉₊ =
      (ceilSqrt (2 ^ 60 * D * n) + e * n + 2 ^ 30 - 1) / 2 ^ 30 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : √((D : ℝ) / n) * n = √((D : ℝ) * n) := by
    have h : (D : ℝ) * n = D / n * (n * n) := by field_simp
    rw [h, Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hn'.le), Real.sqrt_mul_self hn'.le]
  have hX : √(((2 ^ 60 * D * n : ℕ) : ℝ)) = 2 ^ 30 * √((D : ℝ) * n) := by
    rw [show ((2 ^ 60 * D * n : ℕ) : ℝ) = (2 ^ 30) ^ 2 * ((D : ℝ) * n) by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hexpr : (√((D : ℝ) / n) + (e : ℝ) / (2 ^ 30 : ℕ)) * n =
      (√(((2 ^ 60 * D * n : ℕ) : ℝ)) + ((e * n : ℕ) : ℝ)) / ((2 ^ 30 : ℕ) : ℝ) := by
    rw [hX, add_mul, hsq]
    push_cast
    field_simp
    norm_num
  rw [hexpr, ceil_div_natCast _ (by positivity), Nat.ceil_add_natCast (by positivity),
    ceil_sqrt_eq_ceilSqrt]

/-- **The natural threshold is the statement's real threshold.** -/
theorem johnsonThreshold_eq_real (μ R : ℕ) : johnsonThresholdReal μ R = johnsonThreshold μ R := by
  unfold johnsonThresholdReal johnsonThreshold johnsonSlackOf
  exact ceil_johnson_eq _ _ _ (by positivity)

/-! ## ArkLib's sizes and certificate -/

theorem gsNumVars_eq {k : ℕ} (hk : 1 < k) (W : ℕ) : gsNumVars k W = numVars k W := by
  rw [numVars_eq_of_gt_one hk]
  rfl

theorem gsNumConstraints_eq (n m : ℕ) : gsNumConstraints n m = numConstraints n m := by
  rw [numConstraints, card_constraintIndices]
  rfl

/-- **The integer check is ArkLib's certificate.** -/
theorem gsPass_iff {k : ℕ} (hk : 1 < k) (n e : ℕ) (params : GSExecParams) :
    gsPass k n e params = true ↔ GSParamCert k n e params := by
  rw [← paramsPassIntegerChecks_iff]
  unfold gsPass paramsPassIntegerChecks
  rw [gsNumVars_eq hk, gsNumConstraints_eq]

/-- The capacity inequality at `m = ⌊(D + 1)/(A² − D)⌋ + 1`, in natural numbers. -/
theorem capacity_core {D A m : ℕ} (hcap : D < A * A) (hm : m = (D + 1) / (A * A - D) + 1) :
    D * m * (m + 1) < (m * A - 1) * (m * A - 1 + 2) := by
  obtain ⟨y, hy⟩ : ∃ y, y = A * A - D := ⟨_, rfl⟩
  rw [← hy] at hm
  have hypos : 0 < y := by omega
  have hmy : D + 2 ≤ m * y := by
    have h1 := Nat.div_add_mod (D + 1) y
    have h2 := Nat.mod_lt (D + 1) hypos
    have h3 : m * y = y * ((D + 1) / y) + y := by rw [hm]; ring
    clear hy hm hcap
    generalize (D + 1) / y = q at h1 h3
    generalize (D + 1) % y = r at h1 h2
    omega
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hmy)
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; simp at hcap
    · exact h
  obtain ⟨t, ht⟩ : ∃ t, m * A = t + 1 := ⟨m * A - 1, by
    have := Nat.mul_le_mul hm1 hA
    omega⟩
  have hW : (m * A - 1) * (m * A - 1 + 2) + 1 = m * A * (m * A) := by
    rw [ht]; simp only [Nat.add_sub_cancel]; ring
  have hAA : A * A = y + D := by omega
  have key : D * m * (m + 1) + 1 < m * A * (m * A) := by
    have e1 : m * A * (m * A) = m * m * (A * A) := by ring
    rw [e1, hAA]
    have h2 : m * (D + 2) ≤ m * (m * y) := Nat.mul_le_mul_left m hmy
    nlinarith
  omega

/-- The capacity inequality at `m₀`. -/
theorem capacity_at_bound {k n A : ℕ} (hcap : (k - 1) * n < A * A) :
    (k - 1) * n * gsMultiplicityBoundAt k n A * (gsMultiplicityBoundAt k n A + 1) <
      (gsMultiplicityBoundAt k n A * A - 1) * (gsMultiplicityBoundAt k n A * A - 1 + 2) :=
  capacity_core hcap rfl

/-- At `m₀` the check passes. -/
theorem gsPass_bound {k n A : ℕ} (hk : 1 < k) (hA : A ≤ n) (hcap : (k - 1) * n < A * A) :
    gsPass k n (n - A) (gsParamsAt k n A (gsMultiplicityBoundAt k n A)) = true := by
  rw [gsPass_iff hk]
  have hApos : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; simp at hcap
    · exact h
  refine ⟨rfl, rfl, Nat.succ_pos _, ?_, ?_⟩
  · apply numVars_gt_numConstraints_of_mul_lt hk
    have h := capacity_at_bound hcap
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk.le, Nat.cast_one]
    rw [← hc]
    exact_mod_cast h
  · change gsMultiplicityBoundAt k n A * A - 1 < gsMultiplicityBoundAt k n A * (n - (n - A))
    rw [Nat.sub_sub_self hA]
    have : 0 < gsMultiplicityBoundAt k n A * A := Nat.mul_pos (Nat.succ_pos _) hApos
    omega

/-- **The decoder's parameters are certified** at radius `n − A`. -/
theorem gsParamCert_gsParamsFor {k n A : ℕ} (hk : 1 < k) (hA : A ≤ n)
    (hcap : (k - 1) * n < A * A) : GSParamCert k n (n - A) (gsParamsFor k n A) := by
  rw [← gsPass_iff hk]
  unfold gsParamsFor gsMultiplicityAt
  cases h : (List.range' 1 (gsMultiplicityBoundAt k n A)).find?
      (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)) with
  | none => exact gsPass_bound hk hA hcap
  | some m =>
    simp only [Option.getD_some]
    exact List.find?_some (p := fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)) h

/-! ## The admissible shapes -/

/-- At an admissible shape the threshold is at most `n` and its square exceeds `D·n`, `D` level
0's degree `2^κ − 1 + 6`, by kernel evaluation. -/
theorem johnsonThreshold_bounds {μ R : ℕ} (hμ : 16 ≤ μ ∧ μ ≤ 30) (hR : 1 ≤ R ∧ R ≤ 4) :
    johnsonThreshold μ R ≤ 2 ^ (μ - initialFold + R) ∧
      (2 ^ (μ - initialFold) + initialFold - 1) * 2 ^ (μ - initialFold + R) <
        johnsonThreshold μ R * johnsonThreshold μ R := by
  have h : ∀ R < 5, ∀ μ < 31, 1 ≤ R → 16 ≤ μ →
      johnsonThreshold μ R ≤ 2 ^ (μ - initialFold + R) ∧
        (2 ^ (μ - initialFold) + initialFold - 1) * 2 ^ (μ - initialFold + R) <
          johnsonThreshold μ R * johnsonThreshold μ R := by
    decide +kernel
  exact h R (by omega) μ (by omega) hR.1 hμ.1

end
end LeanVM.Extraction
