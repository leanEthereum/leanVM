module

public import Qrom.Leaf

@[expose] public section

/-!
# The QROM search bound

`Qrom.qrom_search_le`: a program that makes at most `t` calls to the quantum random oracle
`H : X → Y` and outputs, at each leaf `p`, a set `out p` of at most `k` inputs, outputs an input
`z` with `good z (H z)` with probability at most `λ (√6 t + 2 k)² tr ρ`, where every input has at
most `s` good values and `λ = s / |Y|`. The module `Qrom.Search` explains the proof.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]

/-- The weight of one leaf in the quantum random-oracle model, observed through the check, is the
weight of the compressed joint post-state against the tabulated check. -/
theorem sum_check_eq (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A)
    (Z : Finset X) (p : Σ u, W u) :
    ∑ H : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace.re *
          ({true} : Set Bool).indicator 1 (decide (∃ z ∈ Z, good z (H z)))) =
      ENNReal.ofReal ((((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (compressAll X Y *
          diagonal (tabWeight (checkFn good Z)) * compressAll X Y)) *
          ((compressedRuntime X Y).jointPost I x ρ p).matrix).trace.re) := by
  rw [← tabCompress_mul_diagonal_mul, ← sum_mul_trace_jointPost_additive_eq, Complex.re_sum]
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hterm : ∀ H : X → Y, (checkFn good Z H * ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
      ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace)).re =
      (if ∃ z ∈ Z, good z (H z) then 1 else 0) * ((Fintype.card Y : ℝ)⁻¹ ^ Fintype.card X *
        ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace.re) := by
    intro H
    have hc : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) =
        (((Fintype.card Y : ℝ)⁻¹ ^ Fintype.card X : ℝ) : ℂ) := by push_cast; rfl
    have hk : checkFn good Z H = (((if ∃ z ∈ Z, good z (H z) then 1 else 0 : ℝ)) : ℂ) := by
      unfold checkFn
      split_ifs <;> simp
    rw [hk, hc, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [hterm]
  rw [ENNReal.ofReal_sum_of_nonneg fun H _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hN.le) _) (SubState.trace_re_nonneg _))]
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  rw [Fintype.card_fun, Nat.cast_pow]
  by_cases h : ∃ z ∈ Z, good z (H z)
  · simp only [h, decide_true, Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply,
      mul_one, ↓reduceIte, one_mul]
    rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hN.le) _), ENNReal.ofReal_pow
      (inv_nonneg.mpr hN.le), ENNReal.ofReal_inv_of_pos hN, ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · simp [h]

variable [Nonempty Y]

/-- **The QROM search bound.** -/
theorem qrom_search_le (I : L.Interp) (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s)
    (t k : ℕ) (x : QuantumComp L (qromSpec X Y) W A) (hx : x.IsQueryBound fun _ ↦ t)
    (ρ : SubState A) (out : (Σ u, W u) → Finset X) (hout : ∀ p, (out p).card ≤ k) :
    qromEvalDistMap I x ρ (fun H p ↦ decide (∃ z ∈ out p, good z (H z))) {true} ≤
      ENNReal.ofReal (((s : ℝ) / Fintype.card Y) * (√6 * t + 2 * k) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  let _ : UniformAnswerMeasure (X →ₒ Y) := UniformAnswerMeasure.ofFiniteNonempty _
  set lam : ℝ := (s : ℝ) / Fintype.card Y with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set δ : ℝ := k * (2 * √lam) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set J := fun p : Σ u, W u ↦ ((compressedRuntime X Y).jointPost I x ρ p).matrix
  have hJ : ∀ p, (J p).PosSemidef := fun p ↦ ((compressedRuntime X Y).jointPost I x ρ p).posSemidef
  -- the weight of each leaf
  set R : (Σ u, W u) → ℝ := fun p ↦ ((((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (compressAll X Y *
      diagonal (tabWeight (checkFn good (out p))) * compressAll X Y)) * J p).trace.re)
  set b : (Σ u, W u) → ℝ := fun p ↦
    (conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ eventProj (searchEvent good)) (J p)).trace.re
  have hlhs : qromEvalDistMap I x ρ (fun H p ↦ decide (∃ z ∈ out p, good z (H z))) {true} =
      ∑' p, ENNReal.ofReal (R p) := by
    rw [qromEvalDistMap, sampledEvalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)]
    simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
      ← ENNReal.tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    exact tsum_congr fun p ↦ sum_check_eq good I x ρ (out p) p
  -- one leaf: `√R ≤ √b + δ √(tr J)`
  have hleaf : ∀ p, ENNReal.ofReal (R p) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (b p) ^ (2⁻¹ : ℝ) +
      ∑' j : ℕ, (if j = 0 then ENNReal.ofReal (δ ^ 2 * (J p).trace.re) else 0) ^ (2⁻¹ : ℝ) := by
    intro p
    rw [tsum_eq_single 0 fun j hj ↦ by simp [hj]]
    simp only [↓reduceIte]
    simp only [ENNReal.ofReal_rpow_inv_two]
    rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((sqrt_check_le good (out p) (hJ p)).trans ?_)
    refine add_le_add le_rfl ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    refine (norm_compress_orProj_sub_le good (out p) s hs).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hout p) (by positivity)
  have hsum := rpow_inv_two_tsum_le_of_le_add_tsum hleaf
  -- the event and the traces
  have hbad : ∑' p, ENNReal.ofReal (b p) ≤
      ENNReal.ofReal (6 * lam) * (t : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re := by
    refine (tsum_eventWeight_compressedRuntime_le I (searchEvent good) (searchEvent_empty good) t
      x hx ρ).trans ?_
    gcongr
    have hI := instability_searchEvent_le good s hs t
    have hne : (s : ℝ≥0∞) / Fintype.card Y ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top s) (by simp)
    have := (ENNReal.toReal_le_toReal (Database.instability_ne_top _ _) hne).mpr hI
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
    linarith
  have htr : ∑' p, ENNReal.ofReal (J p).trace.re ≤ ENNReal.ofReal ρ.matrix.trace.re := by
    have h := ((compressedRuntime X Y).run I x).isCPTNIFamily.tsum_ofReal_trace_re_le
      (ρ.prod (compressedRuntime X Y).init).posSemidef
    have htrace : (ρ.prod (compressedRuntime X Y).init).matrix.trace = ρ.matrix.trace := by
      simp [SubState.matrix_prod, Matrix.trace_kronecker, SubState.matrix_basis]
    rwa [htrace] at h
  have hrest : ∑' j : ℕ, (∑' p, (if j = 0 then ENNReal.ofReal (δ ^ 2 * (J p).trace.re)
      else 0)) ^ (2⁻¹ : ℝ) ≤ (ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^
        (2⁻¹ : ℝ) := by
    rw [tsum_eq_single 0 fun j hj ↦ by simp [hj]]
    simp only [↓reduceIte]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    simp only [ENNReal.ofReal_mul (sq_nonneg δ), ENNReal.tsum_mul_left]
    gcongr
  -- assemble
  have hfinal : (∑' p, ENNReal.ofReal (R p)) ^ (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (6 * lam) * (t : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
    hsum.trans (add_le_add (ENNReal.rpow_le_rpow hbad (by norm_num)) hrest)
  rw [hlhs]
  have hsq := ENNReal.rpow_le_rpow hfinal (z := 2) (by norm_num)
  rw [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_two] at hsq
  refine hsq.trans (le_of_eq ?_)
  -- the closed form
  have htr0 : 0 ≤ ρ.matrix.trace.re := SubState.trace_re_nonneg _
  have e1 : ENNReal.ofReal (6 * lam) * (t : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re =
      ENNReal.ofReal (6 * lam * t ^ 2 * ρ.matrix.trace.re) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 * lam * t ^ 2 by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 * lam by positivity),
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have e2 : ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re =
      ENNReal.ofReal (δ ^ 2 * ρ.matrix.trace.re) := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  rw [e1, e2, ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.sqrt_mul' _ htr0, Real.sqrt_mul' _ htr0, ← add_mul, mul_pow, Real.sq_sqrt htr0,
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _),
    Real.sqrt_sq hδ0, hδ]
  have h6 : √(6 : ℝ) * √lam * t + k * (2 * √lam) = √lam * (√6 * t + 2 * k) := by ring
  rw [h6, mul_pow, Real.sq_sqrt hlam0]

end Qrom
