module

public import Qrom.Leaf
public import Qrom.OvBridge
public import Qrom.OvEvent

@[expose] public section

/-!
# The search bound for games with overrides

`Qrom.OvGame.ov_search_le`: in a game with overrides and side ports (`Qrom.OvGame`), averaged over
the random function `G`, a program with at most `n` calls in all outputs, at each leaf `p`, a set
`out p` of at most `k` inputs one of which satisfies `good z (G z)` with probability at most
`λ (√6 n + 2 k)² tr ρ`. The proof is that of `Qrom.qrom_search_le`, on the register
`B × (S × Database X Y)`, which reassociates to `(B × S) × Database X Y` for the per-leaf bound.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

/-! ## Reassociating the side state into the program register -/

section reassoc

variable {B S T : Type*} [Fintype B] [DecidableEq B] [Fintype S] [DecidableEq S] [Fintype T]
  [DecidableEq T]

theorem trace_submatrix_equiv' {m n : Type*} [Fintype m] [Fintype n] (A : Matrix n n ℂ)
    (e : m ≃ n) : (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact e.sum_comp fun i ↦ A i i

/-- Moving the side state from the runtime register to the program register. -/
def assocE (B S T : Type*) : (B × S) × T ≃ B × (S × T) := Equiv.prodAssoc B S T

theorem one_kronecker_one_kronecker_submatrix (M : Matrix T T ℂ) :
    ((1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ M)).submatrix (assocE B S T) (assocE B S T) =
      (1 : Matrix (B × S) (B × S) ℂ) ⊗ₖ M := by
  ext ⟨⟨b, s⟩, t⟩ ⟨⟨b', s'⟩, t'⟩
  simp only [submatrix_apply, assocE, Equiv.prodAssoc_apply, kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : b = b' <;> by_cases h2 : s = s' <;> simp [h1, h2]

theorem trace_one_kronecker_reassoc (M : Matrix T T ℂ) (J : Matrix (B × (S × T)) (B × (S × T)) ℂ) :
    (((1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ M)) * J).trace =
      (((1 : Matrix (B × S) (B × S) ℂ) ⊗ₖ M) *
        J.submatrix (assocE B S T) (assocE B S T)).trace := by
  rw [← one_kronecker_one_kronecker_submatrix, submatrix_mul_equiv, trace_submatrix_equiv']

theorem trace_conj_one_kronecker_reassoc (M : Matrix T T ℂ)
    (J : Matrix (B × (S × T)) (B × (S × T)) ℂ) :
    (conj ((1 : Matrix B B ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ M)) J).trace =
      (conj ((1 : Matrix (B × S) (B × S) ℂ) ⊗ₖ M)
        (J.submatrix (assocE B S T) (assocE B S T))).trace := by
  rw [conj_apply, conj_apply, ← one_kronecker_one_kronecker_submatrix, conjTranspose_submatrix,
    submatrix_mul_equiv, submatrix_mul_equiv, trace_submatrix_equiv']

end reassoc

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (g : OvGame X Y S P Res)
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)]
variable [Nonempty Y]

/-- The weight of one leaf, averaged over `G` and observed through the check, is the weight of the
compressed joint post-state against the tabulated check. -/
theorem sum_check_eq (I : L.Interp) (x : QuantumComp L (ovSpec X Y S P Res) W A)
    (ρ : SubState A) (Z : Finset X) (p : Σ u, W u) :
    ∑ G : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal ((g.sampled G).jointPost I x ρ p).matrix.trace.re *
          ({true} : Set Bool).indicator 1 (decide (∃ z ∈ Z, good z (G z)))) =
      ENNReal.ofReal ((((1 : Matrix p.1 p.1 ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ (compressAll X Y *
          diagonal (tabWeight (checkFn good Z)) * compressAll X Y))) *
          (g.compressed.jointPost I x ρ p).matrix).trace.re) := by
  rw [← tabCompress_mul_diagonal_mul, ← sum_mul_trace_jointPost_sampled_eq, Complex.re_sum]
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hterm : ∀ G : X → Y, (checkFn good Z G * ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
      ((g.sampled G).jointPost I x ρ p).matrix.trace)).re =
      (if ∃ z ∈ Z, good z (G z) then 1 else 0) * ((Fintype.card Y : ℝ)⁻¹ ^ Fintype.card X *
        ((g.sampled G).jointPost I x ρ p).matrix.trace.re) := by
    intro G
    have hc : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) =
        (((Fintype.card Y : ℝ)⁻¹ ^ Fintype.card X : ℝ) : ℂ) := by push_cast; rfl
    have hk : checkFn good Z G = (((if ∃ z ∈ Z, good z (G z) then 1 else 0 : ℝ)) : ℂ) := by
      unfold checkFn
      split_ifs <;> simp
    rw [hk, hc, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [hterm]
  rw [ENNReal.ofReal_sum_of_nonneg fun G _ ↦ mul_nonneg (by split_ifs <;> norm_num)
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hN.le) _) (SubState.trace_re_nonneg _))]
  refine Finset.sum_congr rfl fun G _ ↦ ?_
  rw [Fintype.card_fun, Nat.cast_pow]
  by_cases h : ∃ z ∈ Z, good z (G z)
  · simp only [h, decide_true, Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply,
      mul_one, ↓reduceIte, one_mul]
    rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hN.le) _), ENNReal.ofReal_pow
      (inv_nonneg.mpr hN.le), ENNReal.ofReal_inv_of_pos hN, ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · simp [h]

/-- **The search bound for games with overrides.** -/
theorem ov_search_le (I : L.Interp) (s : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ s)
    (n k : ℕ) (x : QuantumComp L (ovSpec X Y S P Res) W A) (hx : x.IsTotalQueryBound n)
    (ρ : SubState A) (out : (Σ u, W u) → Finset X) (hout : ∀ p, (out p).card ≤ k) :
    sampledEvalDistMap g.sampled I x ρ (fun G p ↦ decide (∃ z ∈ out p, good z (G z))) {true} ≤
      ENNReal.ofReal (((s : ℝ) / Fintype.card Y) * (√6 * n + 2 * k) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  let _ : UniformAnswerMeasure (X →ₒ Y) := UniformAnswerMeasure.ofFiniteNonempty _
  set lam : ℝ := (s : ℝ) / Fintype.card Y with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set δ : ℝ := k * (2 * √lam) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set J := fun p : Σ u, W u ↦ (g.compressed.jointPost I x ρ p).matrix
  have hJ : ∀ p, (J p).PosSemidef := fun p ↦ (g.compressed.jointPost I x ρ p).posSemidef
  set J' := fun p : Σ u, W u ↦ (J p).submatrix (assocE p.1 S (Database X Y))
    (assocE p.1 S (Database X Y))
  have hJ' : ∀ p, (J' p).PosSemidef := fun p ↦ (hJ p).submatrix _
  set R : (Σ u, W u) → ℝ := fun p ↦ ((((1 : Matrix p.1 p.1 ℂ) ⊗ₖ ((1 : Matrix S S ℂ) ⊗ₖ
      (compressAll X Y * diagonal (tabWeight (checkFn good (out p))) * compressAll X Y))) *
      J p).trace.re)
  set b : (Σ u, W u) → ℝ := fun p ↦ (conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ
      ((1 : Matrix S S ℂ) ⊗ₖ eventProj (searchEvent good))) (J p)).trace.re
  have hlhs : sampledEvalDistMap g.sampled I x ρ
      (fun G p ↦ decide (∃ z ∈ out p, good z (G z))) {true} = ∑' p, ENNReal.ofReal (R p) := by
    rw [sampledEvalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)]
    simp only [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
      ← ENNReal.tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
    exact tsum_congr fun p ↦ g.sum_check_eq good I x ρ (out p) p
  have hleaf : ∀ p, ENNReal.ofReal (R p) ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (b p) ^ (2⁻¹ : ℝ) +
      ∑' j : ℕ, (if j = 0 then ENNReal.ofReal (δ ^ 2 * (J p).trace.re) else 0) ^ (2⁻¹ : ℝ) := by
    intro p
    rw [tsum_eq_single 0 fun j hj ↦ by simp [hj]]
    simp only [↓reduceIte]
    simp only [ENNReal.ofReal_rpow_inv_two]
    rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    have hR : R p = ((((1 : Matrix (p.1 × S) (p.1 × S) ℂ) ⊗ₖ (compressAll X Y *
        diagonal (tabWeight (checkFn good (out p))) * compressAll X Y)) * J' p).trace.re) := by
      simp only [R, J', trace_one_kronecker_reassoc]
    have hb : b p = (conj ((1 : Matrix (p.1 × S) (p.1 × S) ℂ) ⊗ₖ
        eventProj (searchEvent good)) (J' p)).trace.re := by
      simp only [b, J', trace_conj_one_kronecker_reassoc]
    have htrJ : (J' p).trace = (J p).trace := trace_submatrix_equiv' _ _
    rw [hR, hb]
    refine ENNReal.ofReal_le_ofReal ((sqrt_check_le good (out p) (hJ' p)).trans ?_)
    refine add_le_add le_rfl ?_
    rw [htrJ, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hδ0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    refine (norm_compress_orProj_sub_le good (out p) s hs).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hout p) (by positivity)
  have hsum := rpow_inv_two_tsum_le_of_le_add_tsum hleaf
  have hbad : ∑' p, ENNReal.ofReal (b p) ≤
      ENNReal.ofReal (6 * lam) * (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re := by
    refine (g.tsum_eventWeight_compressed_le I (searchEvent good) (searchEvent_empty good) n x hx
      ρ).trans ?_
    gcongr
    have hI := instability_searchEvent_le good s hs (Fintype.card X)
    have hne : (s : ℝ≥0∞) / Fintype.card Y ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.natCast_ne_top s) (by simp)
    have := (ENNReal.toReal_le_toReal (Database.instability_ne_top _ _) hne).mpr hI
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
    linarith
  have htr : ∑' p, ENNReal.ofReal (J p).trace.re ≤ ENNReal.ofReal ρ.matrix.trace.re := by
    have h := (g.compressed.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le
      (ρ.prod g.compressed.init).posSemidef
    have htrace : (ρ.prod g.compressed.init).matrix.trace = ρ.matrix.trace := by
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
  have hfinal : (∑' p, ENNReal.ofReal (R p)) ^ (2⁻¹ : ℝ) ≤
      (ENNReal.ofReal (6 * lam) * (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re) ^
          (2⁻¹ : ℝ) +
        (ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
    hsum.trans (add_le_add (ENNReal.rpow_le_rpow hbad (by norm_num)) hrest)
  rw [hlhs]
  have hsq := ENNReal.rpow_le_rpow hfinal (z := 2) (by norm_num)
  rw [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_two] at hsq
  refine hsq.trans (le_of_eq ?_)
  have htr0 : 0 ≤ ρ.matrix.trace.re := SubState.trace_re_nonneg _
  have e1 : ENNReal.ofReal (6 * lam) * (n : ℝ≥0∞) ^ 2 * ENNReal.ofReal ρ.matrix.trace.re =
      ENNReal.ofReal (6 * lam * n ^ 2 * ρ.matrix.trace.re) := by
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 * lam * n ^ 2 by positivity),
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
  have h6 : √(6 : ℝ) * √lam * n + k * (2 * √lam) = √lam * (√6 * n + 2 * k) := by ring
  rw [h6, mul_pow, Real.sq_sqrt hlam0]

end OvGame

end Qrom
