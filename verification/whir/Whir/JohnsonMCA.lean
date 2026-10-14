module

public import Whir.MutualAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement

/-!
The BCHKS25 same-agreement-set bound, using the pinned ArkLib construction
of the symbolic interpolation certificate, not a certificate hypothesis.
The affine-line provider is transported to the actual (1-z,z) fold over
an arbitrary field. Finite-field probability uses the project's exact
uniform probability. No field characteristic restriction is introduced.
-/
@[expose] public section

namespace Whir.MutualAgreement

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open scoped BigOperators

variable {F : Type*} [Field F]

open Classical in
/-- An exact correlated pair for the affine line gives actual input codewords
on the identical witness set for the binary fold. -/
theorem not_bad_of_exact_pair {n dimension a : ℕ}
    (domain : Fin n ↪ F) (U : Fin 2 → Fin n → F) (z : F)
    (hexact : ∀ P : F[X], P.degree < dimension →
      a ≤ (polynomialAgreementSet domain
        (fun i => U 0 i + z * (U 1 i - U 0 i)) P).card →
      HasExactCorrelatedPair domain (U 0) (fun i => U 1 i - U 0 i)
        (RingHom.id F) dimension z P) :
    ¬ Bad foldGenerator (rsCode domain dimension) a U z := by
  classical
  rintro ⟨T, hT, hfold, j, hj⟩
  obtain ⟨c, hc, hcT⟩ := (mem_projectedCode (rsCode domain dimension) T
    (fun i => ∑ j, foldGenerator z j * U j i)).mp hfold
  obtain ⟨P, hP, hPc⟩ := (mem_rsCode domain dimension c).mp hc
  have hPT : ∀ i ∈ T, P.eval (domain i) = U 0 i + z * (U 1 i - U 0 i) := by
    intro i hi
    rw [hPc i, hcT i hi]
    simp only [foldGenerator, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hcount : a ≤ (polynomialAgreementSet domain
      (fun i => U 0 i + z * (U 1 i - U 0 i)) P).card :=
    hT.trans (Finset.card_le_card fun i hi => (mem_polynomialAgreementSet _ _ _ _).mpr (hPT i hi))
  obtain ⟨pair, hp₀, hp₁, -, hset⟩ := hexact P hP hcount
  have hpair : ∀ i ∈ T,
      pair.1.eval (domain i) = U 0 i ∧ pair.2.eval (domain i) = U 1 i - U 0 i := by
    intro i hi
    have hmem : i ∈ polynomialAgreementSet
        (domain.trans ⟨RingHom.id F, (RingHom.id F).injective⟩)
        (fun i => (RingHom.id F) (U 0 i) + z * (RingHom.id F) (U 1 i - U 0 i)) P := by
      simpa using hPT i hi
    rw [hset] at hmem
    exact (mem_commonPolynomialAgreementSet _ _ _ _ _ _).mp hmem
  apply hj
  fin_cases j
  · apply (mem_projectedCode _ T (U 0)).mpr
    refine ⟨fun i => pair.1.eval (domain i), (mem_rsCode _ _ _).mpr ⟨pair.1, hp₀, fun _ => rfl⟩,
      fun i hi => (hpair i hi).1⟩
  · apply (mem_projectedCode _ T (U 1)).mpr
    refine ⟨fun i => (pair.1 + pair.2).eval (domain i),
      (mem_rsCode _ _ _).mpr ⟨pair.1 + pair.2,
        (degree_add_le _ _).trans_lt (max_lt hp₀ hp₁), fun _ => rfl⟩, ?_⟩
    intro i hi
    simp only [eval_add, (hpair i hi).1, (hpair i hi).2]
    ring

/-- The denominator written as a real three-halves power is exactly the
BCHKS25 expression, with multiplicity denominator equal to the full slack. -/
theorem johnsonNumerator_eq_bchks (n dimension : ℕ) (radius : ℝ) :
    johnsonNumerator n dimension radius =
      let rate : ℝ := (dimension - 1 : ℕ) / n
      let m : ℕ := max ⌈Real.sqrt rate / (1 - Real.sqrt rate - radius)⌉₊ 3
      let t : ℝ := m + 1 / 2
      ((2 * t ^ 5 + 3 * t * radius * rate) / (3 * rate ^ (3 / 2 : ℝ))) * n +
        t / Real.sqrt rate := by
  have h := johnson_sqrt_cube_eq_rpow_three_halves n (dimension - 1)
  dsimp [johnsonRhoMinus] at h
  simp only [johnsonNumerator, h]

open Classical in
/-- The exact BCHKS25 numerator bounds same-set scalar fold failures. ArkLib
constructs the interpolation certificate internally and proves the numerical
comparison to this numerator. The degree ratio is D/n, dimension is D+1. -/
theorem johnson_bad_count {n D : ℕ} (domain : Fin n ↪ F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (radius : ℝ) (hradius : 0 ≤ radius)
    (hJohnson : radius < 1 - Real.sqrt ((D : ℝ) / n))
    (U : Fin 2 → Fin n → F) [Fintype F] :
    ((Finset.univ.filter
      (Bad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ U)).card : ℝ) ≤
      johnsonNumerator n (D + 1) radius := by
  let eta := 1 - Real.sqrt ((D : ℝ) / n) - radius
  have heta : 0 < eta := by dsimp [eta]; linarith
  have ha : johnsonAgreement n D eta = 1 - radius := by
    unfold johnsonAgreement johnsonRhoMinus eta
    ring
  have hthreshold : johnsonAgreement n D eta * n ≤ ⌈(n : ℝ) * (1 - radius)⌉₊ := by
    rw [ha, mul_comm]
    exact Nat.le_ceil _
  have hAn : ⌈(n : ℝ) * (1 - radius)⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  obtain ⟨ex, hcard, hgood⟩ := exists_johnson_line_exactCorrelatedPair domain
    (U 0) (fun i => U 1 i - U 0 i) hD hDn heta hthreshold hAn
  have hsubset : Finset.univ.filter
      (Bad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ U) ⊆ ex := by
    intro z hz
    by_contra hzx
    exact not_bad_of_exact_pair domain U z (hgood z hzx) (Finset.mem_filter.mp hz).2
  have hcompare := johnsonExceptionCount_le_comparisonEstimate hD hDn heta
    (by rw [ha]; linarith) hthreshold
  have hnum : johnsonComparisonEstimate n D eta = johnsonNumerator n (D + 1) radius := by
    unfold johnsonComparisonEstimate johnsonComparisonShift johnsonComparisonMultiplicity
      johnsonGamma johnsonNumerator
    rw [ha]
    simp only [Nat.add_sub_cancel, johnsonRhoMinus, eta]
    congr 2
    ring
  exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans
    (hcard.trans (hcompare.trans_eq hnum))

open Classical in
/-- Arbitrary row interleaving has the identical BCHKS25 bound, not a
row-count multiple. All rows share the agreement set in RowBad. -/
theorem johnson_row_bad_count {n D : ℕ} {R : Type*} [Fintype F] [Fintype R]
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hJohnson : radius < 1 - Real.sqrt ((D : ℝ) / n))
    (U : Fin 2 → R → Fin n → F) :
    ((Finset.univ.filter
      (RowBad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ U)).card : ℝ) ≤
      johnsonNumerator n (D + 1) radius := by
  let s := Finset.univ.filter
    (RowBad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ U)
  obtain ⟨V, hV⟩ := row_bad_transfer foldGenerator (rsCode domain (D + 1))
    ⌈(n : ℝ) * (1 - radius)⌉₊ U s (Finset.card_le_univ s)
    (fun x hx => (Finset.mem_filter.mp hx).2)
  apply le_trans _ (johnson_bad_count domain hD hDn radius hradius hJohnson V)
  exact_mod_cast Finset.card_le_card (show s ⊆ Finset.univ.filter
    (Bad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ V) from
      fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV x hx⟩)

open Classical in
/-- Exact uniform probability for the scalar and arbitrary-row same-set event. -/
theorem johnson_row_bad_probability {n D : ℕ} {R : Type*} [Fintype F] [Fintype R]
    (domain : Fin n ↪ F) (hD : 1 ≤ D) (hDn : D ≤ n - 2)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hJohnson : radius < 1 - Real.sqrt ((D : ℝ) / n))
    (U : Fin 2 → R → Fin n → F) :
    (Soundness.uniformProb (Finset.univ.filter
      (RowBad foldGenerator (rsCode domain (D + 1)) ⌈(n : ℝ) * (1 - radius)⌉₊ U)) : ℝ) ≤
      johnsonNumerator n (D + 1) radius / Fintype.card F := by
  unfold Soundness.uniformProb
  push_cast
  exact div_le_div_of_nonneg_right
    (johnson_row_bad_count domain hD hDn radius hradius hJohnson U) (by positivity)

end Whir.MutualAgreement
