module

public import VCVio.Quantum.Oracle.Compressed.BinaryPartition
public import VCVio.Quantum.Oracle.Compressed.Truncation
public import VCVio.Quantum.Comp.Potential

@[expose] public section

/-!
# The weight of a database event after a bounded number of queries

Let `π : Database X Y → Bool` label the databases, with the empty database outside the event
`π D = true`. A program that makes at most `t` calls to the truncated compressed oracle `O^(t)`
ends with weight at most `6 I t² tr ρ` on the event, where `I = I(π, t)` is the instability of
the labelling (`Quantum.Database.instability`).

The proof is the square-root hybrid against the pinched runtime
(`Quantum.QuantumRuntime.rpow_inv_two_eventWeight_le_commutators`): the square root of the final
weight is at most the sum over the calls of the square roots of the Kraus weights of the
commutators `[1 ⊗ Q, O^(t)]`, each at most `6 I` times the trace of the call's input
(`Quantum.l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul`), and at most `t`
calls carry weight. Since truncation is invisible to such a program
(`Quantum.jointPost_truncatedRuntime`), the bound holds for the joint post-states of the
compressed runtime, which realizes the quantum random-oracle model.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The projector onto the databases in the event, on the database register. -/
noncomputable abbrev eventProj (π : Database X Y → Bool) : Matrix (Database X Y) (Database X Y) ℂ :=
  labelProjector π true

theorem one_kronecker_eventProj (π : Database X Y → Bool) :
    (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ eventProj π =
      labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) true := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases hab : a = b
  · subst hab
    by_cases hcd : c = d
    · subst hcd
      simp [labelProjector]
    · simp [labelProjector, hcd]
  · simp [labelProjector, hab]

theorem eventProj_conjTranspose (π : Database X Y → Bool) : (eventProj π)ᴴ = eventProj π :=
  (isStarProjection_labelProjector π true).isSelfAdjoint

theorem eventProj_mul_self (π : Database X Y → Bool) : eventProj π * eventProj π = eventProj π :=
  (isStarProjection_labelProjector π true).isIdempotentElem

/-- A state on the empty database has no weight on an event the empty database is outside. -/
theorem conj_one_kronecker_eventProj_empty {A : Type*} [Fintype A] [DecidableEq A]
    (π : Database X Y → Bool) (hπ : π Database.empty = false) (ρ : Matrix A A ℂ) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ eventProj π)
      (ρ ⊗ₖ Matrix.single Database.empty Database.empty 1) = 0 := by
  have h : eventProj π * Matrix.single (Database.empty : Database X Y) Database.empty 1 = 0 := by
    ext D D'
    simp only [eventProj, labelProjector, diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases hD : D = Database.empty
    · subst hD
      simp [hπ]
    · simp [Ne.symm hD]
  rw [MatrixMap.conj_apply, ← mul_kronecker_mul, Matrix.one_mul, h, kronecker_zero,
    Matrix.zero_mul]

variable [UniformAnswerMeasure (X →ₒ Y)]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **The event bound for the truncated runtime.** From `ρ` beside the empty database, a program
with at most `t` calls ends with weight at most `6 I(π, t) t² tr ρ` on the event `π`. -/
theorem eventWeight_truncatedRuntime_le (I : L.Interp) (π : Database X Y → Bool)
    (hπ : π Database.empty = false) (t : ℕ) (x : QuantumComp L (qromSpec X Y) W A)
    (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) :
    (truncatedRuntime X Y t).eventWeight I (eventProj π) x
        (ρ.matrix ⊗ₖ (truncatedRuntime X Y t).init.matrix) ≤
      ENNReal.ofReal (6 * (Database.instability π t).toReal) * (t : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set R := truncatedRuntime X Y t
  set c : ℝ≥0∞ := ENNReal.ofReal (6 * (Database.instability π t).toReal)
  have hU : ∀ i r, (R.step i).branch r = MatrixMap.conj (truncatedOracle X Y t) :=
    fun _ _ ↦ branch_truncatedQuery_apply t _
  have hρ : (ρ.matrix ⊗ₖ R.init.matrix).PosSemidef := (ρ.prod R.init).posSemidef
  have hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ eventProj π)
      (ρ.matrix ⊗ₖ R.init.matrix) = 0 := by
    simpa [R, SubState.matrix_basis] using conj_one_kronecker_eventProj_empty π hπ ρ.matrix
  have h := QuantumRuntime.rpow_inv_two_eventWeight_le_commutators (D := R.D) (σ₀ := R.init)
    (s := R.step) (U := fun _ _ ↦ truncatedOracle X Y t) I hU (eventProj_conjTranspose π)
    (eventProj_mul_self π) x hρ hρQ
  -- each call's commutator weight is at most `c` times the trace of its input
  have hcall : ∀ (i : Unit) (σ : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ),
      σ.PosSemidef →
      QuantumRuntime.krausWeight (spec := qromSpec X Y) (D := R.D)
          (fun _ _ ↦ (1 ⊗ₖ eventProj π) * truncatedOracle X Y t -
            truncatedOracle X Y t * (1 ⊗ₖ eventProj π)) i σ ≤
        c * ENNReal.ofReal σ.trace.re := by
    intro i σ hσ
    refine (QuantumRuntime.krausWeight_le (spec := qromSpec X Y) (D := R.D)
      (fun _ _ ↦ (1 ⊗ₖ eventProj π) * truncatedOracle X Y t -
        truncatedOracle X Y t * (1 ⊗ₖ eventProj π)) i hσ).trans ?_
    gcongr
    rw [tsum_fintype, Fintype.sum_unique]
    refine ENNReal.ofReal_le_ofReal ?_
    have := l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul π t true
    rwa [one_kronecker_eventProj]
  have hj : ∀ j, R.queryWeight I (QuantumRuntime.krausWeight
        (fun _ _ ↦ (1 ⊗ₖ eventProj π) * truncatedOracle X Y t -
          truncatedOracle X Y t * (1 ⊗ₖ eventProj π))) x (ρ.matrix ⊗ₖ R.init.matrix) j ≤
      c * ENNReal.ofReal (ρ.matrix ⊗ₖ R.init.matrix).trace.re := by
    intro j
    refine (R.queryWeight_mono I (w' := fun _ σ ↦ c * ENNReal.ofReal σ.trace.re) hcall x hρ j).trans ?_
    rw [QuantumRuntime.queryWeight_const_mul]
    gcongr
    exact R.queryWeight_le_ofReal_trace I (fun _ _ _ ↦ le_rfl) x hρ j
  have htr : (ρ.matrix ⊗ₖ R.init.matrix).trace = ρ.matrix.trace := by
    simp [R, Matrix.trace_kronecker, SubState.matrix_basis]
  rw [htr] at hj
  have hzero : ∀ j ∉ Finset.range t, R.queryWeight I (QuantumRuntime.krausWeight
        (fun _ _ ↦ (1 ⊗ₖ eventProj π) * truncatedOracle X Y t -
          truncatedOracle X Y t * (1 ⊗ₖ eventProj π))) x (ρ.matrix ⊗ₖ R.init.matrix) j ^
        (2⁻¹ : ℝ) = 0 := by
    intro j hj'
    rw [R.queryWeight_eq_zero_of_isQueryBound I hx Finset.univ (by simp)
      (by simpa using hj') _, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hzero] at h
  have hsum : ∑ j ∈ Finset.range t, R.queryWeight I (QuantumRuntime.krausWeight
        (fun _ _ ↦ (1 ⊗ₖ eventProj π) * truncatedOracle X Y t -
          truncatedOracle X Y t * (1 ⊗ₖ eventProj π))) x (ρ.matrix ⊗ₖ R.init.matrix) j ^
        (2⁻¹ : ℝ) ≤ (t : ℝ≥0∞) * (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
    calc _ ≤ ∑ _j ∈ Finset.range t, (c * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ ENNReal.rpow_le_rpow (hj j) (by norm_num)
      _ = _ := by simp
  have h2 := (h.trans hsum)
  have := ENNReal.rpow_le_rpow h2 (z := 2) (by norm_num)
  rw [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at this
  calc _ ≤ _ := this
    _ = _ := by
      rw [show ((t : ℝ≥0∞) ^ (2 : ℝ)) = (t : ℝ≥0∞) ^ 2 by norm_cast]
      ring

/-- **The event bound for the compressed runtime.** A program with at most `t` calls, run from
`ρ` against the compressed oracle, leaves weight at most `6 I(π, t) t² tr ρ` on the event `π`
summed over its leaves. -/
theorem tsum_eventWeight_compressedRuntime_le (I : L.Interp) (π : Database X Y → Bool)
    (hπ : π Database.empty = false) (t : ℕ) (x : QuantumComp L (qromSpec X Y) W A)
    (hx : x.IsQueryBound fun _ ↦ t) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ eventProj π)
        ((compressedRuntime X Y).jointPost I x ρ p).matrix).trace.re ≤
      ENNReal.ofReal (6 * (Database.instability π t).toReal) * (t : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal ρ.matrix.trace.re := by
  refine le_of_eq_of_le ?_ (eventWeight_truncatedRuntime_le I π hπ t x hx ρ)
  refine tsum_congr fun p ↦ ?_
  rw [← jointPost_truncatedRuntime I hx le_rfl ρ p]
  rfl

end Qrom
