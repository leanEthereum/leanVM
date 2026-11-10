module

public import VCVio.Quantum.Comp.HybridProjected
public import QuantumFoundations.MatrixMap.Norm

@[expose] public section

/-!
# Runs that agree on a projected part of the runtime register

Let two runtimes on the same register `D` have Kraus steps `U` and `W`, and let `Π` be a projector
on `D` such that no step leaks from the complement of `Π` into `Π`
(`(1 ⊗ Π) U = (1 ⊗ Π) U (1 ⊗ Π)`, and the same for `W`), and the two steps agree inside `Π`
(`(1 ⊗ Π) U (1 ⊗ Π) = (1 ⊗ Π) W (1 ⊗ Π)`). If the initial states agree inside `Π`, then every
program reaches every leaf with the same joint post-state inside `Π`
(`Qrom.conj_jointPost_eq_of_proj`), and has the same query weights for weights that only read the
inputs inside `Π` (`Qrom.queryWeight_eq_of_proj`).

Both runtimes are simulated, through `ρ ↦ Π ρ Π`, by one runtime whose steps are those of the
second followed by `Π` (`Qrom.projRuntime`).
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

universe u v u₁ v₁ w

namespace Qrom

open Quantum

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg} {D : QReg}
variable {Pi : Matrix D D ℂ}

theorem posSemidef_one_kronecker_one_sub {n : Type*} [Fintype n] [DecidableEq n]
    (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi) :
    ((1 : Matrix n n ℂ) ⊗ₖ (1 - Pi)).PosSemidef := by
  have h : (1 : Matrix n n ℂ) ⊗ₖ (1 - Pi) =
      ((1 : Matrix n n ℂ) ⊗ₖ (1 - Pi))ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ (1 - Pi)) := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_sub, conjTranspose_one, hPi,
      ← mul_kronecker_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP, sub_self, sub_zero]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

variable {s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}

/-- The step of `s₁` followed by `Π`. -/
noncomputable def projStep (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
    (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi) (i : spec.Port) :
    SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i) :=
  SubInstrument.ofIsTNISum (fun r ↦ MatrixMap.conj (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ
      Pi) * W i r)) (fun _ ↦ MatrixMap.isCP_conj _) fun t ↦ by
    rw [← Finset.sum_coe_sort t]
    refine MatrixMap.isTNI_sum_conj_iff.mpr ?_
    rw [Finset.sum_coe_sort t (fun r ↦ (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) *
      W i r)ᴴ * (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r))]
    have h0 := (s₁ i).posSemidef_one_sub_sum_of_branch_eq_conj (hW i) t
    have hterm : ∀ r, (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r)ᴴ *
        (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r) =
        (W i r)ᴴ * ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r := by
      intro r
      rw [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, hPi, Matrix.mul_assoc,
        ← Matrix.mul_assoc ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi),
        ← mul_kronecker_mul, Matrix.one_mul, hPP, ← Matrix.mul_assoc]
    have hone : (1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ (1 - Pi) =
        1 - (1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi := by
      ext ⟨a, c⟩ ⟨b, d⟩
      simp [kroneckerMap_apply, Matrix.one_apply, mul_sub]
      split_ifs <;> simp_all
    have hsplit : 1 - ∑ r ∈ t, (W i r)ᴴ * ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) *
        W i r = (1 - ∑ r ∈ t, (W i r)ᴴ * W i r) + ∑ r ∈ t, (W i r)ᴴ *
          ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ (1 - Pi)) * W i r := by
      rw [hone]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_sub_distrib]
      abel
    simp only [hterm]
    rw [hsplit]
    exact h0.add (Matrix.posSemidef_sum t fun r _ ↦
      (posSemidef_one_kronecker_one_sub hPi hPP).conjTranspose_mul_mul_same (W i r))

variable {σ₀ σ₁ : SubState D}
  {s₀ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}

theorem trace_conj_proj_le (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi) {ρ : Matrix D D ℂ}
    (hρ : ρ.PosSemidef) : (MatrixMap.conj Pi ρ).trace.re ≤ ρ.trace.re := by
  have h1 : (MatrixMap.conj Pi ρ).trace = (Pi * ρ).trace := by
    rw [MatrixMap.conj_apply, hPi, Matrix.trace_mul_cycle, hPP]
  have h2 : (MatrixMap.conj (1 - Pi) ρ).trace = ((1 - Pi) * ρ).trace := by
    rw [MatrixMap.conj_apply, conjTranspose_sub, conjTranspose_one, hPi, Matrix.trace_mul_cycle,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP, sub_self, sub_zero]
  have h3 : 0 ≤ (MatrixMap.conj (1 - Pi) ρ).trace.re := by
    rw [MatrixMap.conj_apply]
    exact (hρ.mul_mul_conjTranspose_same _).trace_nonneg |> fun h ↦ (RCLike.nonneg_iff.mp h).1
  rw [h1]
  rw [h2, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h3
  linarith

/-- The substate `Π σ Π`. -/
noncomputable def projState (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi) (σ : SubState D) :
    SubState D where
  matrix := MatrixMap.conj Pi σ.matrix
  posSemidef := by
    rw [MatrixMap.conj_apply]
    exact σ.posSemidef.mul_mul_conjTranspose_same _
  trace_re_le_one := (trace_conj_proj_le hPi hPP σ.posSemidef).trans σ.trace_re_le_one

/-- The runtime of `s₁` followed by `Π`, started from `Π σ₁ Π`. -/
noncomputable def projRuntime (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
    (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi) (σ₁ : SubState D) : QuantumRuntime spec :=
  QuantumRuntime.mk D (projState hPi hPP σ₁) (projStep hW hPi hPP)

variable (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r)) (hPi : Piᴴ = Pi) (hPP : Pi * Pi = Pi)

include hU hW in
/-- The projected runtime simulates a runtime whose steps agree with those of `s₁` inside `Π` and
do not leak into `Π`. -/
theorem projRuntime_simulation
    (hleak : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hagree : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi) =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi)) (i : spec.Port) (r : spec.Result i) :
    ((projRuntime hW hPi hPP σ₁).step i).branch r ∘ₗ (MatrixMap.conj Pi).amplifyLeft (spec.In i) =
      (MatrixMap.conj Pi).amplifyLeft (spec.Out i) ∘ₗ
        ((QuantumRuntime.mk D σ₀ s₀).step i).branch r := by
  change MatrixMap.conj (((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r) ∘ₗ
      (MatrixMap.conj Pi).amplifyLeft (spec.In i) =
    (MatrixMap.conj Pi).amplifyLeft (spec.Out i) ∘ₗ (s₀ i).branch r
  rw [hU, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← MatrixMap.conj_mul, ← hagree, ← hleak]

include hU hW hPi hPP in
/-- **Agreement of the projected joint post-states.** -/
theorem conj_jointPost_eq_of_proj
    (hleak₀ : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hleak₁ : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hagree : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi) =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hinit : MatrixMap.conj Pi σ₀.matrix = MatrixMap.conj Pi σ₁.matrix)
    (x : QuantumComp L spec X A) (ρ : SubState A) (p : Σ u, X u) :
    (MatrixMap.conj Pi).amplifyLeft p.1 ((QuantumRuntime.mk D σ₀ s₀).jointPost I x ρ p).matrix =
      (MatrixMap.conj Pi).amplifyLeft p.1 ((QuantumRuntime.mk D σ₁ s₁).jointPost I x ρ p).matrix := by
  have h0 := QuantumRuntime.matrix_jointPost_of_simulation (R₁ := QuantumRuntime.mk D σ₀ s₀)
    (R₂ := projRuntime hW hPi hPP σ₁) I
    (projRuntime_simulation hU hW hPi hPP hleak₀ hagree) hinit x ρ p
  have h1 := QuantumRuntime.matrix_jointPost_of_simulation (R₁ := QuantumRuntime.mk D σ₁ s₁)
    (R₂ := projRuntime hW hPi hPP σ₁) I
    (projRuntime_simulation hW hW hPi hPP hleak₁ fun _ _ ↦ rfl) rfl x ρ p
  exact h0.symm.trans h1

include hU hW hPi hPP in
/-- **Agreement of the projected query weights.** -/
theorem queryWeight_eq_of_proj
    (hleak₀ : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hleak₁ : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hagree : ∀ i r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * U i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi) =
      ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Pi) * W i r *
        ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Pi))
    (hinit : MatrixMap.conj Pi σ₀.matrix = MatrixMap.conj Pi σ₁.matrix)
    (w : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix A A ℂ) (j : ℕ) :
    (QuantumRuntime.mk D σ₀ s₀).queryWeight I
        (fun i σ ↦ w i ((MatrixMap.conj Pi).amplifyLeft (spec.In i) σ)) x (ρ ⊗ₖ σ₀.matrix) j =
      (QuantumRuntime.mk D σ₁ s₁).queryWeight I
        (fun i σ ↦ w i ((MatrixMap.conj Pi).amplifyLeft (spec.In i) σ)) x (ρ ⊗ₖ σ₁.matrix) j := by
  have h0 := QuantumRuntime.queryWeight_simulation (R₁ := QuantumRuntime.mk D σ₀ s₀)
    (R₂ := projRuntime hW hPi hPP σ₁) I
    (projRuntime_simulation hU hW hPi hPP hleak₀ hagree) w x (ρ ⊗ₖ σ₀.matrix) j
  have h1 := QuantumRuntime.queryWeight_simulation (R₁ := QuantumRuntime.mk D σ₁ s₁)
    (R₂ := projRuntime hW hPi hPP σ₁) I
    (projRuntime_simulation hW hW hPi hPP hleak₁ fun _ _ ↦ rfl) w x (ρ ⊗ₖ σ₁.matrix) j
  refine h0.symm.trans (Eq.trans ?_ h1)
  have e : ((MatrixMap.conj Pi).amplifyLeft A) (ρ ⊗ₖ σ₀.matrix) =
      ((MatrixMap.conj Pi).amplifyLeft A) (ρ ⊗ₖ σ₁.matrix) := by
    rw [MatrixMap.amplifyLeft_kronecker, MatrixMap.amplifyLeft_kronecker, hinit]
  exact congrArg (fun M ↦ (projRuntime hW hPi hPP σ₁).queryWeight I w x M j) e

end Qrom
