module

public import Qrom.OvBlocks
public import Qrom.OvEvent

@[expose] public section

/-!
# Hiding: replacing the hash by `G` where its inputs carry unseen data

Two games `g₁ g₂ : Qrom.OvGame` with the same side ports whose hashes differ only on the protected
inputs `Prot s x` of each side state differ, call by call, by at most four times the mass of the
call on the protected inputs (`Qrom.OvGame.krausWeight_sub_le`). With the square-root hybrid, the
probability of any event of the first game is at most that of the second plus a sum over the calls
of the square roots of these masses (`Qrom.OvGame.rpow_inv_two_evalDistMap_le_hybrid`).
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable (Prot : S → X → Prop) [∀ s, DecidablePred (Prot s)]

/-- The projector onto the protected inputs, on the hash port's joint register. -/
def protDiag : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ :=
  diagonal fun p ↦ if Prot p.2.1 p.1.1 then 1 else 0

theorem protDiag_conjTranspose : (protDiag (Y := Y) Prot)ᴴ = protDiag Prot := by
  rw [protDiag, diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : Prot p.2.1 p.1.1 <;> simp [h]

theorem protDiag_mul_self : protDiag (Y := Y) Prot * protDiag Prot = protDiag Prot := by
  rw [protDiag, diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : Prot p.2.1 p.1.1 <;> simp [h]

/-- The mass of a hash call on the protected inputs. -/
noncomputable def protMassH (σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (protDiag (Y := Y) Prot * σ).trace.re

/-- The mass of a call on the protected inputs; side ports carry none. -/
noncomputable def protMass : ∀ i : (ovSpec X Y S P Res).Port,
    Matrix ((ovSpec X Y S P Res).In i × (S × Unit)) ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ →
      ℝ≥0∞
  | .inl _ => protMassH Prot
  | .inr _ => fun _ ↦ 0

variable {g₁ g₂ : OvGame X Y S P Res}

/-- Off the protected inputs the two hash ports agree. -/
theorem tableOracle_sub_mul_protDiag (G : X → Y)
    (hov : ∀ s x, ¬ Prot s x → g₁.ov s x = g₂.ov s x) :
    (tableOracle (fun t : S × Unit ↦ g₂.answer t.1 G) -
        tableOracle (fun t : S × Unit ↦ g₁.answer t.1 G)) * protDiag Prot =
      tableOracle (fun t : S × Unit ↦ g₂.answer t.1 G) -
        tableOracle (fun t : S × Unit ↦ g₁.answer t.1 G) := by
  ext p ⟨m', t'⟩
  rw [protDiag, Matrix.mul_diagonal]
  by_cases h : Prot t'.1 m'.1
  · simp [h]
  · have he : g₂.answer t'.1 G m'.1 = g₁.answer t'.1 G m'.1 := by
      simp only [answer, hov _ _ h]
    have he' : (tableOracleEquiv fun t : S × Unit ↦ g₂.answer t.1 G) (m', t') =
        (tableOracleEquiv fun t : S × Unit ↦ g₁.answer t.1 G) (m', t') := by
      simp only [tableOracleEquiv_apply, oracleEquiv_apply, he]
    simp only [h, ↓reduceIte, mul_zero]
    rw [Matrix.sub_apply, tableOracle_apply, tableOracle_apply, he', sub_self]

theorem norm_tableOracle_le_one (read : S × Unit → X → Y) : ‖tableOracle read‖ ≤ 1 :=
  l2_opNorm_le_one_of_conjTranspose_mul_self (conjTranspose_tableOracle_mul_self read)

/-- The per-call cost of a hash call. -/
theorem trace_conj_sub_le (G : X → Y) (hov : ∀ s x, ¬ Prot s x → g₁.ov s x = g₂.ov s x)
    {σ : Matrix ((X × Y) × (S × Unit)) ((X × Y) × (S × Unit)) ℂ} (hσ : σ.PosSemidef) :
    ENNReal.ofReal (MatrixMap.conj (tableOracle (fun t : S × Unit ↦ g₂.answer t.1 G) -
      tableOracle (fun t : S × Unit ↦ g₁.answer t.1 G)) σ).trace.re ≤ 4 * protMassH Prot σ := by
  simp only [protMassH]
  set Dm := tableOracle (fun t : S × Unit ↦ g₂.answer t.1 G) -
    tableOracle (fun t : S × Unit ↦ g₁.answer t.1 G)
  have hD : Dm = Dm * protDiag Prot := (tableOracle_sub_mul_protDiag Prot G hov).symm
  have hnorm : ‖Dm‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [norm_tableOracle_le_one (fun t : S × Unit ↦
      g₂.answer t.1 G), norm_tableOracle_le_one (fun t : S × Unit ↦ g₁.answer t.1 G)])
  have hπσ : (MatrixMap.conj (protDiag (Y := Y) Prot) σ).PosSemidef := by
    rw [MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same _
  have htrπ : (MatrixMap.conj (protDiag (Y := Y) Prot) σ).trace =
      (protDiag (Y := Y) Prot * σ).trace := by
    rw [MatrixMap.conj_apply, protDiag_conjTranspose, Matrix.trace_mul_cycle, protDiag_mul_self]
  have h1 : MatrixMap.conj Dm σ = MatrixMap.conj Dm (MatrixMap.conj (protDiag Prot) σ) := by
    rw [← LinearMap.comp_apply (MatrixMap.conj Dm), ← MatrixMap.conj_mul, ← hD]
  rw [h1, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ((MatrixMap.re_trace_conj_le Dm hπσ).trans ?_)
  rw [htrπ]
  have h0 : 0 ≤ (protDiag (Y := Y) Prot * σ).trace.re := by
    rw [← htrπ]
    exact (hπσ.trace_nonneg |> fun h ↦ (RCLike.nonneg_iff.mp h).1)
  have h4 : ‖Dm‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg Dm]
  exact mul_le_mul_of_nonneg_right h4 h0

/-- **The per-call cost.** -/
theorem krausWeight_sub_le (G : X → Y) (htr : g₁.trans = g₂.trans)
    (hov : ∀ s x, ¬ Prot s x → g₁.ov s x = g₂.ov s x) (i : (ovSpec X Y S P Res).Port)
    {σ : Matrix ((ovSpec X Y S P Res).In i × (S × Unit)) ((ovSpec X Y S P Res).In i × (S × Unit)) ℂ}
    (hσ : σ.PosSemidef) :
    QuantumRuntime.krausWeight (spec := ovSpec X Y S P Res) (D := QReg.of (S × Unit))
        (fun i r ↦ g₂.sampKraus G i r - g₁.sampKraus G i r) i σ ≤ 4 * protMass Prot i σ := by
  rcases i with ⟨⟩ | j
  · let _ : Unique ((ovSpec X Y S P Res).Result (.inl ())) := inferInstanceAs (Unique Unit)
    let _ : Fintype ((ovSpec X Y S P Res).Result (.inl ())) := inferInstanceAs (Fintype Unit)
    rw [QuantumRuntime.krausWeight, tsum_fintype, Fintype.sum_unique]
    exact trace_conj_sub_le Prot G hov hσ
  · have hz : ∀ r, g₂.sampKraus G (.inr j) r - g₁.sampKraus G (.inr j) r = 0 := fun r ↦ by
      change g₂.sideKraus Unit j r - g₁.sideKraus Unit j r = 0
      simp only [sideKraus, htr, sub_self]
    rw [QuantumRuntime.krausWeight]
    refine (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_).le.trans zero_le
    rw [hz r, MatrixMap.conj_apply, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, ENNReal.ofReal_zero]

end OvGame

end Qrom
