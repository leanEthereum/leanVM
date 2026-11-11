module

public import VCVio.Quantum.Comp.Hybrid

@[expose] public section

/-!
# The one-directional hybrid for an event

Let a runtime's steps be Kraus maps `conj (U i r)` and let `Q` be a projector on its register.
Along any run, the square root of the weight on `1 ⊗ Q` grows, call by call, by at most the square
root of the weight that the call moves into the event: the Kraus weight of the forward block
`(1 ⊗ Q) U (1 ⊗ (1 - Q))` on the call's input (`Qrom.rpow_inv_two_fwd_run_le`). Local operations
act on the program register only, so they do not increase the weight on the event; a call keeps the
weight already in the event at most where it is. Unlike the square-root hybrid against the pinched
runtime, nothing is charged for weight that leaves the event.
-/

open Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Qrom

open Quantum QuantumRuntime SubInstrument

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg}

/-- The weight of the event `Q` of the runtime register in a joint operator on `B × D`. -/
noncomputable def evW {B D : Type*} [Fintype B] [DecidableEq B] [Fintype D]
    (Q : Matrix D D ℂ) (Γ : Matrix (B × D) (B × D) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q) Γ).trace.re

/-- The forward block of a Kraus operator: from the complement of the event into the event. -/
noncomputable def fwdKraus {D : QReg} (U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ)
    (Q : Matrix D D ℂ) (i : spec.Port) (r : spec.Result i) :
    Matrix (spec.Out i × D) (spec.In i × D) ℂ :=
  ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Q) * U i r *
    ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ (1 - Q))

section proj

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

omit [DecidableEq n] in
theorem trace_conj_proj {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (M : Matrix n n ℂ) :
    (MatrixMap.conj P M).trace = (P * M).trace := by
  rw [MatrixMap.conj_apply, hP, Matrix.trace_mul_cycle, hPP]

/-- A projector cuts the trace of a positive semidefinite operator. -/
theorem re_trace_conj_proj_le {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    (MatrixMap.conj P M).trace.re ≤ M.trace.re := by
  have hP' : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hPP' : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]
    abel
  have h3 := (hM.mul_mul_conjTranspose_same (1 - P)).trace_nonneg
  rw [← MatrixMap.conj_apply, trace_conj_proj hP' hPP', Matrix.sub_mul, Matrix.one_mul,
    Matrix.trace_sub] at h3
  rw [trace_conj_proj hP hPP]
  have := (Complex.nonneg_iff.mp h3).1
  simp only [Complex.sub_re] at this
  linarith

omit [Fintype n] [DecidableEq n] in
theorem one_kronecker_proj_conjTranspose {B : Type*} [Fintype B] [DecidableEq B]
    {P : Matrix n n ℂ} (hP : Pᴴ = P) : ((1 : Matrix B B ℂ) ⊗ₖ P)ᴴ = (1 : Matrix B B ℂ) ⊗ₖ P := by
  rw [conjTranspose_kronecker, conjTranspose_one, hP]

omit [DecidableEq n] in
theorem one_kronecker_proj_mul_self {B : Type*} [Fintype B] [DecidableEq B]
    {P : Matrix n n ℂ} (hPP : P * P = P) :
    ((1 : Matrix B B ℂ) ⊗ₖ P) * ((1 : Matrix B B ℂ) ⊗ₖ P) = (1 : Matrix B B ℂ) ⊗ₖ P := by
  rw [← mul_kronecker_mul, Matrix.one_mul, hPP]

end proj

section event

variable {B D : Type*} [Fintype B] [DecidableEq B] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
theorem evW_tsum {ι : Type*} (Q : Matrix D D ℂ) {f : ι → Matrix (B × D) (B × D) ℂ}
    (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    evW Q (∑' b, f b) = ∑' b, evW Q (f b) := by
  rw [evW, MatrixMap.map_tsum _ hf]
  exact ofReal_trace_re_tsum (MatrixMap.summable_comp _ hf)
    fun b ↦ (hpos b).mul_mul_conjTranspose_same _

end event

/-! ## One call and one local operation -/

section steps

variable {D : QReg} (R : QuantumRuntime spec)
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ}
  (hU : ∀ i r, (R.step i).branch r = MatrixMap.conj (U i r))
  {Q : Matrix R.D R.D ℂ} (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
include hQ hQQ

omit hQ hQQ in
/-- **A local operation** does not increase the weight on the event. -/
theorem tsum_evW_frame_le {B : QReg} (o : L.Op B) {Γ : Matrix (B × R.D) (B × R.D) ℂ}
    (hΓ : Γ.PosSemidef) :
    ∑' b, evW Q (((I o).frame R.D).branch b Γ) ≤ evW Q Γ := by
  have e : ∀ b, MatrixMap.conj ((1 : Matrix (L.next o b) (L.next o b) ℂ) ⊗ₖ Q)
      (((I o).frame R.D).branch b Γ) =
        ((I o).frame R.D).branch b (MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Q) Γ) := fun b ↦ by
    rw [← MatrixMap.amplifyLeft_conj, ← MatrixMap.amplifyLeft_conj,
      DSubInstrument.branch_frame_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      MatrixMap.amplify_comp_amplifyLeft]
  simp only [evW, e]
  exact ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le
    (hΓ.mul_mul_conjTranspose_same _)

include hU in
/-- **One call.** The square root of the weight on the event after a call is at most that before
the call plus the square root of the Kraus weight of the forward block on the call's input. -/
theorem tsum_evW_queryStep_le (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    {Γ : Matrix (A × R.D) (A × R.D) ℂ} (hΓ : Γ.PosSemidef) :
    (∑' r, evW Q ((R.queryStep i E ℓ).branch r Γ)) ^ (2⁻¹ : ℝ) ≤
      evW Q Γ ^ (2⁻¹ : ℝ) +
        krausWeight (fwdKraus U Q) i (callInput ℓ R.D Γ) ^ (2⁻¹ : ℝ) := by
  set Γ' := (relabel (queryEquivIn ℓ R.D)).branch () Γ with hΓ'
  have hΓ'pos : Γ'.PosSemidef := (relabel _).posSemidef_branch_apply () hΓ
  set QI := (1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q
  set QO := (1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Q
  -- the weight after the call, on the relabelled input
  have hd : ∀ r, evW Q ((R.queryStep i E ℓ).branch r Γ) =
      ENNReal.ofReal (MatrixMap.conj ((QO * U i r) ⊗ₖ (1 : Matrix E E ℂ)) Γ').trace.re := by
    intro r
    rw [evW, queryStep_branch_apply, ← MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.amplifyLeft _ _),
      ← intertwines_relabel_queryEquivOut _ (spec.Out i) E (), LinearMap.comp_apply,
      trace_relabel_branch_apply, ← hΓ', DSubInstrument.branch_frame_apply, hU,
      MatrixMap.amplifyLeft_conj, MatrixMap.amplify_conj, MatrixMap.amplify_conj,
      ← LinearMap.comp_apply (MatrixMap.conj _), ← MatrixMap.conj_mul,
      MatrixMap.mul_kronecker_one]
  have hsplit : ∀ r, (QO * U i r) ⊗ₖ (1 : Matrix E E ℂ) =
      (QO * U i r * QI) ⊗ₖ (1 : Matrix E E ℂ) + fwdKraus U Q i r ⊗ₖ (1 : Matrix E E ℂ) := by
    intro r
    rw [← add_kronecker, fwdKraus, ← Matrix.mul_add]
    congr 1
    rw [← kronecker_add, add_sub_cancel, one_kronecker_one, Matrix.mul_one]
  -- the weight already in the event stays at most where it is
  have hstay : ∑' r, ENNReal.ofReal (MatrixMap.conj ((QO * U i r * QI) ⊗ₖ (1 : Matrix E E ℂ))
      Γ').trace.re ≤ evW Q Γ := by
    have hQI : (MatrixMap.conj (QI ⊗ₖ (1 : Matrix E E ℂ)) Γ').PosSemidef :=
      hΓ'pos.mul_mul_conjTranspose_same _
    calc ∑' r, ENNReal.ofReal (MatrixMap.conj ((QO * U i r * QI) ⊗ₖ (1 : Matrix E E ℂ))
          Γ').trace.re
        ≤ ∑' r, ENNReal.ofReal (((R.step i).frame E).branch r
            (MatrixMap.conj (QI ⊗ₖ (1 : Matrix E E ℂ)) Γ')).trace.re := by
          refine ENNReal.tsum_le_tsum fun r ↦ ENNReal.ofReal_le_ofReal ?_
          have e1 : MatrixMap.conj ((QO * U i r * QI) ⊗ₖ (1 : Matrix E E ℂ)) Γ' =
              MatrixMap.conj (QO ⊗ₖ (1 : Matrix E E ℂ))
                (MatrixMap.conj ((U i r * QI) ⊗ₖ (1 : Matrix E E ℂ)) Γ') := by
            rw [Matrix.mul_assoc, MatrixMap.mul_kronecker_one, MatrixMap.conj_mul]
            rfl
          have e2 : ((R.step i).frame E).branch r (MatrixMap.conj (QI ⊗ₖ (1 : Matrix E E ℂ)) Γ') =
              MatrixMap.conj ((U i r * QI) ⊗ₖ (1 : Matrix E E ℂ)) Γ' := by
            rw [DSubInstrument.branch_frame_apply, hU, MatrixMap.amplify_conj,
              ← LinearMap.comp_apply (MatrixMap.conj _), ← MatrixMap.conj_mul,
              ← MatrixMap.mul_kronecker_one]
          rw [e1, e2]
          refine re_trace_conj_proj_le ?_ ?_ (hΓ'pos.mul_mul_conjTranspose_same _)
          · rw [conjTranspose_kronecker, conjTranspose_one, one_kronecker_proj_conjTranspose hQ]
          · rw [← mul_kronecker_mul, Matrix.one_mul, one_kronecker_proj_mul_self hQQ]
      _ ≤ ENNReal.ofReal (MatrixMap.conj (QI ⊗ₖ (1 : Matrix E E ℂ)) Γ').trace.re :=
          ((R.step i).frame E).isCPTNIFamily.tsum_ofReal_trace_re_le hQI
      _ = evW Q Γ := by
          rw [evW, hΓ', ← MatrixMap.amplify_conj, ← MatrixMap.amplifyLeft_conj,
            ← LinearMap.comp_apply ((MatrixMap.amplifyLeft _ _).amplify E),
            ← intertwines_relabel_queryEquivIn _ ℓ (), LinearMap.comp_apply,
            trace_relabel_branch_apply, MatrixMap.amplifyLeft_conj]
  -- the forward block is the Kraus weight on the call's input
  have hfwd : ∀ r, (MatrixMap.conj (fwdKraus U Q i r ⊗ₖ (1 : Matrix E E ℂ)) Γ').trace =
      (MatrixMap.conj (fwdKraus U Q i r) (callInput ℓ R.D Γ)).trace := fun r ↦ by
    rw [MatrixMap.trace_conj_kronecker_one_apply]
    rfl
  refine (rpow_inv_two_tsum_le_of_le_add (t := fun r ↦ evW Q ((R.queryStep i E ℓ).branch r Γ))
    (a := fun r ↦ ENNReal.ofReal (MatrixMap.conj ((QO * U i r * QI) ⊗ₖ (1 : Matrix E E ℂ))
      Γ').trace.re)
    (b := fun r ↦ ENNReal.ofReal
      (MatrixMap.conj (fwdKraus U Q i r) (callInput ℓ R.D Γ)).trace.re) fun r ↦ ?_).trans ?_
  · rw [hd, hsplit, ← hfwd]
    exact MatrixMap.ofReal_trace_conj_add_rpow_le hΓ'pos _ _
  · exact add_le_add (ENNReal.rpow_le_rpow hstay (by norm_num)) le_rfl

include hU in
/-- **The one-directional hybrid.** Along the run of a program from `Γ`, the square root of the
weight on the event at the leaves is at most that of `Γ`, plus the sum over the calls of the square
roots of the Kraus weights of the forward blocks on their inputs. -/
theorem rpow_inv_two_fwd_run_le (x : QuantumComp L spec X A)
    {Γ : Matrix (A × R.D) (A × R.D) ℂ} (hΓ : Γ.PosSemidef) :
    (∑' p, evW Q ((R.run I x).branch p Γ)) ^ (2⁻¹ : ℝ) ≤
      evW Q Γ ^ (2⁻¹ : ℝ) +
        ∑' j, R.queryWeight I (krausWeight (fwdKraus U Q)) x Γ j ^ (2⁻¹ : ℝ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, evW, map_zero]
        simp,
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_self_add
  | primBind B o k ih =>
    have hΓb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hΓ
    have hL : ∀ p, evW Q ((R.run I (QuantumComp.primBind o k)).branch p Γ) =
        ∑' b, evW Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b Γ)) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact evW_tsum Q ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply Γ)
        fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hΓb b)
    simp only [hL, queryWeight_primBind]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun b ↦ ih b (hΓb b)).trans
      (add_le_add (ENNReal.rpow_le_rpow (tsum_evW_frame_le I R o hΓ) (by norm_num))
        le_rfl)
  | queryBind B i E ℓ k ih =>
    have hΓr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hΓ
    have hL : ∀ p, evW Q ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p Γ) =
        ∑' r, evW Q ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r Γ)) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact evW_tsum Q (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
        (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply Γ)
        fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hΓr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun r ↦ ih r (hΓr r)).trans ?_
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, queryWeight_queryBind_zero, ← add_assoc]
    simp only [queryWeight_queryBind_succ]
    exact add_le_add (tsum_evW_queryStep_le R hU hQ hQQ i E ℓ hΓ) le_rfl

end steps

end Qrom
