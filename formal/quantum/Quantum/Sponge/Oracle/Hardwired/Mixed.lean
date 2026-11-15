module

public import VCVio.Quantum.Comp.Potential
public import VCVio.Quantum.Comp.GradedRuntime
public import VCVio.Quantum.Oracle.Emulated

@[expose] public section

/-!
# Event bounds for runtimes with quantum and classical ports

A generalization of the square-root hybrid event bound
(`Quantum.QuantumRuntime.rpow_inv_two_eventWeight_le_commutators`) to runtimes whose ports are of
two kinds, told apart by `cls : spec.Port → Bool`.

* A **quantum** port (`cls i = false`) may change the weight of the event amplitude-wise: at the
  `n`-th quantum call, `√w' ≤ √w + √(ε n · tr σ)` on inputs `σ` supported on grades at most
  `n + K`.
* A **classical** port (`cls i = true`) changes it additively: `w' ≤ w + d i σ`.

Here `w σ = tr ((1 ⊗ Q) σ (1 ⊗ Q)ᴴ)` is `Quantum.QuantumRuntime.potential Q`. If every step
raises a grade of the runtime register by at most one, a program making at most `q` quantum and
`K` classical calls on every path ends with `√w ≤ ∑_{n < q} √(ε n · tr ρ) + √(w ρ + ∑ d)`, where
`∑ d` is the classical cost summed over all calls (`Quantum.QuantumRuntime.totalWeight`)
(`Quantum.Sponge.rpow_inv_two_eventWeight_le_mixed`). The classical steps cost one square root in
total, not one per call: a classical step uses `(A + √B)² + δ ≤ (A + √(B + δ))²`.

Budgets on the two kinds of calls are charge bounds (`Quantum.Sponge.portCharge`).
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum.Sponge

open Quantum QuantumRuntime

/-! ## Charges of calls -/

section charge

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{u₁, v₁}} {X : QReg → Type w}
  {A : QReg}

/-- The charge `κ i` of a call of port `i`; local operations are free. -/
def portCharge (κ : spec.Port → ℕ) (A : QReg) : QuantumComp.Cmd L spec A → ℕ
  | .prim _ => 0
  | .query i _ _ => κ i

/-- A local operation followed by a continuation is within a charge budget when every
continuation is. -/
theorem isChargeBound_portCharge_primBind_iff (κ : spec.Port → ℕ) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b)) (n : ℕ) :
    IFreeM.IsChargeBound (QuantumComp.primBind o k) (portCharge κ) n ↔
      ∀ b, IFreeM.IsChargeBound (k b) (portCharge κ) n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec) (X := X)
    (c := portCharge κ) (.prim o) (QuantumComp.onDown k) n).trans ?_
  simp only [portCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

/-- A call of port `i` followed by a continuation uses `κ i` of the budget. -/
theorem isChargeBound_portCharge_queryBind_iff (κ : spec.Port → ℕ) (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E) (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (n : ℕ) :
    IFreeM.IsChargeBound (QuantumComp.queryBind i E ℓ k) (portCharge κ) n ↔
      κ i ≤ n ∧ ∀ r, IFreeM.IsChargeBound (k r) (portCharge κ) (n - κ i) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec) (X := X)
    (c := portCharge κ) (.query i E ℓ) (QuantumComp.onDown k) n).trans ?_
  exact and_congr Iff.rfl ULift.forall

end charge

/-! ## Scalar and potential lemmas -/

/-- If `√a ≤ √b + √c`, then `√(a + C) ≤ √c + √(b + C)`. -/
theorem rpow_inv_two_add_le_of_le {a b c C : ℝ≥0∞}
    (h : a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) :
    (a + C) ^ (2⁻¹ : ℝ) ≤ c ^ (2⁻¹ : ℝ) + (b + C) ^ (2⁻¹ : ℝ) := by
  have h' := rpow_inv_two_tsum_le_of_le_add (K := Bool) (t := fun k ↦ if k then a else C)
    (a := fun k ↦ if k then c else 0) (b := fun k ↦ if k then b else C) fun k ↦ by
      cases k
      · simp only [Bool.false_eq_true, ↓reduceIte,
          ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), zero_add, le_refl]
      · simpa only [↓reduceIte, add_comm (b ^ (2⁻¹ : ℝ))] using h
  simpa only [tsum_fintype, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero] using h'

/-- The potential is countably additive on summable families of positive semidefinite
operators. -/
theorem potential_tsum {D Z : Type*} [Fintype D] [Fintype Z] (K : Matrix Z D ℂ) {A ι : Type*}
    [Fintype A] [DecidableEq A] {f : ι → Matrix (A × D) (A × D) ℂ} (hf : Summable f)
    (hpos : ∀ b, (f b).PosSemidef) :
    potential K (∑' b, f b) = ∑' b, potential K (f b) := by
  simp only [potential]
  rw [MatrixMap.map_tsum _ hf]
  refine ofReal_trace_re_tsum (MatrixMap.summable_comp _ hf) fun b ↦ ?_
  rw [MatrixMap.amplifyLeft_conj]
  exact (hpos b).mul_mul_conjTranspose_same _

/-! ## The mixed event bound -/

section mixed

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} (Q : Matrix R.D R.D ℂ) (cls : spec.Port → Bool)
  (g : R.D → ℕ)

/-- The event weight is the summed potential of the leaves. -/
theorem eventWeight_eq_tsum_potential {A : QReg} (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.eventWeight I Q x ρ = ∑' p, potential Q ((R.run I x).branch p ρ) := by
  simp only [eventWeight, potential, MatrixMap.amplifyLeft_conj]

/-- **The mixed bound, by induction on the program.** From a state `ρ` supported on grades at
most `t`, with `n₀` quantum calls already made and at most `q'` quantum and `K'` classical calls
left (`n₀ + q' ≤ q`, `t + K' ≤ n₀ + K`), the summed potential of the leaves satisfies
`√w ≤ ∑' n, √(e n · tr ρ) + √(w ρ + ∑ d)` for every `e` dominating `ε (n₀ + n)` below `q'`. -/
theorem rpow_inv_two_tsum_potential_run_le_mixed
    (hg : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (ε : ℕ → ℝ≥0∞) (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) (q K : ℕ)
    (hq : ∀ n < q, ∀ i, cls i = false → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic (n + K)) σ →
        (∑' r, potential Q ((R.step i).branch r σ)) ^ (2⁻¹ : ℝ) ≤
          potential Q σ ^ (2⁻¹ : ℝ) + (ε n * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ))
    (hc : ∀ i, cls i = true → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ + d i σ)
    {A : QReg} (x : QuantumComp L spec X A) (n₀ q' t K' : ℕ) (e : ℕ → ℝ≥0∞)
    (he : ∀ n < q', ε (n₀ + n) ≤ e n)
    (hxq : IFreeM.IsChargeBound x (portCharge fun i ↦ if cls i then 0 else 1) q')
    (hxK : IFreeM.IsChargeBound x (portCharge fun i ↦ if cls i then 1 else 0) K')
    (hqq : n₀ + q' ≤ q) (htK : t + K' ≤ n₀ + K) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef)
    (hρg : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    (∑' p, potential Q ((R.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      ∑' n, (e n * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n₀ q' t K' e with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_add_left (ENNReal.rpow_le_rpow le_self_add (by norm_num))
  | primBind B o k ih =>
    have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
        ∑' b, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) :=
      fun p ↦ by
        rw [run_primBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q ((((I o).frame R.D).isCPTNIFamily.comp_eval
          (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
          fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hxq hxK
    refine (rpow_inv_two_tsum_le_of_le_add_tsum
      (L := fun b ↦ ∑' p, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
      (t := fun b ↦ potential Q (((I o).frame R.D).branch b ρ) +
        R.totalWeight I d (k b) (((I o).frame R.D).branch b ρ))
      (m := fun j b ↦ e j * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re)
      fun b ↦ (ih b n₀ q' t K' e he (hxq b) (hxK b) hqq htK (hρb b)
        (hρg.amplify_snd _)).trans_eq (add_comm _ _)).trans ?_
    rw [add_comm]
    gcongr with j
    · rw [ENNReal.tsum_mul_left]
      gcongr
      exact ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    · rw [ENNReal.tsum_add, totalWeight_primBind]
      gcongr
      exact tsum_potential_frame_le Q (I o) hρ
  | queryBind B i E ℓ k ih =>
    have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
        ∑' r, potential Q ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)) :=
      fun p ↦ by
        rw [run_queryBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
          fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hxq hxK
    have hσ := posSemidef_callInput ℓ hρ
    have hσg : QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t)
        (callInput ℓ R.D ρ) := hρg.callInput ℓ
    have hρrg := fun r ↦ QuerySupportedOn.queryStep_of_step R g hg i E ℓ r hρg
    have hpot : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R Q i E ℓ r ρ
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    rw [totalWeight_queryBind]
    cases hci : cls i
    · -- A quantum call.
      simp only [hci, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at hxq hxK
      have hk := fun r ↦ ih r (n₀ + 1) (q' - 1) (t + 1) K' (fun n ↦ e (n + 1))
        (fun n hn ↦ by
          rw [show n₀ + 1 + n = n₀ + (n + 1) by omega]
          exact he (n + 1) (by omega))
        (hxq.2 r) (hxK.2 r) (by omega) (by omega) (hρr r) (hρrg r)
      refine (rpow_inv_two_tsum_le_of_le_add_tsum
        (L := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
          ((R.queryStep i E ℓ).branch r ρ)))
        (t := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
          R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
        (m := fun j r ↦ e (j + 1) * ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
        fun r ↦ (hk r).trans_eq (add_comm _ _)).trans ?_
      have hq0 := hq n₀ (by omega) i hci _ hσ (hσg.mono (Set.Iic_subset_Iic.mpr (by omega)))
      rw [potential_callInput, trace_callInput, ← hpot] at hq0
      have hε0 : ε n₀ ≤ e 0 := by simpa using he 0 (by omega)
      have hq0' : (∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ)) ^ (2⁻¹ : ℝ) ≤
          potential Q ρ ^ (2⁻¹ : ℝ) + (e 0 * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) :=
        hq0.trans (by gcongr)
      rw [ENNReal.tsum_add]
      refine (add_le_add (rpow_inv_two_add_le_of_le hq0') le_rfl).trans ?_
      conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
      calc _ ≤ (e 0 * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
            (potential Q ρ + (d i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I d (k r)
              ((R.queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) +
            ∑' j, (e (j + 1) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
            gcongr with j
            · exact le_add_self
            · rw [ENNReal.tsum_mul_left]
              gcongr
        _ = _ := by ring
    · -- A classical call.
      simp only [hci, ↓reduceIte, Nat.sub_zero] at hxq hxK
      have hk := fun r ↦ ih r n₀ q' (t + 1) (K' - 1) e he (hxq.2 r) (hxK.2 r) hqq (by omega)
        (hρr r) (hρrg r)
      refine (rpow_inv_two_tsum_le_of_le_add_tsum
        (L := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
          ((R.queryStep i E ℓ).branch r ρ)))
        (t := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
          R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
        (m := fun j r ↦ e j * ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
        fun r ↦ (hk r).trans_eq (add_comm _ _)).trans ?_
      have hc0 := hc i hci _ hσ
      rw [potential_callInput, ← hpot] at hc0
      rw [add_comm]
      gcongr with j
      · rw [ENNReal.tsum_mul_left]
        gcongr
      · rw [ENNReal.tsum_add, ← add_assoc]
        gcongr

/-- **The mixed event bound.** Let every step of `R` raise the grade `g` of the support by at
most one, let each quantum port satisfy `√w' ≤ √w + √(ε n · tr σ)` at its `n`-th call
(`n < q`) on inputs of grade at most `n + K`, and each classical port `w' ≤ w + d i σ`. A program
making at most `q` quantum and `K` classical calls, run from a positive semidefinite `ρ` of grade
`0`, ends with event weight `√w ≤ ∑_{n < q} √(ε n · tr ρ) + √(w ρ + ∑ d)`. -/
theorem rpow_inv_two_eventWeight_le_mixed
    (hg : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + 1))
          ((R.step i).branch r σ))
    (ε : ℕ → ℝ≥0∞) (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) (q K : ℕ)
    (hq : ∀ n < q, ∀ i, cls i = false → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic (n + K)) σ →
        (∑' r, potential Q ((R.step i).branch r σ)) ^ (2⁻¹ : ℝ) ≤
          potential Q σ ^ (2⁻¹ : ℝ) + (ε n * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ))
    (hc : ∀ i, cls i = true → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ + d i σ)
    {A : QReg} (x : QuantumComp L spec X A)
    (hxq : IFreeM.IsChargeBound x (portCharge fun i ↦ if cls i then 0 else 1) q)
    (hxK : IFreeM.IsChargeBound x (portCharge fun i ↦ if cls i then 1 else 0) K)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hρg : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic 0) ρ) :
    R.eventWeight I Q x ρ ^ (2⁻¹ : ℝ) ≤
      ∑ n ∈ Finset.range q, (ε n * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  rw [eventWeight_eq_tsum_potential]
  refine (rpow_inv_two_tsum_potential_run_le_mixed R I Q cls g hg ε d q K hq hc x 0 q 0 K
    (fun n ↦ if n < q then ε n else 0) (fun n hn ↦ by simp [hn]) hxq hxK (by omega) (by omega) hρ
    hρg).trans_eq ?_
  rw [tsum_eq_sum (s := Finset.range q) fun n hn ↦ by
    simp only [show ¬ n < q by simpa using hn, ↓reduceIte, zero_mul]
    exact ENNReal.zero_rpow_of_pos (by norm_num)]
  congr 1
  exact Finset.sum_congr rfl fun n hn ↦ by
    simp only [Finset.mem_range.mp hn, ↓reduceIte]

end mixed

end Quantum.Sponge

end
