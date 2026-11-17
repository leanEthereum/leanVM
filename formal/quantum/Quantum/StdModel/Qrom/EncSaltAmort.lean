module

public import Quantum.StdModel.Qrom.EncSaltFirst
public import Quantum.Xmss.Assembly.CostJoint
public import Quantum.Xmss.Assembly.RecJ
public import Quantum.Xmss.Assembly.EndReads

@[expose] public section

/-!
# EncTCR$: the challenger's trial reads, amortized over the targets

The total weight `TW` of the challenger's trial reads (`EncSalt.dS`) along the read program of the
EncTCR$ game (`EncSalt.saltProg`) is bounded by a potential argument over the structure of the
game, each answer block treated as a whole.

* **Potential bounds of programs** (`PotB`): the weight along a program plus the potentials of its
  leaves is at most the potential of its input plus a constant times its trace; they compose
  along sequencing (`PotB.bind`), and follow call by call (`potB_of_calls`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v

namespace Quantum.StdModel.Qrom
open Quantum QuantumRuntime
open Quantum.Xmss.Hybrid (totalWeight_le_totalWeight)

/-! ## Potential bounds of programs -/

section potBound

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
  (P : Set R.D) (lam : ℝ≥0∞) {Zk : Type} [Fintype Zk]

/-- **A potential bound of a program**: from every positive semidefinite input supported on `P`,
the weight `w` along the run plus `lam` times the potentials `Ψ p` of the leaves is at most `lam`
times the potential `K` of the input plus `c` times its trace; every leaf is supported on `P`,
and the leaves outside `Lf` are not reached. -/
def PotB {X : QReg → Type} {A : QReg} (x : QuantumComp L spec X A) (K : Matrix Zk R.D ℂ)
    (Ψ : (Σ u, X u) → Matrix Zk R.D ℂ) (c : ℝ≥0∞) (Lf : (Σ u, X u) → Prop) : Prop :=
  ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
    QuerySupportedOn (fun m : A × R.D ↦ m.2) P ρ →
    (R.totalWeight I w x ρ + lam * ∑' p, potential (Ψ p) ((R.run I x).branch p ρ) ≤
      lam * potential K ρ + c * ENNReal.ofReal ρ.trace.re) ∧
    (∀ p, QuerySupportedOn (fun m : p.1 × R.D ↦ m.2) P ((R.run I x).branch p ρ)) ∧
    ∀ p, ¬ Lf p → (R.run I x).branch p ρ = 0

variable {R I w P lam}

/-- A weaker bound: a larger constant, smaller leaf potentials, more leaves. -/
theorem PotB.mono {X : QReg → Type} {A : QReg} {x : QuantumComp L spec X A}
    {K : Matrix Zk R.D ℂ} {Ψ Ψ' : (Σ u, X u) → Matrix Zk R.D ℂ} {c c' : ℝ≥0∞}
    {Lf Lf' : (Σ u, X u) → Prop}
    (h : PotB R I w P lam x K Ψ c Lf) (hc : c ≤ c')
    (hΨ : ∀ p (τ : Matrix (p.1 × R.D) (p.1 × R.D) ℂ), τ.PosSemidef →
      potential (Ψ' p) τ ≤ potential (Ψ p) τ) (hL : ∀ p, Lf p → Lf' p) :
    PotB R I w P lam x K Ψ' c' Lf' := by
  intro ρ hρ hs
  obtain ⟨h1, h2, h3⟩ := h ρ hρ hs
  refine ⟨le_trans ?_ (h1.trans ?_), h2, fun p hp ↦ h3 p fun h ↦ hp (hL p h)⟩
  · refine add_le_add le_rfl (mul_le_mul_right (ENNReal.tsum_le_tsum fun p ↦ ?_) _)
    exact hΨ p _ ((R.run I x).posSemidef_branch_apply p hρ)
  · exact add_le_add le_rfl (mul_le_mul_left hc _)

/-- A program that stops at once. -/
theorem potB_pure {X : QReg → Type} {A : QReg} (y : X A) (K : Matrix Zk R.D ℂ)
    (Ψ : (Σ u, X u) → Matrix Zk R.D ℂ) (hΨ : Ψ ⟨A, y⟩ = K) (Lf : (Σ u, X u) → Prop)
    (hL : Lf ⟨A, y⟩) :
    PotB R I w P lam (QuantumComp.pure (L := L) (spec := spec) y) K Ψ 0 Lf := by
  classical
  intro ρ _ hs
  refine ⟨?_, fun p ↦ ?_, fun p hp ↦ ?_⟩
  · rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply, totalWeight_pure, hΨ, zero_add,
      zero_mul, add_zero]
  · rw [run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hs
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  · have hne : p ≠ ⟨_, y⟩ := fun h ↦ hp (h ▸ hL)
    rw [run_pure, DSubInstrument.branch_ret_of_ne _ hne, LinearMap.zero_apply]

omit [Fintype Zk] in
/-- One call keeps a support invariant when the step of its port does. -/
theorem querySupportedOn_queryStep_of {i : spec.Port}
    (hR : ∀ r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) P ((R.step i).branch r σ))
    {A : QReg} (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ m.2) P ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ m.2) P
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := P) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ m.2)
    (q' := fun m : spec.Out i × R.D ↦ m.2) (fun σ hσ ↦ hR r σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- **Potential bounds compose along sequencing**, for a weight given by the trace of completely
positive maps on positive semidefinite inputs: the constants add, and only the reached leaves of
the first program need a bound of their continuation. -/
theorem PotB.bind {Kc : spec.Port → Type} [∀ i, Fintype (Kc i)]
    {Φ : ∀ i, MatrixMap (spec.In i × R.D) (Kc i)} (hΦ : ∀ i, (Φ i).IsCP)
    (hw : ∀ i σ, σ.PosSemidef → w i σ = ENNReal.ofReal (Φ i σ).trace.re)
    {X Y : QReg → Type} {A : QReg} {x : QuantumComp L spec X A}
    {k : ∀ u, X u → QuantumComp L spec Y u} {K : Matrix Zk R.D ℂ}
    {Ψ : (Σ u, X u) → Matrix Zk R.D ℂ} {Ψ' : (Σ u, Y u) → Matrix Zk R.D ℂ} {c₁ c₂ : ℝ≥0∞}
    {Lf : (Σ u, X u) → Prop} {Lf' : (Σ u, Y u) → Prop}
    (hx : PotB R I w P lam x K Ψ c₁ Lf)
    (hk : ∀ p, Lf p → PotB R I w P lam (k p.1 p.2) (Ψ p) Ψ' c₂ Lf') :
    PotB R I w P lam (x.bind k) K Ψ' (c₁ + c₂) Lf' := by
  intro ρ hρ hs
  obtain ⟨hx1, hx2, hx3⟩ := hx ρ hρ hs
  have hb := fun p ↦ (R.run I x).posSemidef_branch_apply p hρ
  have hw0 : ∀ i, w i 0 = 0 := fun i ↦ by
    rw [hw i 0 PosSemidef.zero, map_zero, Matrix.trace_zero, Complex.zero_re,
      ENNReal.ofReal_zero]
  have hkp : ∀ p, (R.totalWeight I w (k p.1 p.2) ((R.run I x).branch p ρ) +
        lam * ∑' p', potential (Ψ' p') ((R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ))
          ≤ lam * potential (Ψ p) ((R.run I x).branch p ρ) +
            c₂ * ENNReal.ofReal ((R.run I x).branch p ρ).trace.re) ∧
      (∀ p', QuerySupportedOn (fun m : p'.1 × R.D ↦ m.2) P
        ((R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ))) ∧
      ∀ p', ¬ Lf' p' → (R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ) = 0 := by
    intro p
    by_cases hp : Lf p
    · exact hk p hp _ (hb p) (hx2 p)
    · rw [hx3 p hp]
      refine ⟨?_, fun p' ↦ ?_, fun p' _ ↦ map_zero _⟩
      · simp only [map_zero, QuantumRuntime.totalWeight, R.queryWeight_zero I hw0, tsum_zero,
          zero_add]
        simp [potential]
      · rw [map_zero]
        exact querySupportedOn_zero _ _
  have hconv : ∀ {B : QReg} (y : QuantumComp L spec Y B) {τ : Matrix (B × R.D) (B × R.D) ℂ},
      τ.PosSemidef → R.totalWeight I w y τ =
        R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) y τ := fun y τ hτ ↦
    le_antisymm (totalWeight_le_totalWeight R I (fun i σ hσ ↦ (hw i σ hσ).le) y hτ)
      (totalWeight_le_totalWeight R I (fun i σ hσ ↦ (hw i σ hσ).ge) y hτ)
  have hconvX : R.totalWeight I w x ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x ρ :=
    le_antisymm (totalWeight_le_totalWeight R I (fun i σ hσ ↦ (hw i σ hσ).le) x hρ)
      (totalWeight_le_totalWeight R I (fun i σ hσ ↦ (hw i σ hσ).ge) x hρ)
  have hTW : R.totalWeight I w (x.bind k) ρ = R.totalWeight I w x ρ +
      ∑' p, R.totalWeight I w (k p.1 p.2) ((R.run I x).branch p ρ) := by
    rw [hconv _ hρ, R.totalWeight_bind I hΦ x k hρ, hconvX]
    exact congrArg (_ + ·) (tsum_congr fun p ↦ (hconv _ (hb p)).symm)
  have hbr : ∀ p', (R.run I (x.bind k)).branch p' ρ =
      ∑' p, (R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ) := fun p' ↦ by
    rw [run_bind, DSubInstrument.branch_bind_apply]
  have hsum : ∀ p', Summable fun p ↦ (R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ) :=
    fun p' ↦ ((R.run I x).isCPTNIFamily.comp_eval
      (fun p ↦ (R.run I (k p.1 p.2)).isCPTNIFamily) p').summable_apply ρ
  have hpot : ∑' p', potential (Ψ' p') ((R.run I (x.bind k)).branch p' ρ) =
      ∑' p, ∑' p', potential (Ψ' p')
        ((R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ)) := by
    simp only [hbr]
    rw [← ENNReal.tsum_comm]
    exact tsum_congr fun p' ↦ Quantum.Sponge.potential_tsum _ (hsum p')
      fun p ↦ (R.run I (k p.1 p.2)).posSemidef_branch_apply p' (hb p)
  have htr : ∑' p, ENNReal.ofReal ((R.run I x).branch p ρ).trace.re ≤
      ENNReal.ofReal ρ.trace.re :=
    (R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
  refine ⟨?_, fun p' ↦ ?_, fun p' hp' ↦ ?_⟩
  · rw [hTW, hpot, ← ENNReal.tsum_mul_left, add_assoc, ← ENNReal.tsum_add]
    calc R.totalWeight I w x ρ + ∑' p, (R.totalWeight I w (k p.1 p.2) ((R.run I x).branch p ρ) +
          lam * ∑' p', potential (Ψ' p')
            ((R.run I (k p.1 p.2)).branch p' ((R.run I x).branch p ρ)))
        ≤ R.totalWeight I w x ρ + ∑' p, (lam * potential (Ψ p) ((R.run I x).branch p ρ) +
          c₂ * ENNReal.ofReal ((R.run I x).branch p ρ).trace.re) :=
          add_le_add le_rfl (ENNReal.tsum_le_tsum fun p ↦ (hkp p).1)
      _ = (R.totalWeight I w x ρ + lam * ∑' p, potential (Ψ p) ((R.run I x).branch p ρ)) +
          c₂ * ∑' p, ENNReal.ofReal ((R.run I x).branch p ρ).trace.re := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, add_assoc]
      _ ≤ (lam * potential K ρ + c₁ * ENNReal.ofReal ρ.trace.re) +
          c₂ * ENNReal.ofReal ρ.trace.re := add_le_add hx1 (mul_le_mul_right htr _)
      _ = lam * potential K ρ + (c₁ + c₂) * ENNReal.ofReal ρ.trace.re := by ring
  · rw [hbr]
    exact QuerySupportedOn.tsum fun p ↦ (hkp p).2.1 p'
  · rw [hbr]
    exact (tsum_congr fun p ↦ (hkp p).2.2 p' hp').trans tsum_zero

/-- **A potential bound call by call.** Let `x` call only ports with `bad i = 0`, within `n` of
the charge `κ`; let each such call keep the support `P` and satisfy
`w i σ + lam ∑ᵣ Φ(Uᵣ σ) ≤ lam Φ(σ) + κ i c tr σ`. Then `x` has the potential bound `n c` with the
same potential at every leaf. -/
theorem potB_of_calls (K : Matrix Zk R.D ℂ) (bad κ : spec.Port → ℕ) (c : ℝ≥0∞)
    (hstep : ∀ i, bad i = 0 → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
      w i σ + lam * ∑' r, potential K ((R.step i).branch r σ) ≤
        lam * potential K σ + κ i * c * ENNReal.ofReal σ.trace.re)
    (hP : ∀ i, bad i = 0 → ∀ r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) P ((R.step i).branch r σ))
    {X : QReg → Type} {A : QReg} (x : QuantumComp L spec X A) :
    ∀ n, IFreeM.IsChargeBound x (Quantum.Sponge.portCharge bad) 0 →
      IFreeM.IsChargeBound x (Quantum.Sponge.portCharge κ) n →
      PotB R I w P lam x K (fun _ ↦ K) (n * c) (fun _ ↦ True) := by
  classical
  induction x using QuantumComp.inductionOn with
  | pure B y =>
    intro n _ _
    exact (potB_pure y K _ rfl _ trivial).mono zero_le (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
  | primBind B o k ih =>
    intro n hb hκ ρ hρ hs
    rw [Quantum.Sponge.isChargeBound_portCharge_primBind_iff] at hb hκ
    have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    have hsb : ∀ b, QuerySupportedOn (fun m : L.next o b × R.D ↦ m.2) P
        (((I o).frame R.D).branch b ρ) := fun b ↦ by
      rw [DSubInstrument.branch_frame_apply]
      exact QuerySupportedOn.amplify_snd (q := id) hs _
    have hkb := fun b ↦ ih b n (hb b) (hκ b) _ (hρb b) (hsb b)
    have hbr : ∀ p, (R.run I (QuantumComp.primBind o k)).branch p ρ =
        ∑' b, (R.run I (k b)).branch p (((I o).frame R.D).branch b ρ) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
    refine ⟨?_, fun p ↦ ?_, fun _ h ↦ absurd trivial h⟩
    · have hpot : ∑' p, potential K ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
          ∑' b, ∑' p, potential K ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) := by
        simp only [hbr]
        rw [← ENNReal.tsum_comm]
        exact tsum_congr fun p ↦ Quantum.Sponge.potential_tsum _
          ((((I o).frame R.D).isCPTNIFamily.comp_eval
            (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
          fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
      rw [totalWeight_primBind, hpot, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      calc ∑' b, (R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ) +
            lam * ∑' p, potential K ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
          ≤ ∑' b, (lam * potential K (((I o).frame R.D).branch b ρ) +
            n * c * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) :=
            ENNReal.tsum_le_tsum fun b ↦ (hkb b).1
        _ = lam * ∑' b, potential K (((I o).frame R.D).branch b ρ) +
            n * c * ∑' b, ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ ≤ lam * potential K ρ + n * c * ENNReal.ofReal ρ.trace.re :=
            add_le_add (mul_le_mul_right (tsum_potential_frame_le K (I o) hρ) _)
              (mul_le_mul_right (((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ) _)
    · rw [hbr]
      exact QuerySupportedOn.tsum fun b ↦ (hkb b).2.1 p
  | queryBind B i E ℓ k ih =>
    intro n hb hκ ρ hρ hs
    rw [Quantum.Sponge.isChargeBound_portCharge_queryBind_iff] at hb hκ
    have hi : bad i = 0 := Nat.le_zero.mp hb.1
    have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hsr := fun r ↦ querySupportedOn_queryStep_of (P := P) (hP i hi) E ℓ r hs
    have hkr := fun r ↦ ih r (n - κ i) ((hb.2 r).mono (by omega)) (hκ.2 r) _ (hρr r)
      (hsr r)
    have hbr : ∀ p, (R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ =
        ∑' r, (R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
    refine ⟨?_, fun p ↦ ?_, fun _ h ↦ absurd trivial h⟩
    · have hpot : ∑' p, potential K ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
          ∑' r, ∑' p, potential K ((R.run I (k r)).branch p
            ((R.queryStep i E ℓ).branch r ρ)) := by
        simp only [hbr]
        rw [← ENNReal.tsum_comm]
        exact tsum_congr fun p ↦ Quantum.Sponge.potential_tsum _
          (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
            (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
          fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
      have hstep' := hstep i hi _ (posSemidef_callInput ℓ hρ)
        (QuerySupportedOn.callInput (g := id) hs ℓ)
      rw [potential_callInput, trace_callInput] at hstep'
      have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
          ENNReal.ofReal ρ.trace.re :=
        (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
      rw [totalWeight_queryBind, hpot, ← ENNReal.tsum_mul_left, add_assoc, ← ENNReal.tsum_add]
      calc w i (callInput ℓ R.D ρ) + ∑' r, (R.totalWeight I w (k r)
            ((R.queryStep i E ℓ).branch r ρ) + lam * ∑' p, potential K
              ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)))
          ≤ w i (callInput ℓ R.D ρ) + ∑' r, (lam * potential K
              ((R.queryStep i E ℓ).branch r ρ) + (n - κ i : ℕ) * c *
                ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) :=
            add_le_add le_rfl (ENNReal.tsum_le_tsum fun r ↦ (hkr r).1)
        _ = (w i (callInput ℓ R.D ρ) + lam * ∑' r, potential K
              ((R.step i).branch r (callInput ℓ R.D ρ))) +
            (n - κ i : ℕ) * c *
              ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, add_assoc]
            simp only [potential_queryStep]
        _ ≤ (lam * potential K ρ + κ i * c * ENNReal.ofReal ρ.trace.re) +
            (n - κ i : ℕ) * c * ENNReal.ofReal ρ.trace.re :=
            add_le_add hstep' (mul_le_mul_right htr _)
        _ = lam * potential K ρ + n * c * ENNReal.ofReal ρ.trace.re := by
            have hn : (n : ℝ≥0∞) = κ i + (n - κ i : ℕ) := by
              rw [← Nat.cast_add]
              exact congrArg _ (by omega)
            rw [hn]
            ring
    · rw [hbr]
      exact QuerySupportedOn.tsum fun r ↦ (hkr r).2.1 p

/-- A bound from a smaller input potential. -/
theorem PotB.mono_in {X : QReg → Type} {A : QReg} {x : QuantumComp L spec X A}
    {K K' : Matrix Zk R.D ℂ} {Ψ : (Σ u, X u) → Matrix Zk R.D ℂ} {c : ℝ≥0∞}
    {Lf : (Σ u, X u) → Prop} (h : PotB R I w P lam x K Ψ c Lf)
    (hK : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef → potential K ρ ≤ potential K' ρ) :
    PotB R I w P lam x K' Ψ c Lf := by
  intro ρ hρ hs
  obtain ⟨h1, h2, h3⟩ := h ρ hρ hs
  exact ⟨h1.trans (add_le_add (mul_le_mul_right (hK ρ hρ) _) le_rfl), h2, h3⟩

/-- A program on a fixed final register that stops at once. -/
theorem potB_pure₂ {A : QReg} {α : Type} (a : α) (K : Matrix Zk R.D ℂ) (Ψ : α → Matrix Zk R.D ℂ)
    (hΨ : Ψ a = K) (Lf : α → Prop) (hL : Lf a) :
    PotB R I w P lam (QuantumComp₂.pure (L := L) (spec := spec) (A := A) a) K
      (fun p ↦ Ψ p.2.2) 0 (fun p ↦ Lf p.2.2) :=
  potB_pure (X := QuantumComp₂.Leaf A α) ⟨rfl, a⟩ K _ hΨ _ hL

/-- **Sequencing on fixed final registers**: the bound of `x`, then of `k a` at each reached
value `a`. -/
theorem PotB.bind₂ {Kc : spec.Port → Type} [∀ i, Fintype (Kc i)]
    {Φ : ∀ i, MatrixMap (spec.In i × R.D) (Kc i)} (hΦ : ∀ i, (Φ i).IsCP)
    (hw : ∀ i σ, σ.PosSemidef → w i σ = ENNReal.ofReal (Φ i σ).trace.re)
    {A B C : QReg} {α β : Type} {x : QuantumComp₂ L spec A B α}
    {k : α → QuantumComp₂ L spec B C β} {K : Matrix Zk R.D ℂ} {Ψ : α → Matrix Zk R.D ℂ}
    {Ψ' : (Σ u, QuantumComp₂.Leaf C β u) → Matrix Zk R.D ℂ} {c₁ c₂ : ℝ≥0∞} {Lf : α → Prop}
    {Lf' : (Σ u, QuantumComp₂.Leaf C β u) → Prop}
    (hx : PotB R I w P lam x K (fun p ↦ Ψ p.2.2) c₁ (fun p ↦ Lf p.2.2))
    (hk : ∀ a, Lf a → PotB R I w P lam (k a) (Ψ a) Ψ' c₂ Lf') :
    PotB R I w P lam (x.bind k) K Ψ' (c₁ + c₂) Lf' := by
  show PotB R I w P lam (QuantumComp.bind x fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a) K Ψ'
    (c₁ + c₂) Lf'
  refine PotB.bind hΦ hw hx fun p hp ↦ ?_
  obtain ⟨u, rfl, a⟩ := p
  exact hk a hp

/-- **Sequencing on fixed final registers**, the bound of `x` with any leaf potentials. -/
theorem PotB.bind₂' {Kc : spec.Port → Type} [∀ i, Fintype (Kc i)]
    {Φ : ∀ i, MatrixMap (spec.In i × R.D) (Kc i)} (hΦ : ∀ i, (Φ i).IsCP)
    (hw : ∀ i σ, σ.PosSemidef → w i σ = ENNReal.ofReal (Φ i σ).trace.re)
    {A B C : QReg} {α β : Type} {x : QuantumComp₂ L spec A B α}
    {k : α → QuantumComp₂ L spec B C β} {K : Matrix Zk R.D ℂ}
    {Ψ : (Σ u, QuantumComp₂.Leaf B α u) → Matrix Zk R.D ℂ}
    {Ψ' : (Σ u, QuantumComp₂.Leaf C β u) → Matrix Zk R.D ℂ} {c₁ c₂ : ℝ≥0∞}
    {Lf : (Σ u, QuantumComp₂.Leaf B α u) → Prop} {Lf' : (Σ u, QuantumComp₂.Leaf C β u) → Prop}
    (hx : PotB R I w P lam x K Ψ c₁ Lf)
    (hk : ∀ a, Lf ⟨B, rfl, a⟩ → PotB R I w P lam (k a) (Ψ ⟨B, rfl, a⟩) Ψ' c₂ Lf') :
    PotB R I w P lam (x.bind k) K Ψ' (c₁ + c₂) Lf' := by
  show PotB R I w P lam (QuantumComp.bind x fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a) K Ψ'
    (c₁ + c₂) Lf'
  refine PotB.bind hΦ hw hx fun p hp ↦ ?_
  obtain ⟨u, rfl, a⟩ := p
  exact hk a hp

/-- A bound transported along an equality of programs. -/
theorem PotB.of_eq {X : QReg → Type} {A : QReg} {x y : QuantumComp L spec X A}
    {K : Matrix Zk R.D ℂ} {Ψ : (Σ u, X u) → Matrix Zk R.D ℂ} {c : ℝ≥0∞}
    {Lf : (Σ u, X u) → Prop} (h : x = y) (hy : PotB R I w P lam y K Ψ c Lf) :
    PotB R I w P lam x K Ψ c Lf :=
  h ▸ hy

end potBound

/-! ## Counting potentials on the hardwired register -/

section count

open Quantum.Sponge (HwReg hwSpec hwEmpty hwReadKraus spongeHardwired diagPot OneCellLipschitz
  SpongePort)
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

open scoped Classical in
/-- **The recorded cells of `h` in `Y`**, counted. -/
noncomputable def cntY (Y : Set Z) (s : HwReg X Z M) : ℝ :=
  ((Finset.univ.filter fun y ↦ y ∈ Y ∧ s.1.1 y ≠ none).card : ℝ)

omit [Fintype X] [DecidableEq X] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem cntY_nonneg (Y : Set Z) (s : HwReg X Z M) : 0 ≤ cntY Y s :=
  Nat.cast_nonneg _

omit [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- The count of `Y` is the count off the cell `z` plus that cell. -/
theorem cntY_split (Y : Set Z) (z : Z) (s : HwReg X Z M) :
    cntY Y s = cntY (Y \ {z}) s + if z ∈ Y ∧ s.1.1 z ≠ none then 1 else 0 := by
  unfold cntY
  split_ifs with hz
  · rw [show (Finset.univ.filter fun y ↦ y ∈ Y ∧ s.1.1 y ≠ none) =
        insert z (Finset.univ.filter fun y ↦ y ∈ Y \ {z} ∧ s.1.1 y ≠ none) by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Set.mem_sdiff, Set.mem_singleton_iff]
      by_cases hy : y = z
      · subst hy
        exact iff_of_true hz (Or.inl rfl)
      · simp only [hy, false_or, not_false_eq_true, and_true],
      Finset.card_insert_of_notMem (by simp), Nat.cast_add, Nat.cast_one]
    congr
  · rw [add_zero]
    congr 2
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
      Set.mem_singleton_iff]
    by_cases hy : y = z
    · subst hy
      simp only [not_true_eq_false, and_false, false_and, iff_false]
      exact hz
    · simp only [hy, not_false_eq_true, and_true]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] [Fintype M] [DecidableEq M] in
/-- The count off the cell `z` sees neither that cell nor the memory. -/
theorem offCell_cntY (Y : Set Z) (z : Z) :
    Quantum.Xmss.Assembly.OffCell z (cntY (X := X) (M := M) (Y \ {z})) := by
  intro s s' h1 _ _
  unfold cntY
  congr 2
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, hn⟩
    exact ⟨hy, by rwa [← h1 y hy.2]⟩
  · rintro ⟨hy, hn⟩
    exact ⟨hy, by rwa [h1 y hy.2]⟩

omit [Fintype X] [Fintype M] [DecidableEq M] in
/-- **A count of recorded cells is one-cell Lipschitz.** -/
theorem oneCellLipschitz_cntY (Y : Set Z) : OneCellLipschitz (cntY (X := X) (M := M) Y) where
  h D b z v := by
    classical
    show ((Finset.univ.filter fun y ↦ y ∈ Y ∧ Function.update D.1 z v y ≠ none).card : ℝ) ≤
      ((Finset.univ.filter fun y ↦ y ∈ Y ∧ D.1 y ≠ none).card : ℝ) + 1
    have hsub : (Finset.univ.filter fun y ↦ y ∈ Y ∧ Function.update D.1 z v y ≠ none) ⊆
        insert z (Finset.univ.filter fun y ↦ y ∈ Y ∧ D.1 y ≠ none) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hy ⊢
      by_cases hyz : y = z
      · exact Or.inl hyz
      · rw [Function.update_of_ne hyz] at hy
        exact Or.inr hy
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  k _ _ _ _ := le_add_of_nonneg_right zero_le_one
  k' _ _ _ _ := le_add_of_nonneg_right zero_le_one

omit [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] in
/-- Counts of disjoint sets add. -/
theorem cntY_union (A B : Set Z) (h : Disjoint A B) (s : HwReg X Z M) :
    cntY (A ∪ B) s = cntY A s + cntY B s := by
  classical
  unfold cntY
  rw [← Nat.cast_add, ← Finset.card_union_of_disjoint]
  · congr 2
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Set.mem_union]
    tauto
  · rw [Finset.disjoint_filter]
    intro y _ ha hb
    exact Set.disjoint_left.mp h ha.1 hb.1

omit [Fintype X] [DecidableEq X] [DecidableEq Z] [Fintype M] [DecidableEq M] in
/-- Counts grow with the set. -/
theorem cntY_mono {A B : Set Z} (h : A ⊆ B) (s : HwReg X Z M) : cntY A s ≤ cntY B s := by
  unfold cntY
  exact_mod_cast Finset.card_le_card fun y hy ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact ⟨h hy.1, hy.2⟩

/-- Diagonal potentials grow with their weight. -/
theorem potential_diagPot_mono {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {f g : β → ℝ} (hf : ∀ s, 0 ≤ f s) (hfg : ∀ s, f s ≤ g s)
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) :
    potential (diagPot fun s ↦ √(f s)) ρ ≤ potential (diagPot fun s ↦ √(g s)) ρ := by
  rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt hf,
    Quantum.Xmss.Assembly.potential_diagPot_sqrt fun s ↦ (hf s).trans (hfg s)]
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦
    mul_le_mul_of_nonneg_right (hfg q.2) (Complex.nonneg_iff.1 hρ.diag_nonneg).1)

/-- Diagonal potentials add. -/
theorem potential_diagPot_add {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {f g : β → ℝ} (hf : ∀ s, 0 ≤ f s) (hg : ∀ s, 0 ≤ g s)
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) :
    potential (diagPot fun s ↦ √(f s + g s)) ρ =
      potential (diagPot fun s ↦ √(f s)) ρ + potential (diagPot fun s ↦ √(g s)) ρ := by
  have hd : ∀ q, 0 ≤ (ρ q q).re := fun q ↦ (Complex.nonneg_iff.1 hρ.diag_nonneg).1
  rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt fun s ↦ add_nonneg (hf s) (hg s),
    Quantum.Xmss.Assembly.potential_diagPot_sqrt hf,
    Quantum.Xmss.Assembly.potential_diagPot_sqrt hg,
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf _) (hd q))
      (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hg _) (hd q)), ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ ↦ add_mul _ _ _

/-- **A diagonal weight linear in a count**: `∑ ℓ ρ ≤ a Φ_g(ρ) + b tr ρ` when `ℓ ≤ a g + b`. -/
theorem ofReal_sum_le_potential {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (ℓ g : β → ℝ) (hg : ∀ s, 0 ≤ g s) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hℓ : ∀ s, ℓ s ≤ a * g s + b) {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef) :
    ENNReal.ofReal (∑ q, ℓ q.2 * (ρ q q).re) ≤
      ENNReal.ofReal a * potential (diagPot fun s ↦ √(g s)) ρ +
        ENNReal.ofReal b * ENNReal.ofReal ρ.trace.re := by
  have hd : ∀ q, 0 ≤ (ρ q q).re := fun q ↦ (Complex.nonneg_iff.1 hρ.diag_nonneg).1
  have htr : ρ.trace.re = ∑ q, (ρ q q).re := by
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt hg, ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add
      (mul_nonneg ha (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hg _) (hd q)))
      (mul_nonneg hb (htr ▸ Finset.sum_nonneg fun q _ ↦ hd q))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [htr, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have h1 := mul_le_mul_of_nonneg_right (hℓ q.2) (hd q)
  nlinarith

/-- A nonnegative diagonal weight is the trace of the conjugation by the diagonal of its square
roots. -/
theorem ofReal_sum_diag_eq {n : Type} [Fintype n] [DecidableEq n] (f : n → ℝ)
    (hf : ∀ q, 0 ≤ f q) (σ : Matrix n n ℂ) :
    ENNReal.ofReal (∑ q, f q * (σ q q).re) =
      ENNReal.ofReal (MatrixMap.conj (diagonal fun q ↦ ((√(f q) : ℝ) : ℂ)) σ).trace.re := by
  congr 1
  rw [MatrixMap.trace_conj_apply]
  have hK : (diagonal fun q ↦ ((√(f q) : ℝ) : ℂ))ᴴ * diagonal (fun q ↦ ((√(f q) : ℝ) : ℂ)) =
      diagonal fun q ↦ ((f q : ℝ) : ℂ) := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext q
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hf q)]
  rw [hK]
  simp only [Matrix.trace, Matrix.diag, diagonal_mul, Complex.re_sum, Complex.re_ofReal_mul]

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]

/-- **A sponge call raises the count by at most the trace.** -/
theorem tsum_potential_cntY_sponge (m₀ : M) (Y : Set Z) (p : SpongePort)
    {σ : Matrix ((hwSpec X Z M).In (.inl (.inl p)) × (runtime2 X Z m₀).D)
      ((hwSpec X Z M).In (.inl (.inl p)) × (runtime2 X Z m₀).D) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s))
        (((runtime2 X Z m₀).step (.inl (.inl p))).branch r σ) ≤
      potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s)) σ + ENNReal.ofReal σ.trace.re := by
  have hb : ∀ r, ((runtime2 X Z m₀).step (.inl (.inl p))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ := fun r ↦
    LinearMap.congr_fun (runtime2_branch m₀ _ r) σ
  simp only [hb]
  exact Quantum.Xmss.Assembly.tsum_potential_sponge_le (cntY_nonneg Y) (oneCellLipschitz_cntY Y)
    _ m₀ p hσ

open scoped Classical in
/-- **A read of the cell `z` raises the count by at most the trace**, and keeps it off `Y`. -/
theorem tsum_potential_cntY_readH (m₀ : M) (Y : Set Z) (z : Z) (u : M → Option X → M)
    {σ : Matrix ((hwSpec X Z M).In (.inl (.inr (.readH z u))) × (runtime2 X Z m₀).D)
      ((hwSpec X Z M).In (.inl (.inr (.readH z u))) × (runtime2 X Z m₀).D) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' r, potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s))
        (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ) ≤
      potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s)) σ +
        ((if z ∈ Y then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re := by
  set f₀ : HwReg X Z M → ℝ := cntY (Y \ {z})
  set h : HwReg X Z M → ℝ := fun s ↦ if z ∈ Y ∧ s.1.1 z ≠ none then 1 else 0
  have hf0 : ∀ s, 0 ≤ f₀ s := cntY_nonneg _
  have hh0 : ∀ s, 0 ≤ h s := fun s ↦ by
    simp only [h]
    split_ifs <;> norm_num
  have hL : ∀ s, h s ≤ ((if z ∈ Y then 1 else 0 : ℕ) : ℝ) := fun s ↦ by
    simp only [h]
    split_ifs with h1 h2 <;> norm_num
    exact h2 h1.1
  have hdiag : ∀ {τ : Matrix ((hwSpec X Z M).In (.inl (.inr (.readH z u))) × (runtime2 X Z m₀).D)
      ((hwSpec X Z M).In (.inl (.inr (.readH z u))) × (runtime2 X Z m₀).D) ℂ},
      τ.PosSemidef → ∀ q, 0 ≤ (τ q q).re := fun hτ q ↦ (Complex.nonneg_iff.1 hτ.diag_nonneg).1
  have hsplit : ∀ {τ : Matrix ((hwSpec X Z M).In (.inl (.inr (.readH z u))) ×
      (runtime2 X Z m₀).D) ((hwSpec X Z M).In (.inl (.inr (.readH z u))) ×
        (runtime2 X Z m₀).D) ℂ}, τ.PosSemidef →
      potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s)) τ =
        potential (diagPot fun s ↦ √(f₀ s)) τ + potential (diagPot fun s ↦ √(h s)) τ := by
    intro τ hτ
    rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt (cntY_nonneg Y),
      Quantum.Xmss.Assembly.potential_diagPot_sqrt hf0,
      Quantum.Xmss.Assembly.potential_diagPot_sqrt hh0,
      ← ENNReal.ofReal_add (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf0 _) (hdiag hτ q))
        (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hh0 _) (hdiag hτ q)),
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [cntY_split Y z q.2, add_mul]
  have hhle : ∀ {τ : Matrix ((hwSpec X Z M).In (.inl (.inr (.readH z u))) ×
      (runtime2 X Z m₀).D) ((hwSpec X Z M).In (.inl (.inr (.readH z u))) ×
        (runtime2 X Z m₀).D) ℂ}, τ.PosSemidef →
      potential (diagPot fun s ↦ √(h s)) τ ≤
        ((if z ∈ Y then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal τ.trace.re := by
    intro τ hτ
    rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt hh0, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right (hL q.2) (hdiag hτ q)
  have hpsd := fun r ↦
    ((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).posSemidef_branch_apply r hσ
  have hbr : ∀ r, ((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ =
      MatrixMap.conj (hwReadKraus (.readH z u) r) σ := fun r ↦
    LinearMap.congr_fun (runtime2_branch m₀ _ r) σ
  have h0 : ∑' r, potential (diagPot fun s ↦ √(f₀ s))
      (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ) ≤
        potential (diagPot fun s ↦ √(f₀ s)) σ := by
    simp only [hbr]
    exact Quantum.Xmss.Assembly.tsum_potential_readH_le hf0 (offCell_cntY Y z) u hσ
  calc ∑' r, potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s))
        (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ)
      = ∑' r, (potential (diagPot fun s ↦ √(f₀ s))
          (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ) +
        potential (diagPot fun s ↦ √(h s))
          (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ)) :=
        tsum_congr fun r ↦ hsplit (hpsd r)
    _ ≤ potential (diagPot fun s ↦ √(f₀ s)) σ + ((if z ∈ Y then 1 else 0 : ℕ) : ℝ≥0∞) *
        ∑' r, ENNReal.ofReal
          (((runtime2 X Z m₀).step (.inl (.inr (.readH z u)))).branch r σ).trace.re := by
        rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        exact add_le_add h0 (ENNReal.tsum_le_tsum fun r ↦ hhle (hpsd r))
    _ ≤ potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s)) σ +
        ((if z ∈ Y then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re := by
        gcongr
        · rw [hsplit hσ]
          exact le_self_add
        · exact ((runtime2 X Z m₀).step _).isCPTNIFamily.tsum_ofReal_trace_re_le hσ

/-- **The sponge and read ports keep the empty hardwired part.** -/
theorem querySupportedOn_step_hwEmpty (m₀ : M) (i : (hwSpec X Z M).Port)
    (hi : (∃ p, i = .inl (.inl p)) ∨ ∃ z u, i = .inl (.inr (.readH z u)))
    (r : (hwSpec X Z M).Result i)
    (σ : Matrix ((hwSpec X Z M).In i × (runtime2 X Z m₀).D)
      ((hwSpec X Z M).In i × (runtime2 X Z m₀).D) ℂ)
    (h : QuerySupportedOn (fun m : (hwSpec X Z M).In i × (runtime2 X Z m₀).D ↦ m.2)
      {s : HwReg X Z M | s.2.1 = hwEmpty X Z} σ) :
    QuerySupportedOn (fun m : (hwSpec X Z M).Out i × (runtime2 X Z m₀).D ↦ m.2)
      {s : HwReg X Z M | s.2.1 = hwEmpty X Z} (((runtime2 X Z m₀).step i).branch r σ) := by
  rw [LinearMap.congr_fun (runtime2_branch m₀ i r) σ]
  rcases hi with ⟨p, rfl⟩ | ⟨z, u, rfl⟩
  · refine h.conj fun m' m hK hm ↦ ?_
    obtain ⟨a', s'⟩ := m'
    obtain ⟨a, s⟩ := m
    have := Quantum.Sponge.snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ p a a' s s' hK
    change s'.2.1 = hwEmpty X Z
    rw [this]
    exact hm
  · refine h.conj fun m' m hK hm ↦ ?_
    obtain ⟨a', s'⟩ := m'
    obtain ⟨a, s⟩ := m
    change s'.2.1 = hwEmpty X Z
    rw [Quantum.Sponge.hw_eq_of_hwReadKraus_ne_zero (.readH z u) r a a' s s' hK]
    exact hm

theorem runtime2_init_matrix (m₀ : M) :
    (runtime2 X Z m₀).init.matrix = Matrix.single
      (((Quantum.Database.empty, Quantum.Database.empty, Quantum.Database.empty), hwEmpty X Z,
        m₀) : HwReg X Z M)
      ((Quantum.Database.empty, Quantum.Database.empty, Quantum.Database.empty), hwEmpty X Z,
        m₀) 1 :=
  rfl

/-- **The count at the start is zero**: the databases are empty. -/
theorem potential_cntY_init {B : Type} [Fintype B] [DecidableEq B] (m₀ : M) (Y : Set Z) (u : B) :
    potential (diagPot fun s : HwReg X Z M ↦ √(cntY Y s))
      ((SubState.basis u).matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) = 0 := by
  rw [Quantum.Xmss.Assembly.potential_diagPot_sqrt (cntY_nonneg Y)]
  have h0 : cntY Y (((Quantum.Database.empty, Quantum.Database.empty, Quantum.Database.empty),
      hwEmpty X Z, m₀) : HwReg X Z M) = 0 := by
    unfold cntY
    simp [Quantum.Database.empty]
  rw [runtime2_init_matrix, SubState.matrix_basis, single_kronecker_single, one_mul,
    Finset.sum_eq_zero fun q _ ↦ ?_, ENNReal.ofReal_zero]
  rw [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, -⟩ := h
    simp [h0]
  · simp

/-- The start has no hardwired cell. -/
theorem querySupportedOn_init_hw {B : Type} [Fintype B] [DecidableEq B] (m₀ : M) (u : B) :
    QuerySupportedOn (fun m : B × HwReg X Z M ↦ m.2) {s : HwReg X Z M | s.2.1 = hwEmpty X Z}
      ((SubState.basis u).matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) := by
  intro a b h
  rw [runtime2_init_matrix, SubState.matrix_basis, single_kronecker_single, Matrix.single_apply]
    at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact ⟨rfl, rfl⟩
  · exact absurd rfl h

end count

end Quantum.StdModel.Qrom

/-! ## EncTCR$: the challenger's trial reads along the game -/

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Sponge Quantum.Qrom HashSig Props OracleComp OracleSpec Common
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)
open Tcr (Mem IsG GCell GSep uRed uJudge BadR)

section calls

/-- The runtime register with no hardwired cell. -/
def Hw0 : Set (HwReg HashOutput HashDomain Mem) :=
  {s | s.2.1 = hwEmpty HashOutput HashDomain}

/-- The potential of the count of the recorded cells of `h` in `Y`. -/
noncomputable abbrev potK (Y : Set HashDomain) :
    Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ :=
  diagPot fun s : HwReg HashOutput HashDomain Mem ↦ √(cntY Y s)

open scoped Classical in
/-- The ports the trial-read weight `dS` does not see: the sponge ports and the reads with the
reduction's or the decision's policy. -/
noncomputable def badS : (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (.readH z u)) => if u = uRed z ∨ u = uJudge z then 0 else 1
  | _ => 1

/-- The sponge ports and the reads of `h`. -/
def badR : (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr (.readH _ _)) => 0
  | _ => 1

open scoped Classical in
/-- The charge of the count of `Y`: a sponge call, a read of a cell of `Y`. -/
noncomputable def kapY (Y : Set HashDomain) : (hwSpec HashOutput HashDomain Mem).Port → ℕ
  | .inl (.inl _) => 1
  | .inl (.inr (.readH z _)) => if z ∈ Y then 1 else 0
  | _ => 0

open scoped Classical in
/-- The classical queries of the model hitting `Y`. -/
noncomputable def hitY (Y : Set HashDomain) : romWorld.Oracles.Domain → ℕ
  | .inl _ => 0
  | .inr z => if z ∈ Y then 1 else 0

theorem badR_eq_zero_of_badS {i : (hwSpec HashOutput HashDomain Mem).Port} (h : badS i = 0) :
    badR i = 0 := by
  rcases i with (p | c) | c
  · rfl
  · cases c with
    | readH z u => rfl
    | readK _ _ => exact absurd h (by simp [badS])
    | readK' _ _ => exact absurd h (by simp [badS])
  · exact absurd h (by simp [badS])

theorem dS_eq_zero_of_badS {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)
    {i : (hwSpec HashOutput HashDomain Mem).Port} (h : badS i = 0)
    (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem) ℂ) :
    dS e i σ = 0 := by
  rcases i with (p | c) | c
  · rfl
  · cases c with
    | readH z u =>
      have hu : u = uRed z ∨ u = uJudge z := by
        by_contra hu
        simp [badS, hu] at h
      simp [dS, hu]
    | readK _ _ => rfl
    | readK' _ _ => rfl
  · rfl

open scoped Classical in
/-- **A call of a sponge port or a read raises the count of `Y` by its charge**, a call no
weight sees. -/
theorem step_cntY (w : ∀ i, Matrix ((hwSpec HashOutput HashDomain Mem).In i ×
      (runtime2 HashOutput HashDomain mem0).D)
      ((hwSpec HashOutput HashDomain Mem).In i × (runtime2 HashOutput HashDomain mem0).D) ℂ →
        ℝ≥0∞)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) (hbad : ∀ i, bad i = 0 → badR i = 0)
    (hw : ∀ i σ, bad i = 0 → w i σ = 0) (lam : ℝ≥0∞) (Y : Set HashDomain) :
    ∀ i, bad i = 0 → ∀ σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i ×
        (runtime2 HashOutput HashDomain mem0).D)
        ((hwSpec HashOutput HashDomain Mem).In i × (runtime2 HashOutput HashDomain mem0).D) ℂ,
      σ.PosSemidef → QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
        (runtime2 HashOutput HashDomain mem0).D ↦ m.2) Hw0 σ →
      w i σ + lam * ∑' r, potential (potK Y)
          (((runtime2 HashOutput HashDomain mem0).step i).branch r σ) ≤
        lam * potential (potK Y) σ + kapY Y i * lam * ENNReal.ofReal σ.trace.re := by
  intro i hi σ hσ _
  rw [hw i σ hi, zero_add]
  rcases i with (p | c) | c
  · have h := tsum_potential_cntY_sponge mem0 Y p hσ
    calc lam * ∑' r, potential (potK Y)
          (((runtime2 HashOutput HashDomain mem0).step (.inl (.inl p))).branch r σ)
        ≤ lam * (potential (potK Y) σ + ENNReal.ofReal σ.trace.re) := mul_le_mul_right h _
      _ = lam * potential (potK Y) σ +
          kapY Y (.inl (.inl p)) * lam * ENNReal.ofReal σ.trace.re := by
        simp only [kapY, Nat.cast_one, one_mul]
        ring
  · cases c with
    | readH z u =>
      have h := tsum_potential_cntY_readH mem0 Y z u hσ
      calc lam * ∑' r, potential (potK Y)
            (((runtime2 HashOutput HashDomain mem0).step (.inl (.inr (.readH z u)))).branch r σ)
          ≤ lam * (potential (potK Y) σ +
            ((if z ∈ Y then 1 else 0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) :=
            mul_le_mul_right h _
        _ = lam * potential (potK Y) σ +
            kapY Y (.inl (.inr (.readH z u))) * lam * ENNReal.ofReal σ.trace.re := by
          simp only [kapY]
          ring
    | readK _ _ => exact absurd (hbad _ hi) (by simp [badR])
    | readK' _ _ => exact absurd (hbad _ hi) (by simp [badR])
  · exact absurd (hbad _ hi) (by simp [badR])

/-- The calls with `badR i = 0` keep the empty hardwired part. -/
theorem step_hw0 (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ)
    (hbad : ∀ i, bad i = 0 → badR i = 0) :
    ∀ i, bad i = 0 → ∀ r (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i ×
        (runtime2 HashOutput HashDomain mem0).D)
        ((hwSpec HashOutput HashDomain Mem).In i × (runtime2 HashOutput HashDomain mem0).D) ℂ),
      QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).In i ×
        (runtime2 HashOutput HashDomain mem0).D ↦ m.2) Hw0 σ →
      QuerySupportedOn (fun m : (hwSpec HashOutput HashDomain Mem).Out i ×
        (runtime2 HashOutput HashDomain mem0).D ↦ m.2) Hw0
        (((runtime2 HashOutput HashDomain mem0).step i).branch r σ) := by
  intro i hi r σ h
  refine querySupportedOn_step_hwEmpty mem0 i ?_ r σ h
  have h0 := hbad i hi
  rcases i with (p | c) | c
  · exact Or.inl ⟨p, rfl⟩
  · cases c with
    | readH z u => exact Or.inr ⟨z, u, rfl⟩
    | readK _ _ => exact absurd h0 (by simp [badR])
    | readK' _ _ => exact absurd h0 (by simp [badR])
  · exact absurd h0 (by simp [badR])

/-- One step of a charge bound on a command tree: normalize the head, then split the command. -/
local macro "chg_step" : tactic => `(tactic| (
  (conv => arg 1; whnf);
  refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨?_, fun _ ↦ ?_⟩))

/-- **The charges of the read program of a mixed program**: a hash call becomes a sponge call, a
tagged call of a hash a read with its caller's policy, and a tagged coin local operations. -/
theorem isChargeBound_readProgOf (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    (κm : (MixSpec Caller).Port → ℕ) (κr : (hwSpec HashOutput HashDomain Mem).Port → ℕ)
    (hS : ∀ p p', κr (.inl (.inl p')) ≤ κm (.hash p))
    (hR : ∀ c z, κr (.inl (.inr (.readH z (u c z)))) ≤ κm (.call (c, .inr z)))
    {Ω : QReg → Type} {A : QReg}
    {x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A}
    {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge κm) n) :
    IFreeM.IsChargeBound (readProgOf u x) (portCharge κr) n := by
  rw [readProgOf, ← IFreeM.substitute_toSubstitution,
    Quantum.Xmss.Assembly.substitute_substitute]
  refine IFreeM.IsChargeBound.substitute _ (fun A c ↦ ?_) hx
  rcases c with o | ⟨p | ⟨tag, k | z⟩, E, ℓ⟩
  · chg_step
    · exact Nat.zero_le _
    · exact IFreeM.isChargeBound_pure _ _
  · chg_step
    · exact hS p _
    · exact IFreeM.isChargeBound_pure _ _
  · chg_step
    · exact Nat.zero_le _
    chg_step
    · exact Nat.zero_le _
    · exact IFreeM.isChargeBound_pure _ _
  · chg_step
    · exact Nat.zero_le _
    chg_step
    · exact hR tag z
    chg_step
    · exact Nat.zero_le _
    · exact IFreeM.isChargeBound_pure _ _

/-- A tagged call costs its charge. -/
theorem isChargeBound_mixImpl_cost (κm : (MixSpec Caller).Port → ℕ) (c : Caller) (B : QReg)
    (i : RomOracles.Domain) :
    IFreeM.IsChargeBound (mixImpl c B i) (cmdCharge κm) (κm (.call (c, i))) := by
  unfold mixImpl callQ
  exact (FreeM₂.isChargeBound_bind (n₁ := κm (.call (c, i))) (n₂ := 0)
    (isChargeBound_query₂ (S := romWorld.spec) κm (.call (c, i)) B
      (callSplit romWorld (tagSpec Caller) (c, i) B)) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0).mono (by omega)

/-- **A classical algorithm by tagged calls costs the charges of its queries.** -/
theorem isChargeBound_toQuantumAt_cost (κm : (MixSpec Caller).Port → ℕ) (c : Caller)
    (B : QReg) {α : Type} (oa : OracleComp romWorld.Oracles α) :
    ∀ n, QueryCostAtMost oa (fun t ↦ κm (.call (c, t))) n →
      IFreeM.IsChargeBound (oa.toQuantumAt (mixImpl c B)) (cmdCharge κm) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ _ ↦ trivial
  | query_bind i k ih =>
    intro n h
    rw [isWeightBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    exact (FreeM₂.isChargeBound_bind (n₁ := κm (.call (c, i))) (n₂ := n - κm (.call (c, i)))
      (isChargeBound_mixImpl_cost κm c B i) fun a ↦ ih a _ (h.2 a)).mono (by omega)

/-- The mixed charge of the ports seen by `bad`: a tagged read with its caller's policy. -/
noncomputable def kmB (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) : (MixSpec Caller).Port → ℕ
  | .hash _ => 0
  | .call (_, .inl _) => 0
  | .call (c', .inr z) => bad (.inl (.inr (.readH z (u c' z))))

/-- The mixed charge of the count of `Y`: a hash call, a tagged read of a cell of `Y`. -/
noncomputable def kmY (Y : Set HashDomain) : (MixSpec Caller).Port → ℕ
  | .hash _ => 1
  | .call (_, .inl _) => 0
  | .call (_, .inr z) => hitY Y (.inr z)

/-- **A mixed program as reads**: within the charges `kmB` (nothing) and `kmY` (`n`), it raises
the count of `Y` by at most `n lam`, at no weight `w`, and keeps the empty hardwired part. -/
theorem potB_readProgOf (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    (w : ∀ i, Matrix ((hwSpec HashOutput HashDomain Mem).In i ×
      (runtime2 HashOutput HashDomain mem0).D)
      ((hwSpec HashOutput HashDomain Mem).In i × (runtime2 HashOutput HashDomain mem0).D) ℂ →
        ℝ≥0∞)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) (hbad : ∀ i, bad i = 0 → badR i = 0)
    (hw : ∀ i σ, bad i = 0 → w i σ = 0) (hbs : ∀ p, bad (.inl (.inl p)) = 0)
    (lam : ℝ≥0∞) (Y : Set HashDomain) {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A) (n : ℕ)
    (h1 : IFreeM.IsChargeBound x (cmdCharge (kmB u bad)) 0)
    (h2 : IFreeM.IsChargeBound x (cmdCharge (kmY Y)) n) :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments w Hw0 lam (readProgOf u x) (potK Y)
      (fun _ ↦ potK Y) (n * lam) (fun _ ↦ True) :=
  potB_of_calls (R := runtime2 HashOutput HashDomain mem0) (I := .instruments) (w := w)
    (P := Hw0) (lam := lam) (potK Y) bad (kapY Y) lam (step_cntY w bad hbad hw lam Y)
    (step_hw0 bad hbad) _ n
    (isChargeBound_readProgOf u _ bad (fun _ p' ↦ (hbs p').le) (fun _ _ ↦ le_rfl) h1)
    (isChargeBound_readProgOf u _ (kapY Y) (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl) h2)

/-- A classical algorithm by tagged calls of one caller is within the mixed charges of its
queries. -/
theorem isChargeBound_kmB_toQuantumAt (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) (c : Caller)
    (hbc : ∀ z, bad (.inl (.inr (.readH z (u c z)))) = 0) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) :
    IFreeM.IsChargeBound (oa.toQuantumAt (mixImpl c B)) (cmdCharge (kmB u bad)) 0 := by
  refine isChargeBound_toQuantumAt_cost _ c B oa 0 ((queryCostAtMost_zero oa).mono_weight
    fun t ↦ ?_)
  rcases t with k | z
  · exact le_rfl
  · exact (hbc z).le

/-- One tagged call of one caller is within the mixed charge of its query. -/
theorem isChargeBound_kmB_mixImpl (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) (c : Caller)
    (hbc : ∀ z, bad (.inl (.inr (.readH z (u c z)))) = 0) (B : QReg) (i : RomOracles.Domain) :
    IFreeM.IsChargeBound (mixImpl c B i) (cmdCharge (kmB u bad)) 0 := by
  refine (isChargeBound_mixImpl_cost _ c B i).mono ?_
  rcases i with k | z
  · exact le_rfl
  · exact (hbc z).le

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **A classical algorithm by tagged calls, as reads**: with a policy no weight sees, it raises
the count of `Y` by at most `lam` per query hitting `Y`, and keeps the empty hardwired part. -/
theorem potB_toQuantumAt (c : Caller)
    (w : ∀ i, Matrix ((hwSpec HashOutput HashDomain Mem).In i ×
      (runtime2 HashOutput HashDomain mem0).D)
      ((hwSpec HashOutput HashDomain Mem).In i × (runtime2 HashOutput HashDomain mem0).D) ℂ →
        ℝ≥0∞)
    (bad : (hwSpec HashOutput HashDomain Mem).Port → ℕ) (hbad : ∀ i, bad i = 0 → badR i = 0)
    (hw : ∀ i σ, bad i = 0 → w i σ = 0) (hbs : ∀ p, bad (.inl (.inl p)) = 0)
    (hbc : ∀ z, bad (.inl (.inr (.readH z (upd e c z)))) = 0) (lam : ℝ≥0∞) (Y : Set HashDomain)
    (B : QReg) {α : Type} (oa : OracleComp romWorld.Oracles α) (n : ℕ)
    (hn : QueryCostAtMost oa (hitY Y) n) :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments w Hw0 lam
      (readProgOf (upd e) (oa.toQuantumAt (mixImpl c B))) (potK Y) (fun _ ↦ potK Y) (n * lam)
      (fun _ ↦ True) := by
  refine potB_readProgOf (upd e) w bad hbad hw hbs lam Y _ n
    (isChargeBound_kmB_toQuantumAt (upd e) bad c hbc B oa)
    (isChargeBound_toQuantumAt_cost _ c B oa n (hn.mono_weight fun t ↦ ?_))
  rcases t with k | z
  · exact le_rfl
  · exact le_rfl

end calls

/-! ### Sequencing read programs -/

section seq

/-- The read program as one substitution. -/
theorem readProgOf_eq (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    {Ω : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A) :
    readProgOf u x = IFreeM.substitute (fun s a ↦ (readSub u s a).substitute
      Quantum.Xmss.Assembly.liftReadLens.toSubstitution) x := by
  rw [readProgOf, ← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]

/-- The read program of a sequence. -/
theorem readProgOf_bind (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    {X Y : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) X A)
    (k : ∀ t, X t →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Y t) :
    readProgOf u (QuantumComp.bind x k) =
      QuantumComp.bind (readProgOf u x) fun t y ↦ readProgOf u (k t y) := by
  refine (readProgOf_eq u _).trans ?_
  simp only [readProgOf_eq]
  exact IFreeM.substitute_bind _ x k

/-- A mixed program that stops at once. -/
theorem readProgOf_pure (u : Caller → HashDomain → Mem → Option HashOutput → Mem)
    {Ω : QReg → Type} {A : QReg} (y : Ω A) :
    readProgOf u (IFreeM.pure (P := QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (MixSpec Caller)) y) = QuantumComp.pure y :=
  rfl

/-- The reduction's own query, then the rest of its algorithm. -/
theorem run_simulateQ_redImpl_inl {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (B : QReg) {α : Type}
    (i : romWorld.Oracles.Domain)
    (k : (romWorld.Oracles + R').Range (.inl i) → OracleComp (romWorld.Oracles + R') α)
    (log : QueryLog R') :
    (simulateQ (redImpl ans B) (liftM ((romWorld.Oracles + R').query (.inl i)) >>= k)).run log =
      QuantumComp₂.bind (mixImpl .red B i) fun a ↦ (simulateQ (redImpl ans B) (k a)).run log := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change QuantumComp₂.bind ((mixImpl .red B i).map fun a ↦ (a, log))
    (fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2) = _
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]

/-- The challenger's answer to a query of the reduction, then the rest of its algorithm. -/
theorem run_simulateQ_redImpl_inr {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (B : QReg) {α : Type}
    (q' : Q') (k : (romWorld.Oracles + R').Range (.inr q') → OracleComp (romWorld.Oracles + R') α)
    (log : QueryLog R') :
    (simulateQ (redImpl ans B) (liftM ((romWorld.Oracles + R').query (.inr q')) >>= k)).run log =
      QuantumComp₂.bind ((ans q').toQuantumAt (mixImpl .answer B)) fun a ↦
        (simulateQ (redImpl ans B) (k a)).run (log ++ [⟨q', a⟩]) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change QuantumComp₂.bind (((ans q').toQuantumAt (mixImpl .answer B)).map
    fun a ↦ (a, log ++ [⟨q', a⟩])) (fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2) = _
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]

end seq

section dScp

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

theorem dS_eq_trace (i : (hwSpec HashOutput HashDomain Mem).Port)
    (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × RomReg HashDomain HashOutput Mem) ℂ)
    (_ : σ.PosSemidef) : dS e i σ = ENNReal.ofReal (dSΦ e i σ).trace.re := by
  rw [dS_eq_dSΦ]

/-- **Sequencing under the trial-read weight.** -/
theorem potB_bind_dS {lam : ℝ≥0∞} {A B C : QReg} {α β : Type}
    {x : QuantumComp₂ LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) A B α}
    {k : α → QuantumComp₂ LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) B C β}
    {K : Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ : α → Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ' : (Σ u, QuantumComp₂.Leaf C β u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {c₁ c₂ : ℝ≥0∞} {Lf : α → Prop} {Lf' : (Σ u, QuantumComp₂.Leaf C β u) → Prop}
    (hx : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam x K
      (fun p ↦ Ψ p.2.2) c₁ (fun p ↦ Lf p.2.2))
    (hk : ∀ a, Lf a → PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
      (k a) (Ψ a) Ψ' c₂ Lf') :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam (x.bind k) K Ψ'
      (c₁ + c₂) Lf' :=
  PotB.bind₂ (isCP_dSΦ e) (dS_eq_trace e) hx hk

/-- **Sequencing under the trial-read weight**, the bound of the first part with any leaf
potentials (no higher-order unification). -/
theorem potB_bind_dS' {lam : ℝ≥0∞} {A B C : QReg} {α β : Type}
    {x : QuantumComp₂ LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) A B α}
    {k : α → QuantumComp₂ LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) B C β}
    {K : Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ : (Σ u, QuantumComp₂.Leaf B α u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ' : (Σ u, QuantumComp₂.Leaf C β u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {c₁ c₂ : ℝ≥0∞} {Lf : (Σ u, QuantumComp₂.Leaf B α u) → Prop}
    {Lf' : (Σ u, QuantumComp₂.Leaf C β u) → Prop}
    (hx : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam x K Ψ c₁ Lf)
    (hk : ∀ a, Lf ⟨B, rfl, a⟩ → PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e)
      Hw0 lam (k a) (Ψ ⟨B, rfl, a⟩) Ψ' c₂ Lf') :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam (x.bind k) K Ψ'
      (c₁ + c₂) Lf' :=
  PotB.bind₂' (isCP_dSΦ e) (dS_eq_trace e) hx hk

end dScp

/-! ### The answered classes and the freshness of the tweaks -/

section fresh

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The tweaks of a transcript. -/
def twOf (log : SLog Tw Msg Salt Dig) : Set Tw :=
  {t | t ∈ log.map fun x ↦ x.1.1}

omit e in
theorem twOf_nil : twOf ([] : SLog Tw Msg Salt Dig) = ∅ := by
  ext
  simp [twOf]

omit e in
theorem twOf_append (log : SLog Tw Msg Salt Dig) (q : Tw × Msg) (a : Option (Salt × Dig)) :
    twOf (log ++ [⟨q, a⟩]) = insert q.1 (twOf log) := by
  ext t
  simp only [twOf, List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton, Set.mem_ofPred_eq, Set.mem_insert_iff]
  tauto

/-- **The encoding cells at `P` in no class of a tweak of `U`.** -/
def Yset (P : Par) (U : Set Tw) : Set HashDomain :=
  {y | IsG e.hash G y ∧ ∀ t ∈ U, ¬ GCell e.hash G y P t}

/-- The cells of the class of the tweak `t` at `P`. -/
def Kset (P : Par) (t : Tw) : Set HashDomain :=
  {y | GCell e.hash G y P t}

/-- The encoding cells. -/
def Gset : Set HashDomain :=
  {y | IsG e.hash G y}

theorem Yset_empty (P : Par) : Yset e P ∅ = Gset e := by
  ext y
  simp [Yset, Gset]

theorem Yset_subset (P : Par) (U : Set Tw) : Yset e P U ⊆ Gset e :=
  fun _ h ↦ h.1

/-- **Answering a fresh tweak splits its class off the count.** -/
theorem Yset_split (hs : GSep e.hash G) (P : Par) (U : Set Tw) (t : Tw) (ht : t ∉ U) :
    Yset e P U = Yset e P (insert t U) ∪ Kset e P t := by
  ext y
  simp only [Yset, Kset, Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff,
    forall_eq_or_imp]
  constructor
  · rintro ⟨hG, hU⟩
    by_cases hy : GCell e.hash G y P t
    · exact Or.inr hy
    · exact Or.inl ⟨hG, hy, hU⟩
  · rintro (⟨hG, -, hU⟩ | hy)
    · exact ⟨hG, hU⟩
    · refine ⟨⟨P, t, hy⟩, fun t' ht' hy' ↦ ht ?_⟩
      obtain ⟨-, rfl⟩ := Tcr.gCell_unique hs hy hy'
      exact ht'

theorem Yset_disjoint (P : Par) (U : Set Tw) (t : Tw) :
    Disjoint (Yset e P (insert t U)) (Kset e P t) :=
  Set.disjoint_left.mpr fun _ hy hk ↦ hy.2 t (Set.mem_insert _ _) hk

omit e in
/-- One step of the freshness of a classical algorithm of the reduction. -/
def freshStep : (t : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) →
    ((romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Range t →
      SLog Tw Msg Salt Dig → Prop) → SLog Tw Msg Salt Dig → Prop
  | .inl _, k, log => ∀ y, k y log
  | .inr q, k, log => q.1 ∉ twOf log ∧ ∀ y, k y (log ++ [⟨q, y⟩])

omit e in
/-- **Fresh tweaks**: along every path of `oa` from the transcript `log`, every challenger's query
is at a tweak not in the transcript, and `Post` holds at the end. -/
def FreshWP {α : Type} (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (log : SLog Tw Msg Salt Dig) (Post : α → SLog Tw Msg Salt Dig → Prop) : Prop :=
  PFunctor.FreeM.rec (P := (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).toPFunctor)
    (motive := fun _ ↦ SLog Tw Msg Salt Dig → Prop) (fun a log ↦ Post a log)
    (fun t _ ih log ↦ freshStep t ih log) oa log

omit e in
theorem freshWP_pure {α : Type} (a : α) (log : SLog Tw Msg Salt Dig)
    (Post : α → SLog Tw Msg Salt Dig → Prop) :
    FreshWP (pure a : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α) log
      Post ↔ Post a log :=
  Iff.rfl

omit e in
theorem freshWP_query_bind {α : Type}
    (t : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain)
    (k : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Range t →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α)
    (log : SLog Tw Msg Salt Dig) (Post : α → SLog Tw Msg Salt Dig → Prop) :
    FreshWP (liftM ((romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).query t) >>= k) log
      Post ↔ freshStep t (fun y log' ↦ FreshWP (k y) log' Post) log :=
  Iff.rfl

omit e in
open scoped Classical in
/-- **The reduction's reads of encoding cells**, as a query cost. -/
noncomputable def costR (e : SaltEnc Par Tw Msg Salt Dig) :
    (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain → ℕ
  | .inl (.inr z) => if IsG e.hash G z then 1 else 0
  | _ => 0

omit e in
variable (Tw Msg Salt Dig) in
/-- **The challenger's answers**, as a query cost. -/
def costA : (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain → ℕ
  | .inr _ => 1
  | .inl _ => 0

omit e in
/-- **The contract of the per-answer bound**: from every positive semidefinite input with no
hardwired cell, the trial-read weight of the read program of the answer to `q` at `P` is at most
the diagonal weight `ℓ P q`. -/
def AnsBound [SampleableType Par] [SampleableType Salt] (e : SaltEnc Par Tw Msg Salt Dig)
    (ℓ : Par → Tw × Msg → HwReg HashOutput HashDomain Mem → ℝ) : Prop :=
  ∀ (P : Par) (q : Tw × Msg) (B : QReg)
    (ρ : Matrix (B × RomReg HashDomain HashOutput Mem) (B × RomReg HashDomain HashOutput Mem) ℂ),
    ρ.PosSemidef → QuerySupportedOn (fun x : B × RomReg HashDomain HashOutput Mem ↦ x.2) Hw0 ρ →
    (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B))) ρ ≤
      ENNReal.ofReal (∑ s, ℓ P q s.2 * (ρ s s).re)

/-- **A grind reads only cells of its class.** -/
theorem queryCost_grind (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (Y : Set HashDomain)
    (hY : ∀ y ∈ Y, ¬ GCell e.hash G y P t) :
    ∀ n c, QueryCostAtMost (e.grind romWorld P t M r0 c n) (hitY Y) 0 := by
  intro n
  induction n with
  | zero => exact fun _ ↦ trivial
  | succ n ih =>
    intro c
    have hh : QueryCostAtMost (e.hash.eval romWorld () P t (M, e.shift r0 c)) (hitY Y) 0 := by
      unfold TwColl.eval
      refine isWeightBound_map _ ?_
      change QueryCostAtMost (hashQ (e.hash.layout () P t (M, e.shift r0 c))) (hitY Y) 0
      unfold hashQ
      split
      · next x hx =>
        refine (isWeightBound_query (hitY Y) (.inr x)).mono ?_
        have hxY : x ∉ Y := fun hx' ↦ hY x hx' ⟨(), (M, e.shift r0 c), trivial, hx⟩
        simp only [hitY]
        split_ifs with h
        · exact absurd h hxY
        · exact le_rfl
      · exact trivial
    show QueryCostAtMost (e.hash.eval romWorld () P t (M, e.shift r0 c) >>= fun d ↦
      if e.isCode d then pure (some (e.shift r0 c, d)) else e.grind romWorld P t M r0 (c + 1) n)
      (hitY Y) 0
    refine hh.bind (b := 0) fun d ↦ ?_
    split
    · exact trivial
    · exact ih (c + 1)

/-- **An answer reads only cells of the class of its tweak.** -/
theorem queryCost_answer [SampleableType Par] [SampleableType Salt] (P : Par) (q : Tw × Msg)
    (Y : Set HashDomain) (hY : ∀ y ∈ Y, ¬ GCell e.hash G y P q.1) :
    QueryCostAtMost ((encTcrSalt romWorld e).answer P q) (hitY Y) 0 :=
  (isWeightBound_liftM_probComp (hitY Y) (fun _ ↦ rfl) ($ᵗ Salt)).bind fun r0 ↦
    queryCost_grind e P q.1 q.2 r0 Y hY e.limit 0

end fresh

/-! ### The answer blocks -/

section blocks

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **An answer to a fresh tweak pays its weight by its class**: if the per-answer weight is at
most `lam` times the count of its class plus `c₀`, the class leaves the count, which pays. -/
theorem potB_answer [SampleableType Par] [SampleableType Salt] (hs : GSep e.hash G)
    (ℓ : Par → Tw × Msg → HwReg HashOutput HashDomain Mem → ℝ) (hA : AnsBound e ℓ)
    (lamR c₀R : ℝ) (hlam : 0 ≤ lamR) (hc₀ : 0 ≤ c₀R)
    (hℓ : ∀ P q s, ℓ P q s ≤ lamR * cntY (Kset e P q.1) s + c₀R)
    (P : Par) (q : Tw × Msg) (B : QReg) (U : Set Tw) (hU : q.1 ∉ U) :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 (ENNReal.ofReal lamR)
      (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
        (mixImpl .answer B)))
      (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert q.1 U))) (ENNReal.ofReal c₀R)
      (fun _ ↦ True) := by
  intro ρ hρ hs0
  obtain ⟨hk1, hk2, -⟩ := potB_toQuantumAt e .answer (fun _ _ ↦ 0) badR (fun _ h ↦ h)
    (fun _ _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (ENNReal.ofReal lamR)
    (Yset e P (insert q.1 U)) B _ 0
    (queryCost_answer e P q _ fun y hy hg ↦ hy.2 q.1 (Set.mem_insert _ _) hg) ρ hρ hs0
  refine ⟨?_, hk2, fun _ h ↦ absurd trivial h⟩
  have hTW := (hA P q B ρ hρ hs0).trans (ofReal_sum_le_potential (ℓ P q)
    (cntY (Kset e P q.1)) (cntY_nonneg _) lamR c₀R hlam hc₀ (hℓ P q) hρ)
  have hf : (fun s : HwReg HashOutput HashDomain Mem ↦ √(cntY (Yset e P U) s)) =
      fun s ↦ √(cntY (Yset e P (insert q.1 U)) s + cntY (Kset e P q.1) s) :=
    funext fun s ↦ by
      rw [Yset_split e hs P U q.1 hU, cntY_union _ _ (Yset_disjoint e P U q.1)]
  have hsplit : potential (potK (Yset e P U)) ρ = potential (potK (Yset e P (insert q.1 U))) ρ +
      potential (diagPot fun s : HwReg HashOutput HashDomain Mem ↦
        √(cntY (Kset e P q.1) s)) ρ := by
    simp only [potK]
    rw [hf]
    exact potential_diagPot_add (cntY_nonneg _) (cntY_nonneg _) hρ
  have hk1' := hk1
  simp only [Nat.cast_zero, zero_mul, add_zero] at hk1'
  have hpot := le_add_self.trans hk1'
  calc _ ≤ (ENNReal.ofReal lamR * potential (diagPot fun s : HwReg HashOutput HashDomain Mem ↦
          √(cntY (Kset e P q.1) s)) ρ + ENNReal.ofReal c₀R * ENNReal.ofReal ρ.trace.re) +
        ENNReal.ofReal lamR * potential (potK (Yset e P (insert q.1 U))) ρ :=
        add_le_add hTW hpot
    _ = _ := by
        rw [hsplit]
        ring

end blocks

/-! ### The reduction's algorithms -/

section red

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

theorem natCast_mul_add_le (a b : ℕ) (h : b ≤ a) (x : ℝ≥0∞) :
    (b : ℝ≥0∞) * x + ((a - b : ℕ) : ℝ≥0∞) * x = a * x := by
  rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' h]

/-- **The reduction's algorithm by reads**, the challenger answering fresh tweaks: with `n`
reads of encoding cells and `m` answers, the weight is paid by the count of the encoding cells
of the unanswered classes, raised by `lam` per read, plus `c₀` per answer. -/
theorem potB_redImpl [SampleableType Par] [SampleableType Salt] (P : Par) (lam c₀ : ℝ≥0∞)
    (B : QReg)
    (hblk : ∀ (q : Tw × Msg) (U : Set Tw), q.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert q.1 U))) c₀ (fun _ ↦ True))
    {α : Type} (oa : OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) α) :
    ∀ (log : SLog Tw Msg Salt Dig) (n m : ℕ) (Post : α → SLog Tw Msg Salt Dig → Prop),
      QueryCostAtMost oa (costR e) n → QueryCostAtMost oa (costA Tw Msg Salt Dig) m →
      FreshWP oa log Post →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P) B) oa).run
          log))
        (potK (Yset e P (twOf log))) (fun p ↦ potK (Yset e P (twOf p.2.2.2)))
        (n * lam + m * c₀) (fun p ↦ Post p.2.2.1 p.2.2.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro log n m Post _ _ hf
    rw [simulateQ_pure, StateT.run_pure]
    have h := potB_pure₂ (R := runtime2 HashOutput HashDomain mem0)
      (I := LocalSig.Interp.instruments) (w := dS e) (P := Hw0) (lam := lam)
      (L := LocalSig.instruments.{0}) (spec := hwSpec HashOutput HashDomain Mem) (A := B)
      (a, log) (potK (Yset e P (twOf log))) (fun v ↦ potK (Yset e P (twOf v.2))) rfl
      (fun v ↦ Post v.1 v.2) hf
    have h' := h.mono (c' := n * lam + m * c₀) zero_le (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
    exact h'
  | query_bind t k ih =>
    intro log n m Post hn hm hf
    rw [isWeightBound_query_bind_iff] at hn hm
    rw [freshWP_query_bind] at hf
    rcases t with i | q'
    · have hf' : ∀ y, FreshWP (k y) log Post := hf
      rw [run_simulateQ_redImpl_inl, readProgOf_bind₂]
      have hY : hitY (Yset e P (twOf log)) i ≤ costR e (.inl i) := by
        rcases i with c | z
        · exact le_rfl
        · simp only [hitY, costR]
          split_ifs with h1 h2 <;> first | omega | exact absurd h1.1 h2
      have hx := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (mixImpl .red B i) (costR e (.inl i))
        (isChargeBound_kmB_mixImpl (upd e) badS .red (fun z ↦ by simp [badS, upd]) B i)
        ((isChargeBound_mixImpl_cost (kmY _) .red B i).mono (by
          rcases i with c | z
          · exact Nat.zero_le _
          · exact hY))
      refine (potB_bind_dS e (Ψ := fun _ ↦ potK (Yset e P (twOf log)))
        (Lf := fun _ ↦ True) hx fun a _ ↦ ih a log _ _ Post (hn.2 a) (hm.2 a) (hf' a)).mono
        (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      have hc : costA Tw Msg Salt Dig (.inl i) = 0 := rfl
      rw [hc, Nat.sub_zero, ← add_assoc, natCast_mul_add_le _ _ hn.1]
    · obtain ⟨hq, hf'⟩ := (hf : q'.1 ∉ twOf log ∧ ∀ y, FreshWP (k y) (log ++ [⟨q', y⟩]) Post)
      rw [run_simulateQ_redImpl_inr, readProgOf_bind₂]
      have hm1 : 1 ≤ m := hm.1
      refine (potB_bind_dS e
        (Ψ := fun _ ↦ potK (Yset e P (insert q'.1 (twOf log)))) (Lf := fun _ ↦ True)
        (c₂ := (n - costR e (.inr q') : ℕ) * lam +
          (m - costA Tw Msg Salt Dig (.inr q') : ℕ) * c₀)
        (hblk q' (twOf log) hq) fun a _ ↦ ?_).mono ?_ (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · have h := ih a (log ++ [⟨q', a⟩]) _ _ Post (hn.2 a) (hm.2 a) (hf' a)
        rwa [twOf_append] at h
      · have hc : costR e (.inr q' :
            (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))).Domain) = 0 := rfl
        have hc' : costA Tw Msg Salt Dig (.inr q') = 1 := rfl
        rw [hc, hc', Nat.sub_zero]
        have h1 : (m : ℝ≥0∞) = ((m - 1 : ℕ) : ℝ≥0∞) + 1 := by
          exact_mod_cast (Nat.sub_add_cancel hm1).symm
        rw [h1]
        exact le_of_eq (by ring)

end red

/-! ### The adversary's run against the reduction's handler -/

section adv

/-- One command, returning its response. -/
noncomputable def cmd1 {A : QReg}
    (a : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).A A) :
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller))
      (fun t ↦ {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).B A a //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).src A a b = t}) A :=
  IFreeM.liftBind a fun b ↦ IFreeM.pure ⟨b, rfl⟩

theorem liftBind_eq_bind_cmd1 {X : QReg → Type} {A : QReg}
    (a : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).A A)
    (next : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).B A a) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) X
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).src A a b)) :
    IFreeM.liftBind a next = QuantumComp.bind (cmd1 a) fun _ ans ↦ ans.2 ▸ next ans.1 :=
  rfl

theorem isChargeBound_cmd1 {A : QReg}
    (a : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)).A A)
    (κ : (MixSpec Caller).Port → ℕ) {n : ℕ} (h : cmdCharge κ A a ≤ n) :
    IFreeM.IsChargeBound (cmd1 a) (cmdCharge κ) n :=
  (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨h, fun _ ↦ trivial⟩

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **Sequencing under the trial-read weight**, any leaves. -/
theorem potB_bindG_dS {lam : ℝ≥0∞} {X Y : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) X A}
    {k : ∀ u, X u → QuantumComp LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Mem) Y u}
    {K : Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ : (Σ u, X u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {Ψ' : (Σ u, Y u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ}
    {c₁ c₂ : ℝ≥0∞} {Lf : (Σ u, X u) → Prop} {Lf' : (Σ u, Y u) → Prop}
    (hx : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam x K Ψ c₁ Lf)
    (hk : ∀ p, Lf p → PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
      (k p.1 p.2) (Ψ p) Ψ' c₂ Lf') :
    PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
      (QuantumComp.bind x k) K Ψ' (c₁ + c₂) Lf' :=
  PotB.bind (isCP_dSΦ e) (dS_eq_trace e) hx hk

theorem natCast_eq_sub_one_add (k : ℕ) (h : 1 ≤ k) :
    (k : ℝ≥0∞) = ((k - 1 : ℕ) : ℝ≥0∞) + 1 := by
  exact_mod_cast (Nat.sub_add_cancel h).symm

section unfold

variable {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type} {X Y : QReg → Type}
  (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u) {A : QReg}

omit e in
theorem mixRun_prim (o : LocalSig.instruments.{0}.Op A)
    (next : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (advSpec romWorld.spec R)).B A (.prim o)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)).src A
          (.prim o) b)) (s : St) :
    mixRun Tr leaf (IFreeM.liftBind (.prim o) next) s =
      QuantumComp.bind (cmd1 (.prim o)) fun _ ans ↦ ans.2 ▸ mixRun Tr leaf (next ans.1) s :=
  rfl

omit e in
theorem mixRun_hash (p : romWorld.spec.Port) (E : QReg)
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.hash p) × E)
    (next : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (advSpec romWorld.spec R)).B A (.query (.hash p) E ℓ)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)).src A
          (.query (.hash p) E ℓ) b)) (s : St) :
    mixRun Tr leaf (IFreeM.liftBind (.query (.hash p) E ℓ) next) s =
      QuantumComp.bind (cmd1 (.query (.hash p) E ℓ)) fun _ ans ↦
        ans.2 ▸ mixRun Tr leaf (next ans.1) s :=
  rfl

omit e in
theorem mixRun_call (qq : Q) (E : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call qq) × E)
    (next : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (advSpec romWorld.spec R)).B A (.query (.call qq) E ℓ)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)).src A
          (.query (.call qq) E ℓ) b)) (s : St) :
    mixRun Tr leaf (IFreeM.liftBind (.query (.call qq) E ℓ) next) s =
      QuantumComp.bind (Tr s qq E ℓ) fun _ l ↦ l.1 ▸ mixRun Tr leaf (next ⟨l.2.1⟩) l.2.2 :=
  rfl

end unfold

omit e in
theorem mixTrees_apply {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St : Type}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (σ : HHandler romWorld R R' St) (st : St) (log : QueryLog R') (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) :
    mixTrees ans σ (st, log) q E ℓ =
      (QComp.act (B := QReg.of ((advSpec romWorld.spec R).Out (.call q) × E))
        (SubInstrument.relabel ℓ)).bind fun _ ↦
          ((simulateQ (redImpl ans _) (σ st q)).run log).map fun r ↦ (r.1.1, (r.1.2, r.2)) :=
  rfl

/-- **The adversary's run against the reduction's handler, by reads**: each hash call of the
adversary raises the count by `lam`, each of its classical calls runs the handler, within `nσ`
reads of encoding cells and `mσ` fresh answers, under an invariant `J` of the handler's state and
the transcript. -/
theorem potB_mixRun [SampleableType Par] [SampleableType Salt] {Q : Type}
    {R : OracleSpec.{0, 0} Q} {St : Type} (P : Par) (lam c₀ : ℝ≥0∞)
    (hblk : ∀ (B : QReg) (q : Tw × Msg) (U : Set Tw), q.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert q.1 U))) c₀ (fun _ ↦ True))
    (σ : HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (J : St → SLog Tw Msg Salt Dig → Prop) (nσ mσ : ℕ)
    (hσn : ∀ st qq, QueryCostAtMost (σ st qq) (costR e) nσ)
    (hσm : ∀ st qq, QueryCostAtMost (σ st qq) (costA Tw Msg Salt Dig) mσ)
    (hσf : ∀ st qq log, J st log → FreshWP (σ st qq) log fun r log' ↦ J r.2 log')
    {X Y : QReg → Type} (leaf : ∀ u, X u → St × SLog Tw Msg Salt Dig → Y u)
    (Ψ : (Σ u, Y u) →
      Matrix (HwReg HashOutput HashDomain Mem) (HwReg HashOutput HashDomain Mem) ℂ)
    (Lf : (Σ u, Y u) → Prop)
    (hleaf : ∀ u y st log, J st log →
      Ψ ⟨u, leaf u y (st, log)⟩ = potK (Yset e P (twOf log)) ∧ Lf ⟨u, leaf u y (st, log)⟩)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A) :
    ∀ (st : St) (log : SLog Tw Msg Salt Dig) (q k : ℕ), J st log →
      IFreeM.IsChargeBound x (cmdCharge hashCharge) q →
      IFreeM.IsChargeBound x (cmdCharge callCharge) k →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (mixRun (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf x
          (st, log)))
        (potK (Yset e P (twOf log))) Ψ (q * lam + k * (nσ * lam + mσ * c₀)) Lf := by
  have hS : ∀ {Ω : QReg → Type} {B : QReg}
      (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω B)
      (n : ℕ) (U : Set HashDomain),
      IFreeM.IsChargeBound y (cmdCharge (kmB (upd e) badS)) 0 →
      IFreeM.IsChargeBound y (cmdCharge (kmY U)) n →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam (readProgOf (upd e) y)
        (potK U) (fun _ ↦ potK U) (n * lam) (fun _ ↦ True) := fun y n U h1 h2 ↦
    potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
      (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam U y n h1 h2
  induction x using IFreeM.inductionOn with
  | pure _ y =>
    intro st log q k hJ _ _
    obtain ⟨hΨ, hL⟩ := hleaf _ y st log hJ
    have h := potB_pure (R := runtime2 HashOutput HashDomain mem0)
      (I := LocalSig.Interp.instruments) (w := dS e) (P := Hw0) (lam := lam)
      (L := LocalSig.instruments.{0}) (spec := hwSpec HashOutput HashDomain Mem)
      (leaf _ y (st, log)) _ Ψ hΨ Lf hL
    have h' := h.mono (c' := q * lam + k * (nσ * lam + mσ * c₀)) zero_le
      (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
    exact h'
  | liftBind A cmd next ih =>
    intro st log q k hJ hq hk
    replace hq := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hq
    replace hk := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hk
    rcases cmd with o | ⟨p | qq, E, ℓ⟩
    · refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_prim (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf o next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      have h0 := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (cmd1 (.prim o)) 0 (isChargeBound_cmd1 _ _ le_rfl) (isChargeBound_cmd1 _ _ le_rfl)
      refine (potB_bindG_dS e (c₂ := q * lam + k * (nσ * lam + mσ * c₀)) h0
        fun p _ ↦ ?_).mono (le_of_eq (by simp)) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      obtain ⟨t, b, rfl⟩ := p
      exact ih b st log q k hJ (hq.2 b) (hk.2 b)
    · refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_hash (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf p E ℓ next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      have hq1 : 1 ≤ q := hq.1
      have h0 := potB_readProgOf (upd e) (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) lam (Yset e P (twOf log))
        (cmd1 (.query (.hash p) E ℓ)) 1 (isChargeBound_cmd1 _ _ (Nat.zero_le _))
        (isChargeBound_cmd1 _ _ le_rfl)
      refine (potB_bindG_dS e (c₂ := (q - 1 : ℕ) * lam + k * (nσ * lam + mσ * c₀)) h0
        fun p _ ↦ ?_).mono (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · obtain ⟨t, b, rfl⟩ := p
        exact ih b st log (q - 1) k hJ (hq.2 b) (hk.2 b)
      · rw [natCast_eq_sub_one_add q hq1]
        ring
    · have hk1 : 1 ≤ k := hk.1
      have hT : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
          (readProgOf (upd e) (mixTrees ((encTcrSalt romWorld e).answer P) σ (st, log) qq E ℓ))
          (potK (Yset e P (twOf log))) (fun p ↦ potK (Yset e P (twOf p.2.2.2.2)))
          (((0 : ℕ) : ℝ≥0∞) * lam + ((nσ * lam + mσ * c₀) + 0))
          (fun p ↦ J p.2.2.2.1 p.2.2.2.2) := by
        rw [mixTrees_apply, readProgOf_bind₂]
        refine potB_bind_dS e (Ψ := fun _ ↦ potK (Yset e P (twOf log))) (Lf := fun _ ↦ True)
          (hS _ 0 _ (isChargeBound_act _ _ 0) (isChargeBound_act _ _ 0)) fun _ _ ↦ ?_
        rw [QuantumComp₂.map_eq_bind_pure, readProgOf_bind₂]
        have hr := potB_redImpl e P lam c₀
          (QReg.of ((advSpec romWorld.spec R).Out (.call qq) × E)) (hblk _) (σ st qq) log nσ mσ
          (fun r log' ↦ J r.2 log') (hσn st qq) (hσm st qq) (hσf st qq log hJ)
        generalize hX : readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
          (QReg.of ((advSpec romWorld.spec R).Out (.call qq) × E))) (σ st qq)).run log) = X at hr ⊢
        refine potB_bind_dS' e hr fun v hv ↦ ?_
        refine PotB.of_eq (readProgOf_pure (upd e) (Ω := QuantumComp₂.Leaf _ _)
          ⟨rfl, (v.1.1, (v.1.2, v.2))⟩) ?_
        exact potB_pure _ _ _ rfl _ hv
      refine PotB.of_eq ((congrArg (readProgOf (upd e))
        (mixRun_call (mixTrees ((encTcrSalt romWorld e).answer P) σ) leaf qq E ℓ next
          (st, log))).trans (readProgOf_bind _ _ _)) ?_
      refine (potB_bindG_dS e (c₂ := q * lam + (k - 1 : ℕ) * (nσ * lam + mσ * c₀)) hT
        fun p hp ↦ ?_).mono (le_of_eq ?_) (fun _ _ _ ↦ le_rfl) fun _ h ↦ h
      · obtain ⟨u, rfl, v⟩ := p
        exact ih ⟨v.1⟩ v.2.1 v.2.2 q (k - 1) hp (hq.2 _) (hk.2 _)
      · rw [natCast_eq_sub_one_add k hk1]
        ring

end adv

/-! ### The game -/

section game

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- **The total weight of the challenger's trial reads in the EncTCR$ game.** Let the weight of
each answer block be at most `ℓ` (`AnsBound`), with `ℓ P q ≤ lam · (recorded cells of the class
of q.1 at P) + c₀`. Let the adversary make at most `q` hash calls and `kA` classical calls; the
reduction's setup, handler and output make at most `n₁`, `nσ`, `n₂` reads of encoding cells and
`m₁`, `mσ`, `m₂` challenger queries, each at a fresh tweak (`FreshWP`, with an invariant `J` of
the handler's state and the transcript). Then
`TW ≤ lam (n₁ + q + kA nσ + n₂) + c₀ (m₁ + kA mσ + m₂)`. -/
theorem totalWeight_saltProg_le [SampleableType Par] [SampleableType Salt]
    (hs : GSep e.hash G) (ℓ : Par → Tw × Msg → HwReg HashOutput HashDomain Mem → ℝ)
    (hA : AnsBound e ℓ) (lamR c₀R : ℝ) (hlam : 0 ≤ lamR) (hc₀ : 0 ≤ c₀R)
    (hℓ : ∀ P q s, ℓ P q s ≤ lamR * cntY (Kset e P q.1) s + c₀R)
    {Q : Type} {R : OracleSpec.{0, 0} Q} {St S0 Fo : Type}
    (pre : Par → OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) S0)
    (adv : Par → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Par → S0 → St) (σ : Par → HHandler romWorld R (Tw × Msg →ₒ Option (Salt × Dig)) St)
    (post : Par → S0 → Fo → St →
      OracleComp (romWorld.Oracles + (Tw × Msg →ₒ Option (Salt × Dig))) (Tw × Msg × Salt))
    {q kA : ℕ} (hadv : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge hashCharge) q)
    (hadvC : ∀ p a, IFreeM.IsChargeBound (adv p a) (cmdCharge callCharge) kA)
    {n₁ m₁ nσ mσ n₂ m₂ : ℕ}
    (hpreN : ∀ P, QueryCostAtMost (pre P) (costR e) n₁)
    (hpreM : ∀ P, QueryCostAtMost (pre P) (costA Tw Msg Salt Dig) m₁)
    (hσN : ∀ P st qq, QueryCostAtMost (σ P st qq) (costR e) nσ)
    (hσM : ∀ P st qq, QueryCostAtMost (σ P st qq) (costA Tw Msg Salt Dig) mσ)
    (hpostN : ∀ P a f st, QueryCostAtMost (post P a f st) (costR e) n₂)
    (hpostM : ∀ P a f st, QueryCostAtMost (post P a f st) (costA Tw Msg Salt Dig) m₂)
    (J : Par → St → SLog Tw Msg Salt Dig → Prop)
    (hpreF : ∀ P, FreshWP (pre P) [] fun a log ↦ J P (st0 P a) log)
    (hσF : ∀ P st qq log, J P st log → FreshWP (σ P st qq) log fun r log' ↦ J P r.2 log')
    (hpostF : ∀ P a f st log, J P st log → FreshWP (post P a f st) log fun _ _ ↦ True) :
    (runtime2 HashOutput HashDomain mem0).totalWeight .instruments (dS e)
        (saltProg e pre adv st0 σ post) (rhoMem0 mem0) ≤
      ENNReal.ofReal lamR * (n₁ + q + kA * nσ + n₂ : ℕ) +
        ENNReal.ofReal c₀R * (m₁ + kA * mσ + m₂ : ℕ) := by
  set lam := ENNReal.ofReal lamR
  set c₀ := ENNReal.ofReal c₀R
  have hblk : ∀ (P : Par) (B : QReg) (qq : Tw × Msg) (U : Set Tw), qq.1 ∉ U →
      PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P qq).toQuantumAt
          (mixImpl .answer B)))
        (potK (Yset e P U)) (fun _ ↦ potK (Yset e P (insert qq.1 U))) c₀ (fun _ ↦ True) :=
    fun P B qq U hU ↦ potB_answer e hs ℓ hA lamR c₀R hlam hc₀ hℓ P qq B U hU
  have hzero : ∀ (Y : Set HashDomain) (τ : Matrix (HwReg HashOutput HashDomain Mem)
      (HwReg HashOutput HashDomain Mem) ℂ), True := fun _ _ ↦ trivial
  clear hzero
  have hle0 : ∀ (Y : Set HashDomain) {B : QReg}
      (τ : Matrix (B × HwReg HashOutput HashDomain Mem) (B × HwReg HashOutput HashDomain Mem) ℂ),
      τ.PosSemidef → potential (potK ∅) τ ≤ potential (potK Y) τ := fun Y _ τ hτ ↦
    potential_diagPot_mono (cntY_nonneg _) (fun s ↦ cntY_mono (Set.empty_subset Y) s) hτ
  have hgame : PotB (runtime2 HashOutput HashDomain mem0) .instruments (dS e) Hw0 lam
      (saltProg e pre adv st0 σ post) (potK (Gset e)) (fun _ ↦ potK ∅)
      (((0 : ℕ) : ℝ≥0∞) * lam + ((n₁ * lam + m₁ * c₀ + (q * lam + kA * (nσ * lam + mσ * c₀) +
        (n₂ * lam + m₂ * c₀))) + ((0 : ℕ) : ℝ≥0∞) * lam)) (fun _ ↦ True) := by
    show PotB _ _ _ _ _ (readProgOf (upd e) (mixGame (encTcrSalt romWorld e) pre adv st0 σ post))
      _ _ _ _
    unfold mixGame
    rw [readProgOf_bind₂]
    refine potB_bind_dS e (Ψ := fun _ ↦ potK (Gset e)) (Lf := fun _ ↦ True)
      (potB_toQuantumAt e .setup (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) (fun z ↦ by simp [badS, upd]) lam
        (Gset e) _ (encTcrSalt romWorld e).setup 0
        (by exact isWeightBound_liftM_probComp (hitY (Gset e)) (fun _ ↦ rfl) ($ᵗ Par)))
        fun P _ ↦ ?_
    rw [readProgOf_bind₂]
    refine potB_bind_dS e (Ψ := fun _ ↦ potK ∅) (Lf := fun _ ↦ True) ?_ fun r _ ↦ ?_
    · rw [← Yset_empty e P]
      unfold mixNormal
      rw [readProgOf_bind₂]
      have hpre := potB_redImpl e P lam c₀ (QReg.of Unit) (hblk P _)
        (pre ((encTcrSalt romWorld e).pub P)) [] n₁ m₁
        (fun a log ↦ J P (st0 ((encTcrSalt romWorld e).pub P) a) log) (hpreN P) (hpreM P)
        (hpreF P)
      rw [twOf_nil] at hpre
      generalize readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
        (QReg.of Unit)) (pre ((encTcrSalt romWorld e).pub P))).run []) = X at hpre ⊢
      refine potB_bind_dS' e hpre fun p hp ↦ ?_
      rw [readProgOf_bind₂]
      unfold mixRunL
      refine potB_bind_dS' e (potB_mixRun e P lam c₀ (hblk P) (σ ((encTcrSalt romWorld e).pub P))
        (J P) nσ mσ (hσN P) (hσM P) (hσF P)
        (Y := QuantumComp₂.Leaf (QReg.of Unit)
          ((Fo × St) × QueryLog (Tw × Msg →ₒ Option (Salt × Dig))))
        (fun _ l q ↦ ⟨l.1, ((l.2, q.1), q.2)⟩)
        (fun p ↦ potK (Yset e P (twOf p.2.2.2))) (fun p ↦ J P p.2.2.1.2 p.2.2.2)
        (fun _ _ _ _ hJ ↦ ⟨rfl, hJ⟩) (adv ((encTcrSalt romWorld e).pub P) p.1)
        (st0 ((encTcrSalt romWorld e).pub P) p.1) p.2 q kA hp (hadv P p.1) (hadvC P p.1))
        fun r hr ↦ ?_
      have hpost := potB_redImpl e P lam c₀ (QReg.of Unit) (hblk P _)
        (post ((encTcrSalt romWorld e).pub P) p.1 r.1.1 r.1.2) r.2 n₂ m₂
        (fun _ _ ↦ True) (hpostN P p.1 r.1.1 r.1.2) (hpostM P p.1 r.1.1 r.1.2)
        (hpostF P p.1 r.1.1 r.1.2 r.2 hr)
      generalize readProgOf (upd e) ((simulateQ (redImpl ((encTcrSalt romWorld e).answer P)
        (QReg.of Unit)) (post ((encTcrSalt romWorld e).pub P) p.1 r.1.1 r.1.2)).run r.2) = Z
        at hpost ⊢
      exact hpost.mono le_rfl (fun _ τ hτ ↦ hle0 _ τ hτ) fun _ _ ↦ trivial
    · refine potB_toQuantumAt e .judge (dS e) badS (fun _ h ↦ badR_eq_zero_of_badS h)
        (fun _ σ h ↦ dS_eq_zero_of_badS e h σ) (fun _ ↦ rfl) (fun z ↦ by simp [badS, upd]) lam
        ∅ _ ((encTcrSalt romWorld e).judge P r.2 r.1) 0
        ((queryCostAtMost_zero _).mono_weight fun t ↦ ?_)
      rcases t with k | z
      · exact le_rfl
      · simp only [hitY]
        split_ifs with h
        · exact h.elim
        · exact le_rfl
  have hρ : (rhoMem0 mem0 : Matrix (QReg.of Unit × RomReg HashDomain HashOutput Mem)
      (QReg.of Unit × RomReg HashDomain HashOutput Mem) ℂ).PosSemidef :=
    ((SubState.basis ()).prod (runtime2 HashOutput HashDomain mem0).init).posSemidef
  have htr : ENNReal.ofReal (rhoMem0 mem0 :
      Matrix (QReg.of Unit × RomReg HashDomain HashOutput Mem)
      (QReg.of Unit × RomReg HashDomain HashOutput Mem) ℂ).trace.re ≤ 1 := by
    change ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtime2 HashOutput HashDomain mem0).init.matrix).trace.re ≤ 1
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr
      ((SubState.basis ()).prod (runtime2 HashOutput HashDomain mem0).init).trace_re_le_one
  have h := (hgame _ hρ (querySupportedOn_init_hw mem0 ())).1
  rw [potential_cntY_init mem0 (Gset e) (), mul_zero, zero_add] at h
  refine le_self_add.trans (h.trans ((mul_le_mul_right htr _).trans (le_of_eq ?_)))
  rw [mul_one]
  push_cast
  ring

end game

end Quantum.StdModel.Qrom.EncSalt

end
