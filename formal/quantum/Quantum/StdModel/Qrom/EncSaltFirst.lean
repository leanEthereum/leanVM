module

public import Quantum.StdModel.Qrom.EncSalt
public import Quantum.Xmss.Assembly.EncRefined

@[expose] public section

/-!
# EncTCR$ in the QROM: the cost of an answer

The trial reads of an answer of EncTCR$ (`Props.encTcrSalt`) add their linearized cost (`dS`)
to the event weight. Summed over an answer, against the state at the answer's start, this cost is
at most a diagonal weight `ansCost`, averaged over the uniform base `R_0` of the salts.

* **A cell read with outcome-dependent weights** (`re_trace_gramW_le_dom`,
  `sum_ofReal_readH_le`): if every outcome's weight after the read, at every content of the read
  cell, is at most `H` of the state before, the weights after the read are at most the weight of
  `H`. No decompressed-`⊥` hypothesis is needed.
* **Step bounds of a program** (`StepQ`, `Step₂`): the total weight of a program plus the
  potentials of its branches at their leaves is at most a potential of the start; the rules
  follow the program (local operations, calls, sequencing), and the challenger's coins average
  the leaves' weights (`step₂_call_coin`, `step₂_sampler`).
* **The cost of a trial read** (`readLin_uSel_le`): `2 + 2/N` on a recorded or hardwired cell;
  on an empty cell `(2F + 2)/N`, plus `2F/N` per other recorded cell of its class if the class
  has no record (`badR_record_new`: a new record changes the event only through the
  truncations of the class's other cells and of the judge's read).
* **A grind** (`step₂_grind`): the trials' weights `fTrial` add up, a trial's read leaving the
  later trials' weights unchanged when its outcome is not a codeword.
* **The cost of an answer** (`totalWeight_answer_le`): averaged over the base, the trials of
  an answer to `(t, M)` at `P` weigh at most
  `limit · ((2 + 2/N) · #{r | cell (M, r) recorded} / |Salt| + [class without record] ·
  2F/N · (#{recorded cells of the class} + limit) + (2F + 2)/N)` (`ansCost`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum.StdModel.Qrom.EncSalt

open Quantum QuantumRuntime Quantum.Sponge

/-! ## A cell read with outcome-dependent weights -/

section gramDom

open Quantum.Xmss.Assembly (gramW_apply gramW_off sum_cr_mul_cr)

variable {n Y R M0 : Type} [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y]
  [Fintype R] [DecidableEq R] [Fintype M0] [DecidableEq M0]
  {e : n ≃ Option Y × R} {act : R → Prop} [DecidablePred act] {μ : R → M0}
  {τ : Option Y → R → R} {K : Option Y × M0 → Matrix n n ℂ} {idx : n → Option Y × M0}
  {φ : n → n}

/-- **A cell read with outcome-dependent weights, dominated**: if on every active rest every
outcome's weight after the read, through the compression's column, is at most `H` at every
content of the cell before the read, and the hardwired columns' classical moves are at most `H`,
the weights after the read are at most the weight of `H`. -/
theorem re_trace_gramW_le_dom [Nonempty Y] (h : CellRead e act μ τ K)
    (hc : ClsOff e act K idx φ) (w : Option Y → n → ℝ) (H : n → ℝ)
    (hact : ∀ r, act r → ∀ o a', ∑ a, cr a o ^ 2 * w o (e.symm (a, τ o r)) ≤
      H (e.symm (a', r)))
    (hoff : ∀ s, ¬ act (e s).2 → w (idx s).1 (φ s) ≤ H s)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    ((∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i) * σ).trace.re ≤
      ∑ s, H s * (σ s s).re := by
  obtain ⟨G, hG⟩ : ∃ G : Matrix n n ℂ,
      G = ∑ i, (K i)ᴴ * diagonal (fun u ↦ ((w i.1 u : ℝ) : ℂ)) * K i := ⟨_, rfl⟩
  rw [← hG]
  have hGa : ∀ s, act (e s).2 → ∀ t, G t s = if (e t).2 = (e s).2 then
      ((∑ o, cr (e t).1 o * (∑ a, cr a o ^ 2 * w o (e.symm (a, τ o (e s).2))) *
        cr o (e s).1 : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_apply h w hs t
  have hGo : ∀ s, ¬ act (e s).2 → ∀ t,
      G t s = if t = s then ((w (idx s).1 (φ s) : ℝ) : ℂ) else 0 :=
    fun s hs t ↦ by rw [hG]; exact gramW_off h hc w hs t
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : (G * σ).trace = ∑ s, ∑ t, G t s * σ s t := by
    rw [Matrix.trace]
    simp only [diag_apply, Matrix.mul_apply]
    exact Finset.sum_comm
  have hsplit : ∀ f : n → ℝ, ∑ s, f s = ∑ r, ∑ a, f (e.symm (a, r)) := fun f ↦ by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [htr, Complex.re_sum, hsplit, hsplit]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : act r
  · obtain ⟨S, hS⟩ : ∃ S : Matrix (Option Y) (Option Y) ℂ,
        ∀ a' a, σ (e.symm (a', r)) (e.symm (a, r)) = S a' a := ⟨fun a' a ↦ _, fun _ _ ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Option Y → ℝ,
        ∀ o, ∑ b, cr b o ^ 2 * w o (e.symm (b, τ o r)) = g o := ⟨_, fun _ ↦ rfl⟩
    have hF : ∀ a', ∑ t, G t (e.symm (a', r)) * σ (e.symm (a', r)) t =
        ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a := fun a' ↦ by
      have hs : act (e (e.symm (a', r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
      rw [sum_rest_eq (e := e) r fun t ht ↦ by
        rw [hGa _ hs, Equiv.apply_symm_apply, ite_eq_right ht, zero_mul]]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [hGa _ hs]
      simp only [Equiv.apply_symm_apply, ↓reduceIte, hg, hS]
    have hVc : ∑ a', ∑ a, ((∑ o, cr a o * g o * cr o a' : ℝ) : ℂ) * S a' a =
        ∑ o, (g o : ℂ) * ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ ↦ ?_
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
      push_cast
      ring
    have hVsum : ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a = ∑ a, S a a := by
      calc ∑ o, ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a
          = ∑ a', ∑ a, ∑ o, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a' _ ↦ Finset.sum_comm
        _ = ∑ a', ∑ a, (if a = a' then 1 else 0) * S a' a := by
            refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.sum_mul, sum_cr_mul_cr]
        _ = ∑ a', S a' a' := by
            refine Finset.sum_congr rfl fun a' _ ↦ ?_
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
              ↓reduceIte]
    have hVnn : ∀ o, 0 ≤ (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re := fun o ↦ by
      have hSm := (hσ.submatrix fun a : Option Y ↦ e.symm (a, r)).dotProduct_mulVec_nonneg
        (fun a ↦ ((cr a o : ℝ) : ℂ))
      have key : star (fun a ↦ ((cr a o : ℝ) : ℂ)) ⬝ᵥ
          ((σ.submatrix (fun a : Option Y ↦ e.symm (a, r)) fun a ↦ e.symm (a, r)) *ᵥ
            fun a ↦ ((cr a o : ℝ) : ℂ)) =
          ∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a := by
        simp only [dotProduct, mulVec, submatrix_apply, Pi.star_apply, Complex.star_def,
          Complex.conj_ofReal, hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a' _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [cr_comm o a']
        push_cast
        ring
      rw [key] at hSm
      exact (Complex.nonneg_iff.1 hSm).1
    set m := Finset.univ.inf' Finset.univ_nonempty fun a' : Option Y ↦ H (e.symm (a', r))
    have hgm : ∀ o, g o ≤ m := fun o ↦
      Finset.le_inf' _ _ fun a' _ ↦ by rw [← hg]; exact hact r hr o a'
    simp only [hF]
    rw [← Complex.re_sum, hVc, Complex.re_sum]
    simp only [Complex.re_ofReal_mul]
    have hRHS : ∑ a, (σ (e.symm (a, r)) (e.symm (a, r))).re =
        ∑ o, (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re := by
      have h1 := congrArg Complex.re hVsum
      rw [Complex.re_sum, Complex.re_sum] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun a _ ↦ by rw [hS]
    calc ∑ o, g o * (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re
        ≤ ∑ o, m * (∑ a', ∑ a, ((cr o a' * cr a o : ℝ) : ℂ) * S a' a).re :=
          Finset.sum_le_sum fun o _ ↦ mul_le_mul_of_nonneg_right (hgm o) (hVnn o)
      _ = m * ∑ a, (σ (e.symm (a, r)) (e.symm (a, r))).re := by rw [hRHS, Finset.mul_sum]
      _ ≤ ∑ a, H (e.symm (a, r)) * (σ (e.symm (a, r)) (e.symm (a, r))).re := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right
            (Finset.inf'_le _ (Finset.mem_univ a)) (hre _)
  · refine Finset.sum_le_sum fun a _ ↦ ?_
    have hs : ¬ act (e (e.symm (a, r))).2 := by rw [Equiv.apply_symm_apply]; exact hr
    rw [Finset.sum_eq_single (e.symm (a, r))]
    · rw [hGo _ hs, ite_eq_left rfl, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_right (hoff _ hs) (hre _)
    · intro t _ ht
      rw [hGo _ hs, ite_eq_right ht, zero_mul]
    · simp

end gramDom

/-! ## Steps of a program -/

section step

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) (wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

/-- **A step bound of a program**: from every positive semidefinite start, the total weight of
`x` plus the potentials `U` of its branches at their leaves is at most the potential `V` of the
start. -/
def StepQ {Ω : QReg → Type w} {A : QReg} (x : QuantumComp L spec Ω A)
    (U : (Σ u, Ω u) → Matrix R.D R.D ℂ) (V : Matrix R.D R.D ℂ) : Prop :=
  ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
    R.totalWeight I wt x ρ + ∑' p, potential (U p) ((R.run I x).branch p ρ) ≤ potential V ρ

variable {R I wt}

theorem stepQ_pure {Ω : QReg → Type w} {A : QReg} (U : (Σ u, Ω u) → Matrix R.D R.D ℂ)
    (y : Ω A) : StepQ R I wt (QuantumComp.pure (L := L) (spec := spec) y) U (U ⟨A, y⟩) := by
  intro ρ _
  rw [totalWeight_pure, zero_add, run_pure, tsum_eq_single (⟨A, y⟩ : Σ u, Ω u) fun p hp ↦ by
      rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
      simp [potential],
    DSubInstrument.branch_ret_self, LinearMap.id_apply]

theorem stepQ_mono {Ω : QReg → Type w} {A : QReg} {x : QuantumComp L spec Ω A}
    {U : (Σ u, Ω u) → Matrix R.D R.D ℂ} {V V' : Matrix R.D R.D ℂ} (hx : StepQ R I wt x U V)
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef → potential V ρ ≤ potential V' ρ) :
    StepQ R I wt x U V' :=
  fun ρ hρ ↦ (hx ρ hρ).trans (h ρ hρ)

/-- **A local operation**: the continuations' bounds `V' b`, summed over the operation's
branches, are at most `V`. -/
theorem stepQ_primBind {Ω : QReg → Type w} {A : QReg} (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec Ω (L.next o b))
    {U : (Σ u, Ω u) → Matrix R.D R.D ℂ} (V' : L.Outcome o → Matrix R.D R.D ℂ)
    {V : Matrix R.D R.D ℂ} (hk : ∀ b, StepQ R I wt (k b) U (V' b))
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      ∑' b, potential (V' b) (((I o).frame R.D).branch b ρ) ≤ potential V ρ) :
    StepQ R I wt (QuantumComp.primBind o k) U V := by
  intro ρ hρ
  have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
  have hL : ∀ p, potential (U p) ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
      ∑' b, potential (U p) ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) :=
    fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact potential_tsum _ ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
        fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
  simp only [hL]
  rw [ENNReal.tsum_comm, totalWeight_primBind, ← ENNReal.tsum_add]
  exact (ENNReal.tsum_le_tsum fun b ↦ hk b _ (hρb b)).trans (h ρ hρ)

/-- **A call**: the call's weight plus the continuations' bounds `V' r`, summed over the call's
branches, are at most `V`. -/
theorem stepQ_queryBind {Ω : QReg → Type w} {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E) (k : spec.Result i → QuantumComp L spec Ω (QReg.of (spec.Out i × E)))
    {U : (Σ u, Ω u) → Matrix R.D R.D ℂ} (V' : spec.Result i → Matrix R.D R.D ℂ)
    {V : Matrix R.D R.D ℂ} (hk : ∀ r, StepQ R I wt (k r) U (V' r))
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      wt i (callInput ℓ R.D ρ) + ∑' r, potential (V' r) ((R.queryStep i E ℓ).branch r ρ) ≤
        potential V ρ) :
    StepQ R I wt (QuantumComp.queryBind i E ℓ k) U V := by
  intro ρ hρ
  have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
  have hL : ∀ p, potential (U p) ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
      ∑' r, potential (U p) ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)) :=
    fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact potential_tsum _ (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
        (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
        fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
  simp only [hL]
  rw [ENNReal.tsum_comm, totalWeight_queryBind, add_assoc, ← ENNReal.tsum_add]
  exact (add_le_add le_rfl (ENNReal.tsum_le_tsum fun r ↦ hk r _ (hρr r))).trans (h ρ hρ)

/-- `stepQ_primBind` on the raw command node. -/
theorem stepQ_liftBind_prim {Ω : QReg → Type w} {A : QReg} (o : L.Op A)
    (k : (b : (QuantumComp.toIPFunctor L spec).B A (.prim o)) →
      QuantumComp L spec Ω ((QuantumComp.toIPFunctor L spec).src A (.prim o) b))
    {U : (Σ u, Ω u) → Matrix R.D R.D ℂ} (V' : L.Outcome o → Matrix R.D R.D ℂ)
    {V : Matrix R.D R.D ℂ} (hk : ∀ b, StepQ R I wt (k ⟨b⟩) U (V' b))
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      ∑' b, potential (V' b) (((I o).frame R.D).branch b ρ) ≤ potential V ρ) :
    StepQ R I wt (IFreeM.liftBind (P := QuantumComp.toIPFunctor L spec) (.prim o) k) U V :=
  stepQ_primBind o (fun b ↦ k ⟨b⟩) V' hk h

/-- `stepQ_queryBind` on the raw command node. -/
theorem stepQ_liftBind_query {Ω : QReg → Type w} {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : (b : (QuantumComp.toIPFunctor L spec).B A (.query i E ℓ)) →
      QuantumComp L spec Ω ((QuantumComp.toIPFunctor L spec).src A (.query i E ℓ) b))
    {U : (Σ u, Ω u) → Matrix R.D R.D ℂ} (V' : spec.Result i → Matrix R.D R.D ℂ)
    {V : Matrix R.D R.D ℂ} (hk : ∀ r, StepQ R I wt (k ⟨r⟩) U (V' r))
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
      wt i (callInput ℓ R.D ρ) + ∑' r, potential (V' r) ((R.queryStep i E ℓ).branch r ρ) ≤
        potential V ρ) :
    StepQ R I wt (IFreeM.liftBind (P := QuantumComp.toIPFunctor L spec) (.query i E ℓ) k) U V :=
  stepQ_queryBind i E ℓ (fun r ↦ k ⟨r⟩) V' hk h

/-- A pure node, raw. -/
theorem stepQ_pure' {Ω : QReg → Type w} {A : QReg} (U : (Σ u, Ω u) → Matrix R.D R.D ℂ)
    (y : Ω A) :
    StepQ R I wt (IFreeM.pure (P := QuantumComp.toIPFunctor L spec) y) U (U ⟨A, y⟩) :=
  stepQ_pure U y

variable (R I wt) in
/-- **A step bound of a fixed-register program**, with the leaf potentials `U a` at the return
values. -/
def Step₂ {A B : QReg} {α : Type w} (x : QuantumComp₂ L spec A B α)
    (U : α → Matrix R.D R.D ℂ) (V : Matrix R.D R.D ℂ) : Prop :=
  ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef →
    R.totalWeight I wt x ρ + ∑' a, potential (U a) ((R.run₂ I x).branch a ρ) ≤ potential V ρ

theorem step₂_iff_stepQ {A B : QReg} {α : Type w} (x : QuantumComp₂ L spec A B α)
    (U : α → Matrix R.D R.D ℂ) (V : Matrix R.D R.D ℂ) :
    Step₂ R I wt x U V ↔
      StepQ R I wt x (fun p ↦ U ((QuantumComp₂.leafEquiv B α).symm p)) V := by
  refine forall_congr' fun ρ ↦ forall_congr' fun _ ↦ ?_
  rw [← (QuantumComp₂.leafEquiv B α).tsum_eq]
  rfl

theorem step₂_pure {A : QReg} {α : Type w} (U : α → Matrix R.D R.D ℂ) (a : α) :
    Step₂ R I wt (QuantumComp₂.pure (L := L) (spec := spec) (A := A) a) U (U a) := by
  rw [step₂_iff_stepQ]
  exact stepQ_pure _ _

theorem step₂_mono {A B : QReg} {α : Type w} {x : QuantumComp₂ L spec A B α}
    {U : α → Matrix R.D R.D ℂ} {V V' : Matrix R.D R.D ℂ} (hx : Step₂ R I wt x U V)
    (h : ∀ ρ : Matrix (A × R.D) (A × R.D) ℂ, ρ.PosSemidef → potential V ρ ≤ potential V' ρ) :
    Step₂ R I wt x U V' :=
  fun ρ hρ ↦ (hx ρ hρ).trans (h ρ hρ)

/-- **Sequencing**, for a weight given by the trace of completely positive maps: a bound `V'` at
the leaves of `x` that bounds every continuation. -/
theorem step₂_bind {K : spec.Port → Type*} [∀ i, Fintype (K i)]
    {Φ : ∀ i, MatrixMap (spec.In i × R.D) (K i)} (hΦ : ∀ i, (Φ i).IsCP) {A B C : QReg}
    {α β : Type w} (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    {U : β → Matrix R.D R.D ℂ} (V' : α → Matrix R.D R.D ℂ) {V : Matrix R.D R.D ℂ}
    (hx : Step₂ R I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x V' V)
    (hk : ∀ a, Step₂ R I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k a) U (V' a)) :
    Step₂ R I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (x.bind k) U V := by
  intro ρ hρ
  have hρa := fun a ↦ (R.run₂ I x).posSemidef_branch_apply a hρ
  have htw : R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (x.bind k) ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x ρ +
        ∑' a, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k a)
          ((R.run₂ I x).branch a ρ) := by
    refine (R.totalWeight_bind I hΦ x
      (fun u (p : QuantumComp₂.Leaf B α u) ↦ p.casesOn fun h a ↦ h ▸ k a) hρ).trans
      (congrArg (_ + ·) ?_)
    rw [← (QuantumComp₂.leafEquiv B α).tsum_eq]
    rfl
  have hbr : ∀ b, potential (U b) ((R.run₂ I (x.bind k)).branch b ρ) =
      ∑' a, potential (U b) ((R.run₂ I (k a)).branch b ((R.run₂ I x).branch a ρ)) := fun b ↦ by
    rw [run₂_bind]
    rw [DSubInstrument.branch_bind_apply]
    exact potential_tsum _ (((R.run₂ I x).isCPTNIFamily.comp_eval
      (fun a ↦ (R.run₂ I (k a)).isCPTNIFamily) b).summable_apply ρ)
      fun a ↦ (R.run₂ I (k a)).posSemidef_branch_apply b (hρa a)
  rw [htw]
  simp only [hbr]
  rw [ENNReal.tsum_comm, add_assoc, ← ENNReal.tsum_add]
  exact (add_le_add le_rfl (ENNReal.tsum_le_tsum fun a ↦ hk a _ (hρa a))).trans
    ((le_of_eq (by rfl)).trans (hx ρ hρ))

end step

/-! ## Diagonal potentials -/

section wPot

/-- The potential of the diagonal weight `f`: `potential (wPot f) ρ = ∑ f q.2 ρ_qq`. -/
noncomputable def wPot {n : Type*} [DecidableEq n] (f : n → ℝ) : Matrix n n ℂ :=
  diagPot fun s ↦ √(f s)

theorem potential_wPot {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {f : β → ℝ} (hf : ∀ s, 0 ≤ f s) (σ : Matrix (α × β) (α × β) ℂ) :
    potential (wPot f) σ = ENNReal.ofReal (∑ q, f q.2 * (σ q q).re) :=
  Quantum.Xmss.Assembly.potential_diagPot_sqrt hf σ

/-- The diagonal potentials are monotone in the weight. -/
theorem potential_wPot_mono {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {f g : β → ℝ} (hf : ∀ s, 0 ≤ f s) (hfg : ∀ s, f s ≤ g s)
    {σ : Matrix (α × β) (α × β) ℂ} (hσ : σ.PosSemidef) :
    potential (wPot f) σ ≤ potential (wPot g) σ := by
  rw [potential_wPot hf, potential_wPot fun s ↦ (hf s).trans (hfg s)]
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right
    (hfg q.2) (Complex.nonneg_iff.1 hσ.diag_nonneg).1)

/-- The diagonal potential of a sum is the sum. -/
theorem potential_wPot_add {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {f g : β → ℝ} (hf : ∀ s, 0 ≤ f s) (hg : ∀ s, 0 ≤ g s)
    {σ : Matrix (α × β) (α × β) ℂ} (hσ : σ.PosSemidef) :
    potential (wPot fun s ↦ f s + g s) σ = potential (wPot f) σ + potential (wPot g) σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [potential_wPot fun s ↦ add_nonneg (hf s) (hg s), potential_wPot hf, potential_wPot hg,
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf _) (hre q))
      (Finset.sum_nonneg fun q _ ↦ mul_nonneg (hg _) (hre q)), ← Finset.sum_add_distrib]
  simp only [add_mul]

/-- A uniform coin, framed, scales every branch by the inverse of the number of outcomes. -/
theorem branch_frame_uniform {Ω A D : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [DecidableEq A]
    [Fintype D] (ω : Ω) (ρ : Matrix (A × D) (A × D) ℂ) :
    ((SubInstrument.uniform Ω A).frame D).branch ω ρ = ((Fintype.card Ω : ℂ)⁻¹) • ρ := by
  ext x y
  rw [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply,
    SubInstrument.branch_uniform_apply]
  rfl

/-- The potentials of the branches of a framed uniform coin: the average. -/
theorem tsum_potential_frame_uniform {Ω A D : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A]
    [DecidableEq A] [Fintype D] [DecidableEq D] (f : Ω → D → ℝ) (hf : ∀ ω s, 0 ≤ f ω s)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' ω, potential (wPot (f ω)) (((SubInstrument.uniform Ω A).frame D).branch ω ρ) =
      potential (wPot fun s ↦ ∑ ω, (Fintype.card Ω : ℝ)⁻¹ * f ω s) ρ := by
  have hre : ∀ q, 0 ≤ (ρ q q).re := fun q ↦ (Complex.nonneg_iff.1 hρ.diag_nonneg).1
  have hN : (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have hω : ∀ ω, potential (wPot (f ω)) (((SubInstrument.uniform Ω A).frame D).branch ω ρ) =
      ENNReal.ofReal (∑ q, (Fintype.card Ω : ℝ)⁻¹ * f ω q.2 * (ρ q q).re) := fun ω ↦ by
    rw [branch_frame_uniform, potential_wPot (hf ω)]
    congr 1
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Matrix.smul_apply, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul]
    ring
  simp only [hω]
  rw [potential_wPot fun s ↦ Finset.sum_nonneg fun ω _ ↦ mul_nonneg hN (hf ω s),
    tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ Finset.sum_nonneg fun q _ ↦
      mul_nonneg (mul_nonneg hN (hf ω _)) (hre q)]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_mul]

end wPot

/-! ## A read with outcome-dependent weights -/

section readStep

open Quantum.Xmss.Assembly (sum_dW_conj_dep)

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M]
  [DecidableEq M]

/-- The columns of the compression have norm one, also at `⊥`. -/
theorem sum_cr_sq_all [Nonempty X] (o : Option X) : ∑ a, cr a o ^ 2 = 1 := by
  rcases o with _ | y
  · have hN : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Fintype.sum_option]
    simp only [cr_comm _ none, cr_none_some_sq, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    simp [cr, hN]
  · exact sum_cr_sq y

/-- **A read of `h` with outcome-dependent weights**: if every outcome's weight after the read
of the unhardwired cell `z`, at every content of the cell, is at most `H` before, and the
classical move of a hardwired cell too, the weights after the read are at most the weight of
`H`. -/
theorem sum_ofReal_readH_le [Nonempty X] (z : Z) (u : M → Option X → M)
    (U : Option X → HwReg X Z M → ℝ) (hU : ∀ o s, 0 ≤ U o s) (H : HwReg X Z M → ℝ)
    (hact : ∀ s : HwReg X Z M, s.2.1.1 z = none → ∀ o a,
      U o ((Function.update s.1.1 z a, s.1.2), s.2.1, u s.2.2 o) ≤ H s)
    (hoff : ∀ s : HwReg X Z M, s.2.1.1 z ≠ none →
      U (s.2.1.1 z) (s.1, s.2.1, u s.2.2 (s.2.1.1 z)) ≤ H s)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑ r : Option X × M, ENNReal.ofReal (∑ q, U r.1 q.2 *
      ((MatrixMap.conj (hwReadKraus (.readH z u) r) σ) q q).re) ≤
      ENNReal.ofReal (∑ q, H q.2 * (σ q q).re) := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ Finset.sum_nonneg fun q _ ↦ mul_nonneg (hU _ _)
    (Complex.nonneg_iff.1
      ((MatrixMap.isCP_conj (hwReadKraus (.readH z u) r)).posSemidef hσ).diag_nonneg).1]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := sum_dW_conj_dep (fun r ↦ hwReadKraus (.readH z u) r) (fun r q ↦ U r.1 q.2) σ
  refine (le_of_eq h1).trans ?_
  refine re_trace_gramW_le_dom (cellRead_readH (z := z) u) (clsOff_readH z u)
    (fun o q ↦ U o q.2) (fun q ↦ H q.2) (fun r hr o a' ↦ ?_) (fun q hq ↦ hoff q.2 hq) hσ
  set q := (splitH' z).symm (a', r) with hq
  have hr' : (splitH' z q).2 = r := by rw [hq, Equiv.apply_symm_apply]
  have hz : q.2.2.1.1 z = none := by
    rw [← hr'] at hr
    exact hr
  calc ∑ a, cr a o ^ 2 * U o ((splitH' z).symm (a, tauH z u o r)).2
      = ∑ a, cr a o ^ 2 *
          U o ((Function.update q.2.1.1 z a, q.2.1.2), q.2.2.1, u q.2.2.2 o) := by
        rw [← hr']
        simp only [splitH'_symm_tau]
    _ ≤ ∑ a, cr a o ^ 2 * H q.2 :=
        Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hact q.2 hz o a) (sq_nonneg _)
    _ = H q.2 := by rw [← Finset.sum_mul, sum_cr_sq_all, one_mul]

end readStep

/-! ## The read programs of the challenger's calls -/

section calls

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)

variable {Sx M' : Type} [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M']

omit [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M'] in
/-- A substitution distributes over sequencing of fixed-register programs. -/
theorem readProgOf_bind₂
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    {A B C : QReg} {α β : Type} (x : QComp (MixSpec Caller) A B α)
    (k : α → QComp (MixSpec Caller) B C β) :
    readProgOf upd (x.bind k) =
      QuantumComp₂.bind (readProgOf upd x) fun a ↦ readProgOf upd (k a) := by
  have h1 : IFreeM.substitute (readSub upd) (x.bind k) =
      QuantumComp₂.bind (IFreeM.substitute (readSub upd) x) fun a ↦
        IFreeM.substitute (readSub upd) (k a) :=
    (IFreeM.substitute_bind (readSub upd) x _).trans
      (congrArg _ (funext fun _ ↦ funext fun ⟨h, _⟩ ↦ by subst h; rfl))
  have h2 := IFreeM.substitute_bind Quantum.Xmss.Assembly.liftReadLens.toSubstitution
    (IFreeM.substitute (readSub upd) x : IFreeM (QuantumComp.toIPFunctor
      LocalSig.instruments.{0} (Quantum.Sponge.hwReadSpec HashOutput HashDomain (Finset Sx × M')))
      (QuantumComp₂.Leaf B α) A)
    (fun _ p ↦ p.casesOn fun h a ↦ h ▸ IFreeM.substitute (readSub upd) (k a))
  simp only [IFreeM.substitute_toSubstitution] at h2
  change IFreeM.mapLens _ (IFreeM.substitute (readSub upd) (x.bind k)) = _
  rw [h1]
  refine h2.trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

/-- One step of a step bound: normalize the program's head. -/
local macro "step_whnf" : tactic => `(tactic| (conv => arg 4; whnf))

/-- A local operation of a step bound keeping the potential. -/
local macro "step_prim" : tactic => `(tactic| (
  step_whnf;
  refine stepQ_liftBind_prim _ _ (fun _ ↦ _) (fun _ ↦ ?_)
    (fun ρ hρ ↦ tsum_potential_frame_le _ _ hρ)))

/-- The local operations up to the leaf, keeping the potential. -/
local macro "step_finish" : tactic => `(tactic| (
  repeat step_prim
  step_whnf
  exact stepQ_pure' _ _))

variable (m₀ : Finset Sx × M')
  (wt : ∀ i, Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
    HwReg HashOutput HashDomain (Finset Sx × M'))
    ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
      HwReg HashOutput HashDomain (Finset Sx × M')) ℂ → ℝ≥0∞)

/-- **A coin of the challenger**: the leaves' weights averaged over the coin. -/
theorem step₂_call_coin
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (B : QReg) (n : ℕ) (U : Fin (n + 1) → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ)
    (hU : ∀ b s, 0 ≤ U b s) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments wt
      (readProgOf upd (mixImpl .answer B (.inl n))) (fun b ↦ wPot (U b))
      (wPot fun s ↦ ∑ b, ((n + 1 : ℕ) : ℝ)⁻¹ * U b s) := by
  refine (step₂_iff_stepQ _ _ _).2 ?_
  step_prim
  step_whnf
  refine stepQ_liftBind_prim _ _ (fun b ↦ wPot (U b)) (fun b ↦ ?_) (fun ρ hρ ↦ ?_)
  · step_finish
  · have h := tsum_potential_frame_uniform (Ω := Fin (n + 1)) U hU hρ
    rw [Fintype.card_fin] at h
    exact h.le

/-- **The read of a trial at a call**: its weight `wt ≤ Lf` plus the leaves' weights after the
read, at most `H` (`sum_ofReal_readH_le`), are at most the weight of `Lf + H`. -/
theorem query_readH_le (x : HashDomain) (u : Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (U : HashOutput → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hU : ∀ v s, 0 ≤ U v s)
    (Lf H : HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hL : ∀ s, 0 ≤ Lf s)
    (hH : ∀ s, 0 ≤ H s)
    (hd : ∀ σ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
        (.inl (.inr (.readH x u))) × HwReg HashOutput HashDomain (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
          (.inl (.inr (.readH x u))) × HwReg HashOutput HashDomain (Finset Sx × M')) ℂ,
      σ.PosSemidef → wt (.inl (.inr (.readH x u))) σ ≤ ENNReal.ofReal (∑ q, Lf q.2 * (σ q q).re))
    (hact : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x = none → ∀ o a,
      U (o.getD 0) ((Function.update s.1.1 x a, s.1.2), s.2.1, u s.2.2 o) ≤ H s)
    (hoff : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x ≠ none →
      U ((s.2.1.1 x).getD 0) (s.1, s.2.1, u s.2.2 (s.2.1.1 x)) ≤ H s)
    {A E : QReg} (ℓ : A ≃ (hwSpec HashOutput HashDomain (Finset Sx × M')).In
      (.inl (.inr (.readH x u))) × E)
    {ρ : Matrix (A × HwReg HashOutput HashDomain (Finset Sx × M'))
      (A × HwReg HashOutput HashDomain (Finset Sx × M')) ℂ} (hρ : ρ.PosSemidef) :
    wt (.inl (.inr (.readH x u))) (callInput ℓ _ ρ) +
      ∑' r : Option HashOutput × (Finset Sx × M'), potential (wPot (U (r.1.getD 0)))
        (((runtime2 HashOutput HashDomain m₀).queryStep (.inl (.inr (.readH x u))) E ℓ).branch
          r ρ) ≤
      potential (wPot fun s ↦ Lf s + H s) ρ := by
  have hσ := posSemidef_callInput (D := HwReg HashOutput HashDomain (Finset Sx × M')) ℓ hρ
  rw [potential_wPot_add hL hH hρ, ← potential_callInput (wPot Lf) ℓ ρ,
    ← potential_callInput (wPot H) ℓ ρ]
  refine add_le_add ((hd _ hσ).trans_eq (potential_wPot hL _).symm) ?_
  have hsum : ∑' r : Option HashOutput × (Finset Sx × M'), potential (wPot (U (r.1.getD 0)))
      (((runtime2 HashOutput HashDomain m₀).queryStep (.inl (.inr (.readH x u))) E ℓ).branch
        r ρ) =
      ∑ r : Option HashOutput × (Finset Sx × M'), ENNReal.ofReal (∑ q, U (r.1.getD 0) q.2 *
        ((MatrixMap.conj (hwReadKraus (.readH x u) r) (callInput ℓ _ ρ)) q q).re) := by
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    exact (potential_queryStep (runtime2 HashOutput HashDomain m₀) (wPot (U (r.1.getD 0)))
      (.inl (.inr (.readH x u))) E ℓ r ρ).trans ((congrArg (potential _)
        (LinearMap.congr_fun (runtime2_branch m₀ (.inl (.inr (.readH x u))) r) _)).trans
          (potential_wPot (hU _) _))
  rw [hsum]
  exact (sum_ofReal_readH_le x u (fun o s ↦ U (o.getD 0) s) (fun _ _ ↦ hU _ _) H hact hoff
    hσ).trans_eq (potential_wPot hH _).symm

/-- **A trial read of the challenger**: its weight `Lf` and the leaves' weights `U v` after the
read, bounded by `H` before. -/
theorem step₂_call_read
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (B : QReg) (x : HashDomain)
    (U : HashOutput → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hU : ∀ v s, 0 ≤ U v s)
    (Lf H : HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hL : ∀ s, 0 ≤ Lf s)
    (hH : ∀ s, 0 ≤ H s)
    (hd : ∀ σ : Matrix ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
        (.inl (.inr (.readH x (upd .answer x)))) × HwReg HashOutput HashDomain (Finset Sx × M'))
        ((hwSpec HashOutput HashDomain (Finset Sx × M')).In
          (.inl (.inr (.readH x (upd .answer x)))) ×
            HwReg HashOutput HashDomain (Finset Sx × M')) ℂ,
      σ.PosSemidef → wt (.inl (.inr (.readH x (upd .answer x)))) σ ≤
        ENNReal.ofReal (∑ q, Lf q.2 * (σ q q).re))
    (hact : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x = none → ∀ o a,
      U (o.getD 0) ((Function.update s.1.1 x a, s.1.2), s.2.1, upd .answer x s.2.2 o) ≤ H s)
    (hoff : ∀ s : HwReg HashOutput HashDomain (Finset Sx × M'), s.2.1.1 x ≠ none →
      U ((s.2.1.1 x).getD 0) (s.1, s.2.1, upd .answer x s.2.2 (s.2.1.1 x)) ≤ H s) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments wt
      (readProgOf upd (mixImpl .answer B (.inr x))) (fun v ↦ wPot (U v))
      (wPot fun s ↦ Lf s + H s) := by
  refine (step₂_iff_stepQ _ _ _).2 ?_
  step_prim
  step_whnf
  refine stepQ_liftBind_query (R := runtime2 HashOutput HashDomain m₀) (I := .instruments)
    (wt := wt) (.inl (.inr (.readH x (upd .answer x)))) _ _ _
    (fun r : Option HashOutput × (Finset Sx × M') ↦ wPot (U (r.1.getD 0))) (fun r ↦ ?_)
    (fun ρ hρ ↦ query_readH_le m₀ wt x (upd .answer x) U hU Lf H hL hH hd hact hoff _ hρ)
  step_finish

end calls

/-! ## The challenger's sampler -/

section sampler

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)

variable {Sx M' : Type} [Fintype Sx] [DecidableEq Sx] [Fintype M'] [DecidableEq M']

/-- A sampler lifted to the model's oracles is answered by the model's coins. -/
theorem toQuantumAt_liftComp {spec : QuantumOracleSpec.{0, 0}} {B : QReg} {α : Type}
    (pa : ProbComp α) (q : QueryImpl romWorld.Oracles (QComp spec B B)) :
    (liftComp pa romWorld.Oracles).toQuantumAt q = pa.toQuantumAt fun n ↦ q (.inl n) := by
  induction pa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    have hq : liftComp (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) romWorld.Oracles =
        (liftM (romWorld.Oracles.query (.inl n)) :
          OracleComp romWorld.Oracles (Fin (n + 1))) :=
      liftComp_liftM_query _ n
    rw [liftComp_bind, hq, toQuantumAt_query_bind, toQuantumAt_query_bind]
    exact congrArg _ (funext ih)

variable (m₀ : Finset Sx × M') {K : (hwSpec HashOutput HashDomain (Finset Sx × M')).Port → Type}
  [∀ i, Fintype (K i)]
  {Φ : ∀ i, MatrixMap ((hwSpec HashOutput HashDomain (Finset Sx × M')).In i ×
    HwReg HashOutput HashDomain (Finset Sx × M')) (K i)} (hΦ : ∀ i, (Φ i).IsCP)
include hΦ

/-- **The challenger's sampler**: the leaves' weights averaged over the sampler's law. -/
theorem step₂_sampler
    (upd : Caller → HashDomain → Finset Sx × M' → Option HashOutput → Finset Sx × M')
    (B : QReg) {α : Type} [Fintype α] (pa : ProbComp α)
    (U : α → HwReg HashOutput HashDomain (Finset Sx × M') → ℝ) (hU : ∀ a s, 0 ≤ U a s) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments
      (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re)
      (readProgOf upd (pa.toQuantumAt fun n ↦ mixImpl .answer B (.inl n)))
      (fun a ↦ wPot (U a))
      (wPot fun s ↦ ∑ a, (Pr{let z ← pa}[z = a]).toReal * U a s) := by
  classical
  induction pa using OracleComp.inductionOn with
  | pure a =>
    refine step₂_mono (step₂_pure _ a) fun ρ hρ ↦ potential_wPot_mono (hU a) (fun s ↦ ?_) hρ
    rw [Finset.sum_eq_single a (fun b _ hb ↦ by rw [prEvent_pure, ite_eq_right (Ne.symm hb)]; simp)
      (by simp), prEvent_pure, ite_eq_left rfl, ENNReal.toReal_one, one_mul]
  | query_bind n k ih =>
    rw [toQuantumAt_query_bind, readProgOf_bind₂]
    have hV : ∀ b s, 0 ≤ ∑ a, (Pr{let z ← k b}[z = a]).toReal * U a s := fun b s ↦
      Finset.sum_nonneg fun a _ ↦ mul_nonneg ENNReal.toReal_nonneg (hU a s)
    refine step₂_mono (step₂_bind hΦ _ _ _
      (step₂_call_coin m₀ _ upd B n (fun b s ↦ ∑ a, (Pr{let z ← k b}[z = a]).toReal * U a s) hV)
      fun b ↦ ih b) fun ρ hρ ↦
        potential_wPot_mono (fun s ↦ Finset.sum_nonneg fun b _ ↦ mul_nonneg (by positivity)
          (hV b s)) (fun s ↦ le_of_eq ?_) hρ
    have hq : ∀ b : Fin (n + 1),
        Pr{let z ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))}[z = b] =
          ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := fun b ↦ by
      simpa [Finset.filter_eq'] using
        (prEvent_liftM_query_eq_card_div (spec := unifSpec) n (fun x ↦ x = b))
    have hP : ∀ a, (Pr{let z ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= k}[
        z = a]).toReal = ∑ b, ((n + 1 : ℕ) : ℝ)⁻¹ * (Pr{let z ← k b}[z = a]).toReal :=
      fun a ↦ by
        rw [prEvent_bind_eq_sum_fintype, ENNReal.toReal_sum fun b _ ↦
          ENNReal.mul_ne_top (by rw [hq]; simp) (prEvent_ne_top _)]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [ENNReal.toReal_mul, hq, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp only [hP, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring

end sampler

/-! ## The grind of an answer -/

section grind

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The weight of the trials `c, …, c + n - 1`, the trial `c'` weighing `f c'`. -/
def gsum (f : ℕ → HwReg HashOutput HashDomain Mem → ℝ) :
    ℕ → ℕ → HwReg HashOutput HashDomain Mem → ℝ
  | _, 0 => fun _ ↦ 0
  | c, n + 1 => fun s ↦ f c s + gsum f (c + 1) n s

theorem gsum_nonneg {f : ℕ → HwReg HashOutput HashDomain Mem → ℝ} (hf : ∀ c s, 0 ≤ f c s) :
    ∀ n c s, 0 ≤ gsum f c n s
  | 0, _, _ => le_rfl
  | n + 1, c, s => add_nonneg (hf c s) (gsum_nonneg hf n (c + 1) s)

theorem gsum_congr {f : ℕ → HwReg HashOutput HashDomain Mem → ℝ}
    {s s' : HwReg HashOutput HashDomain Mem} :
    ∀ n c, (∀ c', c ≤ c' → c' < c + n → f c' s' = f c' s) → gsum f c n s' = gsum f c n s
  | 0, _, _ => rfl
  | n + 1, c, h => by
    change f c s' + gsum f (c + 1) n s' = f c s + gsum f (c + 1) n s
    rw [h c le_rfl (by omega),
      gsum_congr n (c + 1) fun c' hc' hc'' ↦ h c' (by omega) (by omega)]

theorem gsum_eq_sum (f : ℕ → HwReg HashOutput HashDomain Mem → ℝ) :
    ∀ n c s, gsum f c n s = ∑ j ∈ Finset.range n, f (c + j) s
  | 0, _, _ => by simp [gsum]
  | n + 1, c, s => by
    rw [Finset.sum_range_succ']
    change f c s + gsum f (c + 1) n s = _
    rw [gsum_eq_sum f n (c + 1) s, add_comm]
    refine congrArg (· + _) (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [add_assoc, add_comm 1 j]

variable {e}

/-- One trial of a grind: the read of the trial's cell, then the codeword test. -/
theorem toQuantumAt_grind_succ (hlen : e.hash.LengthLe maxLen) {spec : QuantumOracleSpec.{0, 0}}
    {B : QReg} (q : QueryImpl romWorld.Oracles (QComp spec B B)) (P : Par) (t : Tw) (M : Msg)
    (r0 : Salt) (c n : ℕ) :
    (e.grind romWorld P t M r0 c (n + 1)).toQuantumAt q =
      (q (.inr (cell e P t (M, e.shift r0 c)))).bind fun v ↦
        (if e.isCode (e.hash.trunc v) then pure (some (e.shift r0 c, e.hash.trunc v)) else
          e.grind romWorld P t M r0 (c + 1) n).toQuantumAt q := by
  have hq : e.hash.eval romWorld () P t (M, e.shift r0 c) = e.hash.trunc <$>
      (liftM (romWorld.Oracles.query (.inr (cell e P t (M, e.shift r0 c)))) :
        OracleComp romWorld.Oracles HashOutput) := by
    rw [TwColl.eval]
    exact congrArg _ (hashQ_of_encodeInput_eq_some (encodeInput_cell hlen P t _))
  rw [SaltEnc.grind, hq, map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind]
  exact toQuantumAt_query_bind q _ _

variable (m₀ : Mem) {K : (hwSpec HashOutput HashDomain Mem).Port → Type} [∀ i, Fintype (K i)]
  {Φ : ∀ i, MatrixMap ((hwSpec HashOutput HashDomain Mem).In i ×
    HwReg HashOutput HashDomain Mem) (K i)} (hΦ : ∀ i, (Φ i).IsCP)
include hΦ

/-- **A grind**: trial `c' < L` weighs at most `f c'` at its read, and the weights of the later
trials ignore the cell of a trial and its memory move when its outcome is not a codeword. -/
theorem step₂_grind (hlen : e.hash.LengthLe maxLen) (B : QReg) (P : Par) (t : Tw) (M : Msg)
    (r0 : Salt) (f : ℕ → HwReg HashOutput HashDomain Mem → ℝ) (hf : ∀ c s, 0 ≤ f c s) (L : ℕ)
    (hd : ∀ c, c < L → ∀ (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In
        (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) × HwReg HashOutput HashDomain Mem)
        ((hwSpec HashOutput HashDomain Mem).In
          (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
            (upd e .answer (cell e P t (M, e.shift r0 c)))))) ×
              HwReg HashOutput HashDomain Mem) ℂ),
      σ.PosSemidef → ENNReal.ofReal (Φ (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) σ).trace.re ≤
        ENNReal.ofReal (∑ q, f c q.2 * (σ q q).re))
    (hinv : ∀ c c', c < c' → c' < L → ∀ (s : HwReg HashOutput HashDomain Mem) a o,
      e.isCode (e.hash.trunc (o.getD 0)) = false →
      f c' ((Function.update s.1.1 (cell e P t (M, e.shift r0 c)) a, s.1.2), s.2.1,
        upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2 o) = f c' s) :
    ∀ n c, c + n ≤ L → Step₂ (runtime2 HashOutput HashDomain m₀) .instruments
      (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re)
      (readProgOf (upd e) ((e.grind romWorld P t M r0 c n).toQuantumAt (mixImpl .answer B)))
      (fun _ ↦ wPot fun _ ↦ 0) (wPot (gsum f c n)) := by
  intro n
  induction n with
  | zero =>
    intro c _
    exact step₂_pure _ none
  | succ n ih =>
    intro c hcL
    rw [toQuantumAt_grind_succ hlen, readProgOf_bind₂]
    have hG := gsum_nonneg hf n (c + 1)
    set x := cell e P t (M, e.shift r0 c)
    refine step₂_bind hΦ _ _ (fun v ↦ wPot fun s ↦
        if e.isCode (e.hash.trunc v) then 0 else gsum f (c + 1) n s)
      (step₂_call_read m₀ _ (upd e) B x _ (fun v s ↦ by split_ifs <;> simp [hG]) (f c)
        (gsum f (c + 1) n) (hf c) hG (hd c (by omega)) (fun s _ o a ↦ ?_) (fun s _ ↦ ?_))
      fun v ↦ ?_
    · split_ifs with hv
      · exact hG s
      · exact le_of_eq (gsum_congr n (c + 1) fun c' hc' hc'' ↦
          hinv c c' (by omega) (by omega) s a o (Bool.not_eq_true _ ▸ hv))
    · split_ifs with hv
      · exact hG s
      · refine le_of_eq ?_
        have h := gsum_congr (f := f) (s := s)
          (s' := ((Function.update s.1.1 x (s.1.1 x), s.1.2), s.2.1,
            upd e .answer x s.2.2 (s.2.1.1 x))) n (c + 1) fun c' hc' hc'' ↦
          hinv c c' (by omega) (by omega) s _ _ (Bool.not_eq_true _ ▸ hv)
        rwa [Function.update_eq_self] at h
    · by_cases hv : e.isCode (e.hash.trunc v) = true
      · simp only [hv, ↓reduceIte]
        exact step₂_pure _ _
      · simp only [hv, Bool.false_eq_true, ↓reduceIte]
        exact ih (c + 1) (by omega)

end grind

/-! ## The trial costs as a trace of completely positive maps -/

section dSCP

open Quantum.Qrom HashSig Props
open Tcr (Mem BadR uRed uJudge)

variable {Par Tw Msg Salt Dig : Type} (e : SaltEnc Par Tw Msg Salt Dig)

/-- The trace of a diagonal weight. -/
theorem re_trace_conj_wPot {n : Type*} [Fintype n] [DecidableEq n] {f : n → ℝ}
    (hf : ∀ q, 0 ≤ f q) (σ : Matrix n n ℂ) :
    (MatrixMap.conj (wPot f) σ).trace.re = ∑ q, f q * (σ q q).re := by
  rw [MatrixMap.conj_apply, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [wPot, diagPot, Matrix.diag_apply, diagonal_conjTranspose, diagonal_mul,
    mul_diagonal, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf q),
    Complex.re_ofReal_mul]

theorem readLin_nonneg {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [Fintype M] [DecidableEq M] (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (z : Z)
    (u : M → Option X → M) (q : Unit × HwReg X Z M) : 0 ≤ readLin S z u q := by
  unfold readLin
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · split_ifs <;> positivity
  · split_ifs <;> positivity
  · rcases pd_mem (e := splitH' z) (act := actH z) (Flip (splitH' z) (tauH z u) (liftSet S))
      q with h | h <;> simp [h]

open scoped Classical in
/-- The diagonal of the trial costs: `readLin` at the trial reads. -/
noncomputable def dSf : ∀ i : (hwSpec HashOutput HashDomain Mem).Port,
    (hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem → ℝ
  | .inl (.inr (.readH z u)) => fun q ↦
      if u = uRed z ∨ u = uJudge z then 0 else readLin (BadR e.hash G) z u q
  | _ => fun _ ↦ 0

theorem dSf_nonneg (i : (hwSpec HashOutput HashDomain Mem).Port)
    (q : (hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem) :
    0 ≤ dSf e i q := by
  rcases i with (p | c) | c
  · exact le_rfl
  · cases c with
    | readH z u =>
      by_cases hu : u = uRed z ∨ u = uJudge z
      · simp only [dSf, hu, ↓reduceIte, le_refl]
      · simp only [dSf, hu, ↓reduceIte]
        exact readLin_nonneg _ z u q
    | readK _ _ => exact le_rfl
    | readK' _ _ => exact le_rfl
  · exact le_rfl

/-- **The trial costs as completely positive maps**: the diagonal `dSf`. -/
noncomputable def dSΦ (i : (hwSpec HashOutput HashDomain Mem).Port) :
    MatrixMap ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem)
      ((hwSpec HashOutput HashDomain Mem).In i × HwReg HashOutput HashDomain Mem) :=
  MatrixMap.conj (wPot (dSf e i))

theorem isCP_dSΦ (i : (hwSpec HashOutput HashDomain Mem).Port) : (dSΦ e i).IsCP :=
  MatrixMap.isCP_conj _

theorem dS_eq_dSΦ : dS e = fun i σ ↦ ENNReal.ofReal (dSΦ e i σ).trace.re := by
  funext i σ
  rw [dSΦ, re_trace_conj_wPot (dSf_nonneg e i)]
  rcases i with (p | c) | c
  · simp [dS, dSf]
  · cases c with
    | readH z u =>
      by_cases hu : u = uRed z ∨ u = uJudge z
      · simp [dS, dSf, hu]
      · simp only [dS, dSf, hu, ↓reduceIte]
        rfl
    | readK _ _ => simp [dS, dSf]
    | readK' _ _ => simp [dS, dSf]
  · simp [dS, dSf]

end dSCP

/-! ## The cost of a trial read -/

section cost

open Quantum.Qrom HashSig Props
open Tcr (Mem BadR JBad tgt Recordless SameCls IsG GSep recordless_of_sameCls
  tgt_eq_empty_of_recordless tgt_congr_cls card_tgt_le badR_record_iff)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}

/-- The values whose truncation lies in `T` are at most `F` per truncation. -/
theorem card_filter_le_of_trunc {V D : Type} [Fintype V] [DecidableEq D] (tr : V → D) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun v ↦ tr v = o).card ≤ F) (T : Finset D) (P : V → Prop)
    [DecidablePred P] (hP : ∀ v, P v → tr v ∈ T) :
    (Finset.univ.filter P).card ≤ F * T.card := by
  classical
  refine (Finset.card_le_card (t := T.biUnion fun o ↦ Finset.univ.filter fun v ↦ tr v = o)
    fun v hv ↦ ?_).trans (Finset.card_biUnion_le.trans ?_)
  · exact Finset.mem_biUnion.2 ⟨tr v, hP v (Finset.mem_filter.1 hv).2,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  · rw [mul_comm]
    exact Finset.sum_le_card_nsmul _ _ _ fun o _ ↦ hF o

/-- **A new record at `x` of a class without a record keeps the event**, unless its truncation
is that of another cell of the class or of the judge's read at the class. -/
theorem badR_record_new (hs : GSep e.hash G) {x : HashDomain}
    {s : RomReg HashDomain HashOutput Mem} (hrl : Recordless e.hash G s.2.2 x) {v : HashOutput}
    {m' : Mem} (hrec : m'.recs = Function.update s.2.2.recs x (some v))
    (hsl : m'.slot = s.2.2.slot)
    (hT : ∀ y w, SameCls e.hash G y x → y ≠ x → unionH s y = some w →
      e.hash.trunc w ≠ e.hash.trunc v)
    (hJ : ∀ z' w, s.2.2.slot = some (z', w) → SameCls e.hash G z' x →
      e.hash.trunc w ≠ e.hash.trunc v) :
    ((s.1, s.2.1, m') : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
      s ∈ BadR e.hash G := by
  have hout : ∀ y, ¬ SameCls e.hash G y x →
      tgt e.hash G s.2.1 m' y = tgt e.hash G s.2.1 s.2.2 y :=
    fun y hy ↦ tgt_congr_cls (fun x₀ hx₀ ↦ by
      rw [hrec, Function.update_of_ne]
      rintro rfl
      exact hy hx₀.symm) _ _
  have hin' : ∀ y w, SameCls e.hash G y x → w ∈ tgt e.hash G s.2.1 m' y →
      y ≠ x ∧ e.hash.trunc w = e.hash.trunc v := by
    rintro y w hyx ⟨x₀, v₀, hv₀, hne, hc, -, ht⟩
    have hx₀ : x₀ = x := by
      by_contra h
      rw [hrec, Function.update_of_ne h, hrl x₀ (hc.trans hs hyx)] at hv₀
      cases hv₀
    subst hx₀
    rw [hrec, Function.update_self] at hv₀
    cases hv₀
    exact ⟨Ne.symm hne, ht⟩
  have hin : ∀ y w, SameCls e.hash G y x → w ∉ tgt e.hash G s.2.1 s.2.2 y := fun y w hyx ↦ by
    rw [tgt_eq_empty_of_recordless (recordless_of_sameCls hs hrl hyx)]
    exact Set.notMem_empty w
  constructor
  · rintro (⟨y, w, hyw, hw⟩ | ⟨z', w, hsl', hw⟩)
    · change w ∈ tgt e.hash G s.2.1 m' y at hw
      by_cases hyx : SameCls e.hash G y x
      · obtain ⟨hne, ht⟩ := hin' y w hyx hw
        exact absurd ht (hT y w hyx hne hyw)
      · exact Or.inl ⟨y, w, hyw, by rw [← hout y hyx]; exact hw⟩
    · change m'.slot = some (z', w) at hsl'
      change w ∈ tgt e.hash G s.2.1 m' z' at hw
      rw [hsl] at hsl'
      by_cases hzx : SameCls e.hash G z' x
      · exact absurd (hin' z' w hzx hw).2 (hJ z' w hsl' hzx)
      · exact Or.inr ⟨z', w, hsl', by rw [← hout z' hzx]; exact hw⟩
  · rintro (⟨y, w, hyw, hw⟩ | ⟨z', w, hsl', hw⟩)
    · have hyx : ¬ SameCls e.hash G y x := fun h ↦ hin y w h hw
      refine Or.inl ⟨y, w, hyw, ?_⟩
      change w ∈ tgt e.hash G s.2.1 m' y
      rw [hout y hyx]
      exact hw
    · have hzx : ¬ SameCls e.hash G z' x := fun h ↦ hin z' w h hw
      refine Or.inr ⟨z', w, ?_, ?_⟩
      · change m'.slot = _
        rw [hsl]
        exact hsl'
      · change w ∈ tgt e.hash G s.2.1 m' z'
        rw [hout z' hzx]
        exact hw

theorem card_optionElim_le {α β : Type} [DecidableEq β] (o : Option α) (P : α → Prop)
    [DecidablePred P] (f : α → β) :
    (o.elim (∅ : Finset β) fun p ↦ if P p then {f p} else ∅).card ≤ 1 := by
  rcases o with _ | p
  · simp
  · simp only [Option.elim_some]
    split_ifs <;> simp

open scoped Classical in
/-- The cells of the class of `x` other than `x` that are in the database or hardwired. -/
noncomputable def clsCnt (x : HashDomain) (s : RomReg HashDomain HashOutput Mem) : ℕ :=
  (Finset.univ.filter fun y ↦ SameCls e.hash G y x ∧ y ≠ x ∧ unionH s y ≠ none).card

variable (e) in
/-- **The truncations a new record at `x` must avoid**: those of the other cells of its class,
and of the judge's read at the class; at most `clsCnt + 1` of them. -/
theorem exists_truncSet (x : HashDomain) (s : RomReg HashDomain HashOutput Mem) :
    ∃ T : Finset Dig, T.card ≤ clsCnt (e := e) x s + 1 ∧
      (∀ y w, SameCls e.hash G y x → y ≠ x → unionH s y = some w → e.hash.trunc w ∈ T) ∧
      (∀ z' w, s.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T) := by
  classical
  refine ⟨(Finset.univ.filter fun y ↦ SameCls e.hash G y x ∧ y ≠ x ∧ unionH s y ≠ none).image
      (fun y ↦ e.hash.trunc ((unionH s y).getD 0)) ∪
    (s.2.2.slot.elim ∅ fun p ↦ if SameCls e.hash G p.1 x then {e.hash.trunc p.2} else ∅),
    ?_, fun y w hyx hne hy ↦ ?_, fun z' w hsl hzx ↦ ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le.trans ?_) ?_)
    · unfold clsCnt
      exact le_of_eq (congrArg Finset.card (Finset.filter_congr fun _ _ ↦ Iff.rfl))
    · exact card_optionElim_le (α := HashDomain × HashOutput) (β := Dig) _
        (fun p ↦ SameCls e.hash G p.1 x) fun p ↦ e.hash.trunc p.2
  · rw [Finset.mem_union, Finset.mem_image]
    refine Or.inl ⟨y, ?_, by rw [hy]; rfl⟩
    rw [Finset.mem_filter]
    exact ⟨by simp, hyx, hne, by rw [hy]; exact Option.some_ne_none w⟩
  · rw [Finset.mem_union, hsl]
    simp [hzx]

/-- The read of `x` from `s` moves the memory with the answers' policy, and keeps the event,
unless the outcome is in the target of `x`, or records a class without a record with a
truncation in `T`. -/
theorem badR_uSel_or (hs : GSep e.hash G) {x : HashDomain} (s : RomReg HashDomain HashOutput Mem)
    {T : Finset Dig}
    (hT1 : ∀ y w, SameCls e.hash G y x → y ≠ x → unionH s y = some w → e.hash.trunc w ∈ T)
    (hT2 : ∀ z' w, s.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T)
    (v : HashOutput) (hv : ¬ (Recordless e.hash G s.2.2 x ∧ e.hash.trunc v ∈ T)) :
    ((s.1, s.2.1, uSel e x s.2.2 (some v)) : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
      s ∈ BadR e.hash G := by
  classical
  by_cases hrec : IsG e.hash G x ∧ Recordless e.hash G s.2.2 x ∧
      ∃ v', some v = some v' ∧ e.isCode (e.hash.trunc v') = true
  · have hTv : e.hash.trunc v ∉ T := fun h ↦ hv ⟨hrec.2.1, h⟩
    refine badR_record_new hs hrec.2.1 (v := v) ?_ rfl (fun y w hyx hne hy h ↦ ?_)
      fun z' w hsl hzx h ↦ ?_
    · rw [uSel_recs, ite_eq_left hrec]
      rfl
    · exact hTv (h ▸ hT1 y w hyx hne hy)
    · exact hTv (h ▸ hT2 z' w hsl hzx)
  · refine badR_congr_mem (s := s) ?_ rfl
    rw [uSel_recs, ite_eq_right hrec]

/-- The values counted by `rdCnt` and `hFlip` at the empty cell `x`: in the target of `x`, or
recording a class without a record with a truncation in `T`. -/
theorem rd_or_flip_imp (hs : GSep e.hash G) {x : HashDomain}
    (q : Unit × RomReg HashDomain HashOutput Mem) (hw : q.2.2.1.1 x = none)
    (hd : q.2.1.1 x = none) {T : Finset Dig}
    (hT1 : ∀ y w, SameCls e.hash G y x → y ≠ x → unionH q.2 y = some w → e.hash.trunc w ∈ T)
    (hT2 : ∀ z' w, q.2.2.2.slot = some (z', w) → SameCls e.hash G z' x → e.hash.trunc w ∈ T)
    (v : HashOutput) :
    (¬ ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2.1, uSel e x q.2.2.2 (some v)) :
        RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔ q.2 ∈ BadR e.hash G) ∨
      hFlip (BadR e.hash G) x (uSel e x) q v) →
    v ∈ tgt e.hash G q.2.2.1 q.2.2.2 x ∨
      (Recordless e.hash G q.2.2.2 x ∧ e.hash.trunc v ∈ T) := by
  intro h
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnt, hnr⟩ := hcon
  have hrd : ∀ a : Option HashOutput,
      ((((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, uSel e x q.2.2.2 (some v)) :
        RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
        (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
          RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G) := fun a ↦ by
    have hu : ∀ y, y ≠ x →
        unionH (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
          RomReg HashDomain HashOutput Mem) y = unionH q.2 y := fun y hy ↦ by
      change (q.2.2.1.1 y).or (Function.update q.2.1.1 x a y) = (q.2.2.1.1 y).or (q.2.1.1 y)
      rw [Function.update_of_ne hy]
    exact badR_uSel_or hs (((Function.update q.2.1.1 x a, q.2.1.2), q.2.2.1, q.2.2.2) :
        RomReg HashDomain HashOutput Mem)
      (fun y w hyx hne hy ↦ hT1 y w hyx hne ((hu y hne).symm.trans hy)) hT2 v hnr
  have hrec : ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2) :
      RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔ q.2 ∈ BadR e.hash G) :=
    badR_record_iff hw hnt none hd (Or.inl rfl)
  rcases h with h | h | ⟨a, h⟩
  · exact h ((hrd (some v)).trans hrec)
  · exact h hrec
  · exact h (hrd a)

open scoped Classical in
/-- A count of the values counted by `rdCnt` or `hFlip`: `F (clsCnt + 1)` at a class without a
record, `F` at a class with one. -/
theorem card_rd_le (hs : GSep e.hash G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) {x : HashDomain}
    (q : Unit × RomReg HashDomain HashOutput Mem) (hw : q.2.2.1.1 x = none)
    (hd : q.2.1.1 x = none) (P : HashOutput → Prop) {_ : DecidablePred P}
    (hP : ∀ v, P v → ¬ ((((Function.update q.2.1.1 x (some v), q.2.1.2), q.2.2.1,
        uSel e x q.2.2.2 (some v)) : RomReg HashDomain HashOutput Mem) ∈ BadR e.hash G ↔
          q.2 ∈ BadR e.hash G) ∨ hFlip (BadR e.hash G) x (uSel e x) q v) :
    ((Finset.univ.filter P).card : ℝ) ≤
      if Recordless e.hash G q.2.2.2 x then F * (clsCnt (e := e) x q.2 + 1) else F := by
  classical
  obtain ⟨T, hTc, hT1, hT2⟩ := exists_truncSet e x q.2
  have himp := fun v hv ↦ rd_or_flip_imp hs q hw hd hT1 hT2 v (hP v hv)
  split_ifs with hr
  · have h := card_filter_le_of_trunc e.hash.trunc hF T P fun v hv ↦ ((himp v hv).resolve_left
      (by rw [tgt_eq_empty_of_recordless hr]; exact Set.notMem_empty v)).2
    exact_mod_cast h.trans (Nat.mul_le_mul_left F hTc)
  · have h := (Finset.card_le_card (Finset.monotone_filter_right (s := Finset.univ)
      (p := P) (q := fun v ↦ v ∈ tgt e.hash G q.2.2.1 q.2.2.2 x) fun v _ hv ↦
        ((himp v hv).resolve_right fun h ↦ hr h.1))).trans (card_tgt_le hF _ _ _)
    exact_mod_cast h

open scoped Classical in
/-- **The cost of a trial read**, linearized: `2 + 2/N` on a recorded or hardwired cell; on an
empty cell `(2F + 2)/N`, plus `2F/N` per other recorded cell of its class if the class has no
record. -/
theorem readLin_uSel_le (hs : GSep e.hash G) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (x : HashDomain)
    (q : Unit × RomReg HashDomain HashOutput Mem) :
    readLin (BadR e.hash G) x (uSel e x) q ≤
      (2 + 2 / (Fintype.card HashOutput : ℝ)) *
          (if q.2.2.1.1 x = none ∧ q.2.1.1 x = none then 0 else 1) +
        ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * clsCnt (e := e) x q.2 else 0) +
          2 * F + 2) / Fintype.card HashOutput := by
  have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.2 Fintype.card_pos
  have hpd := pd_flip_le_readH (BadR e.hash G) x (uSel e x) q
  have hR : 0 ≤ (if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * clsCnt (e := e) x q.2
      else 0) := by split_ifs <;> positivity
  have hcls : ∀ o, (if hCls (BadR e.hash G) (uSel e x) o q then (1 : ℝ) else 0) ≤ 1 :=
    fun o ↦ by split_ifs <;> norm_num
  have h2N : 0 ≤ 2 / (Fintype.card HashOutput : ℝ) := by positivity
  unfold readLin
  by_cases hw : q.2.2.1.1 x = none
  · by_cases hd : q.2.1.1 x = none
    · rw [ite_eq_left hw, ite_eq_left hd, ite_eq_left ⟨hw, hd⟩, ite_eq_left ⟨hw, hd⟩,
        mul_zero, zero_add]
      rw [ite_eq_right fun h ↦ h.2 hd] at hpd
      have h1 : (rdCnt (BadR e.hash G) x (uSel e x) q : ℝ) ≤ _ :=
        card_rd_le hs hF q hw hd _ fun v hv ↦ Or.inl hv
      have h2 : ((Finset.univ.filter (hFlip (BadR e.hash G) x (uSel e x) q)).card : ℝ) ≤ _ :=
        card_rd_le hs hF q hw hd _ fun v hv ↦ Or.inr hv
      have key : (rdCnt (BadR e.hash G) x (uSel e x) q : ℝ) +
          (Finset.univ.filter (hFlip (BadR e.hash G) x (uSel e x) q)).card ≤
          (if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * clsCnt (e := e) x q.2 else 0) +
            2 * F := by
        split_ifs at h1 h2 ⊢
        · push_cast at h1 h2
          nlinarith
        · linarith
      refine le_trans (add_le_add le_rfl hpd) ?_
      rw [add_zero, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [key]) hN.le
    · have hn : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x = none) := fun h ↦ hd h.2
      rw [ite_eq_left hw, ite_eq_right hd, ite_eq_right hn, ite_eq_right hn, mul_one, add_zero]
      rw [ite_eq_left (show q.2.2.1.1 x = none ∧ q.2.1.1 x ≠ none from ⟨hw, hd⟩)] at hpd
      have h3 := hcls (q.2.1.1 x)
      have h4 : 0 ≤ ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * clsCnt (e := e) x q.2
          else 0) + 2 * F + 2) / Fintype.card HashOutput := by positivity
      linarith
  · have hn : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x = none) := fun h ↦ hw h.1
    have hn' : ¬ (q.2.2.1.1 x = none ∧ q.2.1.1 x ≠ none) := fun h ↦ hw h.1
    rw [ite_eq_right hw, ite_eq_right hn, ite_eq_right hn, mul_one, add_zero]
    rw [ite_eq_right hn'] at hpd
    have h3 := hcls (q.2.2.1.1 x)
    have h4 : 0 ≤ ((if Recordless e.hash G q.2.2.2 x then 2 * (F : ℝ) * clsCnt (e := e) x q.2
        else 0) + 2 * F + 2) / Fintype.card HashOutput := by positivity
    nlinarith

end cost

/-! ## The cost of an answer -/

section final

open Quantum.Qrom HashSig Props OracleComp OracleSpec
open Quantum.Xmss.Hybrid (runtime2)
open Tcr (Mem BadR Recordless SameCls IsG GSep GCell gCell_unique recordless_of_sameCls)

variable {Par Tw Msg Salt Dig : Type} {e : SaltEnc Par Tw Msg Salt Dig}

/-- The cell of an encoding input names the input. -/
theorem cell_inj (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen) {P : Par} {t : Tw} {d d' : Msg × Salt}
    (h : cell e P t d = cell e P t d') : d = d' :=
  hinj P t (encodeInput_injective (encodeInput_cell hlen P t d)
    (by rw [h]; exact encodeInput_cell hlen P t d'))

variable (e) in
/-- The trial cells of a grind from the base `r0`. -/
noncomputable def trialSet (P : Par) (t : Tw) (M : Msg) (r0 : Salt) : Finset HashDomain :=
  (Finset.range e.limit).image fun c ↦ cell e P t (M, e.shift r0 c)

theorem cell_mem_trialSet {P : Par} {t : Tw} {M : Msg} {r0 : Salt} {c : ℕ} (hc : c < e.limit) :
    cell e P t (M, e.shift r0 c) ∈ trialSet e P t M r0 :=
  Finset.mem_image.2 ⟨c, Finset.mem_range.2 hc, rfl⟩

variable (e) in
open scoped Classical in
/-- The cells of the class of `(P, t)` off the trial cells, in the database or hardwired. -/
noncomputable def nOut (P : Par) (t : Tw) (M : Msg) (r0 : Salt)
    (s : HwReg HashOutput HashDomain Mem) : ℕ :=
  (Finset.univ.filter fun y ↦
    GCell e.hash G y P t ∧ y ∉ trialSet e P t M r0 ∧ unionH s y ≠ none).card

variable (e) in
open scoped Classical in
/-- **The weight of trial `c`** of a grind from the base `r0`. -/
noncomputable def fTrial (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  (2 + 2 / (Fintype.card HashOutput : ℝ)) * (if s.2.1.1 (cell e P t (M, e.shift r0 c)) = none ∧
      s.1.1 (cell e P t (M, e.shift r0 c)) = none then 0 else 1) +
    ((if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c)) then
      2 * (F : ℝ) * (nOut e P t M r0 s + e.limit) else 0) + 2 * F + 2) /
        Fintype.card HashOutput

open scoped Classical in
theorem fTrial_nonneg (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ fTrial e F P t M r0 c s := by
  unfold fTrial
  have : 0 ≤ (if Recordless e.hash G s.2.2 (cell e P t (M, e.shift r0 c)) then
      2 * (F : ℝ) * (nOut e P t M r0 s + e.limit) else 0) := by split_ifs <;> positivity
  split_ifs <;> positivity

/-- A filter whose elements satisfy `Q` or lie in `T` is at most the `Q`-filter and `T`. -/
theorem card_filter_le_union {α : Type} [Fintype α] [DecidableEq α] (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (T : Finset α) (h : ∀ y, P y → Q y ∨ y ∈ T) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card + T.card := by
  refine (Finset.card_le_card fun y hy ↦ ?_).trans (Finset.card_union_le _ T)
  rcases h y (Finset.mem_filter.1 hy).2 with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)
  · exact Finset.mem_union_right _ h'

open scoped Classical in
/-- The other recorded cells of the class of a trial cell: off the trial cells, or trial cells. -/
theorem clsCnt_le_nOut (hs : GSep e.hash G) (hlen : e.hash.LengthLe maxLen) {P : Par} {t : Tw}
    {M : Msg} {r0 : Salt} {c : ℕ} (s : HwReg HashOutput HashDomain Mem) :
    (clsCnt (e := e) (cell e P t (M, e.shift r0 c)) s : ℝ) ≤ nOut e P t M r0 s + e.limit := by
  have h : clsCnt (e := e) (cell e P t (M, e.shift r0 c)) s ≤ nOut e P t M r0 s + e.limit := by
    unfold clsCnt nOut
    refine (card_filter_le_union _ _ (trialSet e P t M r0) fun y hy ↦ ?_).trans
      (add_le_add le_rfl (Finset.card_image_le.trans (Finset.card_range _).le))
    obtain ⟨hyx, -, hu⟩ := hy
    by_cases ht : y ∈ trialSet e P t M r0
    · exact Or.inr ht
    · refine Or.inl ⟨?_, ht, hu⟩
      obtain ⟨P', t', h1, h2⟩ := hyx
      obtain ⟨rfl, rfl⟩ := gCell_unique hs (gCell_cell hlen P t _) h2
      exact h1
  exact_mod_cast h

open scoped Classical in
/-- The read of a trial cell costs at most the trial's weight. -/
theorem dSΦ_trial_le (hs : GSep e.hash G) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F) (P : Par) (t : Tw)
    (M : Msg) (r0 : Salt) (c : ℕ)
    (σ : Matrix ((hwSpec HashOutput HashDomain Mem).In
        (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
          (upd e .answer (cell e P t (M, e.shift r0 c)))))) × HwReg HashOutput HashDomain Mem)
        ((hwSpec HashOutput HashDomain Mem).In
          (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
            (upd e .answer (cell e P t (M, e.shift r0 c)))))) ×
              HwReg HashOutput HashDomain Mem) ℂ) (hσ : σ.PosSemidef) :
    ENNReal.ofReal (dSΦ e (.inl (.inr (.readH (cell e P t (M, e.shift r0 c))
        (upd e .answer (cell e P t (M, e.shift r0 c)))))) σ).trace.re ≤
      ENNReal.ofReal (∑ q, fTrial e F P t M r0 c q.2 * (σ q q).re) := by
  rw [dSΦ, re_trace_conj_wPot (dSf_nonneg e _)]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ mul_le_mul_of_nonneg_right ?_
    (Complex.nonneg_iff.1 hσ.diag_nonneg).1)
  simp only [dSf]
  by_cases hu : upd e .answer (cell e P t (M, e.shift r0 c)) =
      Tcr.uRed (cell e P t (M, e.shift r0 c)) ∨
      upd e .answer (cell e P t (M, e.shift r0 c)) = Tcr.uJudge (cell e P t (M, e.shift r0 c))
  · rw [ite_eq_left hu]
    exact fTrial_nonneg F P t M r0 c q.2
  · rw [ite_eq_right hu]
    refine (readLin_uSel_le hs hF (cell e P t (M, e.shift r0 c)) q).trans
      (add_le_add le_rfl ?_)
    have hN : (0 : ℝ) ≤ Fintype.card HashOutput := Nat.cast_nonneg _
    refine div_le_div_of_nonneg_right (add_le_add (add_le_add ?_ le_rfl) le_rfl) hN
    split_ifs
    · exact mul_le_mul_of_nonneg_left (clsCnt_le_nOut hs hlen q.2) (by positivity)
    · exact le_rfl

open scoped Classical in
/-- The weights of the later trials ignore a trial's cell and its memory move when its outcome is
not a codeword. -/
theorem fTrial_move (hinj : ∀ P t, (e.hash.layout () P t).Injective)
    (hlen : e.hash.LengthLe maxLen)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    (F : ℕ) (P : Par) (t : Tw) (M : Msg) (r0 : Salt) {c c' : ℕ} (hcc : c < c')
    (hc' : c' < e.limit) (s : HwReg HashOutput HashDomain Mem) (a o : Option HashOutput)
    (ho : e.isCode (e.hash.trunc (o.getD 0)) = false) :
    fTrial e F P t M r0 c' ((Function.update s.1.1 (cell e P t (M, e.shift r0 c)) a, s.1.2),
      s.2.1, upd e .answer (cell e P t (M, e.shift r0 c)) s.2.2 o) = fTrial e F P t M r0 c' s := by
  set x := cell e P t (M, e.shift r0 c)
  have hxx : cell e P t (M, e.shift r0 c') ≠ x := fun h ↦ by
    have := congrArg Prod.snd (cell_inj hinj hlen h)
    exact absurd (hdist r0 c' c hc' (by omega) this) (by omega)
  have hrecs : (uSel e x s.2.2 o).recs = s.2.2.recs := by
    rw [uSel_recs, ite_eq_right]
    rintro ⟨-, -, v, rfl, hv⟩
    simp only [Option.getD_some] at ho
    rw [ho] at hv
    exact Bool.false_ne_true hv
  have hrl : ∀ z, Recordless e.hash G (uSel e x s.2.2 o) z ↔ Recordless e.hash G s.2.2 z :=
    fun z ↦ by
      unfold Tcr.Recordless
      rw [hrecs]
  have hn : nOut e P t M r0 ((Function.update s.1.1 x a, s.1.2), s.2.1, uSel e x s.2.2 o) =
      nOut e P t M r0 s := by
    unfold nOut
    refine congrArg Finset.card (Finset.filter_congr fun y _ ↦ and_congr_right fun _ ↦
      and_congr_right fun hy ↦ ?_)
    have hyx : y ≠ x := fun h ↦ hy (h ▸ cell_mem_trialSet (by omega))
    change (s.2.1.1 y).or (Function.update s.1.1 x a y) ≠ none ↔ (s.2.1.1 y).or (s.1.1 y) ≠ none
    rw [Function.update_of_ne hyx]
  unfold fTrial
  change (2 + 2 / (Fintype.card HashOutput : ℝ)) * (if s.2.1.1 (cell e P t (M, e.shift r0 c')) =
      none ∧ Function.update s.1.1 x a (cell e P t (M, e.shift r0 c')) = none then 0 else 1) +
    ((if Recordless e.hash G (uSel e x s.2.2 o) (cell e P t (M, e.shift r0 c')) then
      2 * (F : ℝ) * (nOut e P t M r0 ((Function.update s.1.1 x a, s.1.2), s.2.1,
        uSel e x s.2.2 o) + e.limit) else 0) + 2 * F + 2) / Fintype.card HashOutput = _
  rw [Function.update_of_ne hxx, hn]
  simp only [hrl]

/-- Sequencing classical algorithms run from inside an experiment. -/
theorem toQuantumAt_bind' {spec : QuantumOracleSpec.{0, 0}} {B : QReg} {α β : Type}
    (oa : OracleComp romWorld.Oracles α) (g : α → OracleComp romWorld.Oracles β)
    (qi : QueryImpl romWorld.Oracles (QComp spec B B)) :
    (oa >>= g).toQuantumAt qi = (oa.toQuantumAt qi).bind fun a ↦ (g a).toQuantumAt qi := by
  simp only [OracleComp.toQuantumAt, simulateQ_bind]
  rfl

open scoped Classical in
/-- **An answer, as a step bound**: the grind from every base, averaged over the base. -/
theorem step₂_answer [SampleableType Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    [Fintype Salt] (m₀ : Mem) (B : QReg) (P : Par) (q : Tw × Msg) :
    Step₂ (runtime2 HashOutput HashDomain m₀) .instruments
      (fun i σ ↦ ENNReal.ofReal (dSΦ e i σ).trace.re)
      (readProgOf (upd e) ((sample romWorld Salt >>= fun r0 ↦
        e.grind romWorld P q.1 q.2 r0 0 e.limit).toQuantumAt (mixImpl .answer B)))
      (fun _ ↦ wPot fun _ ↦ 0)
      (wPot fun s ↦ ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal *
        gsum (fTrial e F P q.1 q.2 r0) 0 e.limit s) := by
  rw [toQuantumAt_bind', sample, toQuantumAt_liftComp, readProgOf_bind₂]
  exact step₂_bind (isCP_dSΦ e) _ _ _
    (step₂_sampler m₀ (isCP_dSΦ e) (upd e) B ($ᵗ Salt)
      (fun r0 ↦ gsum (fTrial e F P q.1 q.2 r0) 0 e.limit)
      fun r0 s ↦ gsum_nonneg (fTrial_nonneg F P q.1 q.2 r0) _ _ _)
    fun r0 ↦ step₂_grind m₀ (isCP_dSΦ e) hlen B P q.1 q.2 r0 (fTrial e F P q.1 q.2 r0)
      (fTrial_nonneg F P q.1 q.2 r0) e.limit
      (fun c _ σ hσ ↦ dSΦ_trial_le hs hlen hF P q.1 q.2 r0 c σ hσ)
      (fun c c' hcc hc' s a o ho ↦ fTrial_move hinj hlen hdist F P q.1 q.2 r0 hcc hc' s a o ho)
      e.limit 0 (by omega)

/-- A filter is monotone in its predicate. -/
theorem card_filter_mono' {α : Type} [Fintype α] (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ y, P y → Q y) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card :=
  Finset.card_le_card (Finset.monotone_filter_right _ fun y _ ↦ h y)

variable (e) in
open scoped Classical in
/-- **The cost of an answer to `(t, M)` at `P`**, on the database of the state `s`: per trial,
`(2 + 2/N)` times the share of the salts whose cell is recorded, `2F/N` per recorded cell of the
class (plus the trials) if the class has no record, and `(2F + 2)/N`. -/
noncomputable def ansCost [Fintype Salt] (F : ℕ) (P : Par) (q : Tw × Msg)
    (s : HwReg HashOutput HashDomain Mem) : ℝ :=
  e.limit * ((2 + 2 / (Fintype.card HashOutput : ℝ)) *
      (Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card /
        Fintype.card Salt +
    ((if ∀ d, Recordless e.hash G s.2.2 (cell e P q.1 d) then
      2 * (F : ℝ) * ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
        e.limit) else 0) + 2 * F + 2) / Fintype.card HashOutput)

theorem ansCost_nonneg [Fintype Salt] (F : ℕ) (P : Par) (q : Tw × Msg)
    (s : HwReg HashOutput HashDomain Mem) : 0 ≤ ansCost e F P q s := by
  classical
  unfold ansCost
  have : 0 ≤ (if ∀ d, Recordless e.hash G s.2.2 (cell e P q.1 d) then
      2 * (F : ℝ) * ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card +
        e.limit) else 0) := by split_ifs <;> positivity
  positivity

open scoped Classical in
/-- **A trial's weight on a state without hardwired cells**: the recorded indicator of its cell,
and the class's weight, read on the database. -/
theorem fTrial_le_hw (hs : GSep e.hash G) (hlen : e.hash.LengthLe maxLen) (F : ℕ) (P : Par)
    (t : Tw) (M : Msg) (r0 : Salt) (c : ℕ) (s : HwReg HashOutput HashDomain Mem)
    (hW : s.2.1 = hwEmpty HashOutput HashDomain) :
    fTrial e F P t M r0 c s ≤ (2 + 2 / (Fintype.card HashOutput : ℝ)) *
        (if s.1.1 (cell e P t (M, e.shift r0 c)) ≠ none then 1 else 0) +
      ((if ∀ d, Recordless e.hash G s.2.2 (cell e P t d) then 2 * (F : ℝ) *
        ((Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card + e.limit)
          else 0) + 2 * F + 2) / Fintype.card HashOutput := by
  have hw : ∀ y, s.2.1.1 y = none := fun y ↦ by
    rw [hW]
    exact hwEmpty_fst_apply y
  unfold fTrial
  refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (div_le_div_of_nonneg_right (add_le_add (add_le_add ?_ le_rfl) le_rfl) (Nat.cast_nonneg _))
  · rw [hw]
    split_ifs <;> simp_all
  · split_ifs with h1 h2 h2
    · have hn : nOut e P t M r0 s ≤
          (Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card := by
        unfold nOut
        refine card_filter_mono' _ _ fun y hy ↦ ⟨hy.1, ?_⟩
        have h := hy.2.2
        change (s.2.1.1 y).or (s.1.1 y) ≠ none at h
        rwa [hw, Option.none_or] at h
      have hn' : (nOut e P t M r0 s : ℝ) ≤
          (Finset.univ.filter fun y ↦ GCell e.hash G y P t ∧ s.1.1 y ≠ none).card := by
        exact_mod_cast hn
      exact mul_le_mul_of_nonneg_left (add_le_add hn' le_rfl) (by positivity)
    · exact absurd (fun d ↦ recordless_of_sameCls hs h1 (sameCls_cell hlen P t d _)) h2
    · positivity
    · exact le_rfl

/-- **Averaging over the base**: a weight below `A · ind + K` per trial, the indicators summing
over the bases to at most `H` per trial, averages to at most `L (A H / |ι| + K)`. -/
theorem avg_sum_le {ι : Type} [Fintype ι] [Nonempty ι] (L : ℕ) (f ind : ι → ℕ → ℝ)
    (A K H : ℝ) (hA : 0 ≤ A) (hf : ∀ i c, f i c ≤ A * ind i c + K)
    (hind : ∀ c, ∑ i, ind i c ≤ H) :
    ∑ i, (Fintype.card ι : ℝ)⁻¹ * ∑ c ∈ Finset.range L, f i c ≤
      L * (A * H / Fintype.card ι + K) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ i, ∑ c ∈ Finset.range L, (A * ind i c + K) =
      A * ∑ c ∈ Finset.range L, ∑ i, ind i c + Fintype.card ι * (L * K) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Finset.card_range, nsmul_eq_mul]
  have hH : ∑ c ∈ Finset.range L, ∑ i, ind i c ≤ L * H := by
    refine (Finset.sum_le_sum fun c _ ↦ hind c).trans ?_
    simp
  calc ∑ i, (Fintype.card ι : ℝ)⁻¹ * ∑ c ∈ Finset.range L, f i c
      ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * ∑ c ∈ Finset.range L, (A * ind i c + K) :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun c _ ↦ hf i c) (inv_nonneg.2 hN.le)
    _ = (Fintype.card ι : ℝ)⁻¹ * (A * ∑ c ∈ Finset.range L, ∑ i, ind i c) + L * K := by
        rw [← Finset.mul_sum, hsum, mul_add, inv_mul_cancel_left₀ hN.ne']
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * (A * (L * H)) + L * K :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hA)
          (inv_nonneg.2 hN.le)) le_rfl
    _ = L * (A * H / Fintype.card ι + K) := by
        field_simp

open scoped Classical in
/-- **The averaged weight of the trials is the answer's cost** on a state without hardwired
cells. -/
theorem avg_fTrial_le [SampleableType Salt] [Fintype Salt] (hs : GSep e.hash G)
    (hlen : e.hash.LengthLe maxLen) (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (F : ℕ) (P : Par) (q : Tw × Msg) (s : HwReg HashOutput HashDomain Mem)
    (hW : s.2.1 = hwEmpty HashOutput HashDomain) :
    ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal * gsum (fTrial e F P q.1 q.2 r0) 0 e.limit s ≤
      ansCost e F P q s := by
  have hPr : ∀ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal = (Fintype.card Salt : ℝ)⁻¹ :=
    fun r0 ↦ by
      rw [SampleableType.prEvent_uniformSample_eq_singleton, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
  simp only [hPr, gsum_eq_sum, zero_add]
  refine (avg_sum_le e.limit (fun r0 c ↦ fTrial e F P q.1 q.2 r0 c s)
    (fun r0 c ↦ if s.1.1 (cell e P q.1 (q.2, e.shift r0 c)) ≠ none then 1 else 0)
    (2 + 2 / (Fintype.card HashOutput : ℝ))
    (((if ∀ d, Recordless e.hash G s.2.2 (cell e P q.1 d) then 2 * (F : ℝ) *
      ((Finset.univ.filter fun y ↦ GCell e.hash G y P q.1 ∧ s.1.1 y ≠ none).card + e.limit)
        else 0) + 2 * F + 2) / Fintype.card HashOutput)
    ((Finset.univ.filter fun r : Salt ↦ s.1.1 (cell e P q.1 (q.2, r)) ≠ none).card)
    (by positivity) (fun r0 c ↦ fTrial_le_hw hs hlen F P q.1 q.2 r0 c s hW)
    fun c ↦ ?_).trans (le_of_eq ?_)
  · rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_card_of_injOn (fun r0 ↦ e.shift r0 c)
      (fun r0 hr0 ↦ by simpa using hr0)
      (hbase c).injOn
  · unfold ansCost
    rfl

open scoped Classical in
/-- **The cost of an answer** (`AnsBound`): from a positive semidefinite state without hardwired
cells, the trial reads of an answer to `(t, M)` at `P` add at most the weight of `ansCost`,
averaged over the base. -/
theorem totalWeight_answer_le [SampleableType Salt] [Fintype Salt] (hs : GSep e.hash G)
    (hinj : ∀ P t, (e.hash.layout () P t).Injective) (hlen : e.hash.LengthLe maxLen) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ e.hash.trunc y = o).card ≤ F)
    (hbase : ∀ c, Function.Injective fun r0 ↦ e.shift r0 c)
    (hdist : ∀ r0 c c', c < e.limit → c' < e.limit → e.shift r0 c = e.shift r0 c' → c = c')
    [SampleableType Par] (m₀ : Mem) (P : Par) (q : Tw × Msg) (B : QReg)
    (ρ : Matrix (B × RomReg HashDomain HashOutput Mem) (B × RomReg HashDomain HashOutput Mem) ℂ)
    (hρ : ρ.PosSemidef)
    (hW : QuerySupportedOn (fun x ↦ x.2) {s | s.2.1 = hwEmpty HashOutput HashDomain} ρ) :
    (runtime2 HashOutput HashDomain m₀).totalWeight .instruments (dS e)
        (readProgOf (upd e) (((encTcrSalt romWorld e).answer P q).toQuantumAt
          (mixImpl .answer B))) ρ ≤
      ENNReal.ofReal (∑ s, ansCost e F P q s.2 * (ρ s s).re) := by
  rw [dS_eq_dSΦ]
  have h := step₂_answer hs hinj hlen hF hdist m₀ B P q ρ hρ
  refine (le_self_add.trans h).trans ?_
  have hV : ∀ s : HwReg HashOutput HashDomain Mem, 0 ≤ ∑ r0, (Pr{let z ← $ᵗ Salt}[z = r0]).toReal *
      gsum (fTrial e F P q.1 q.2 r0) 0 e.limit s := fun s ↦ Finset.sum_nonneg fun r0 _ ↦
    mul_nonneg ENNReal.toReal_nonneg (gsum_nonneg (fTrial_nonneg F P q.1 q.2 r0) _ _ _)
  rw [potential_wPot hV]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun s _ ↦ ?_)
  by_cases h0 : ρ s s = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (avg_fTrial_le hs hlen hbase F P q s.2 (hW s s h0).1)
      (Complex.nonneg_iff.1 hρ.diag_nonneg).1

end final

end Quantum.StdModel.Qrom.EncSalt

end
