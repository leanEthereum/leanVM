module

public import Quantum.Sponge.Oracle.Hardwired.ReadCost
public import Quantum.Xmss.Assembly.ProgView
public import VCVio.Quantum.Comp.HybridMeasure

@[expose] public section

/-!
# The event bound with the verification's reads graded like sponge calls

Security's event bound (`ewR_le`) prices every classical call linearly, so each verification read
(it reads the adversary's own forgery path) may cost up to `1`. ReadCost's square-root form
(`potential_readKeep_le_sqrt`) prices a read that keeps the memory, for an event up-closed in the
read cell and a state with no decompressed `⊥` there, like a sponge call:
`∑ w' ≤ (√w + √keepE)² + keepE + recW`. This file grades the verification's reads that way.

* **Programs whose calls are all graded** (`rpow_inv_two_tsum_potential_run_le_sqrtCalls`,
  `rpow_inv_two_eventWeight_le_sqrtCalls`): if every call presented an operator satisfying `P`
  (`ForallQueries`) has `∑ w' ≤ (√w + √(η tr σ))² + d σ`, a program of at most `n` calls ends with
  `√w ≤ n √(η tr ρ) + √(w ρ + ∑ d)` (Mixed's quantum case with an additive term, the step
  `(√b + √c)² + δ ≤ …`, `rpow_inv_two_add_le_of_le_sq`).
* **The read costs from S4's fresh bound** (`keepE_le_of_freshBound`, `recW_le`,
  `upCell_of_upClosed`): on states of database grade at most `N`, `keepE ≤ ε tr σ` for the fresh
  bound `ε` of the event below `N + 1` entries (the flipping values over the value count:
  `F/|X|` for `h`, capacity scale for `k`, `k'`), and `recW ≤ (2/|X| + 2/|Z|) tr σ`. Hence a read
  of `runtimeR` that keeps the memory costs `(√w + √(ε tr σ))² + (ε + 2/|X| + 2/|Z|) tr σ`
  (`tsum_potential_readKeep_runtimeR_le`).
* **The invariants at the calls**: no decompressed `⊥` (`forallQueries_noBot`, EndReads'
  `decR_step_noBot` transported by `ForallQueries.of_simulation`), the database grade and the reads
  that keep the memory (CostRun's `forallQueries_of_charge_step` with the zero-budget charge
  `nonKeep`; the verification's reads all keep the memory, `chg_verifyT_nonKeep`, and are at most
  `3 verifyBlocks`, `chg_verifyT_one`). `rpow_inv_two_eventWeight_keepReads_le` is the bound for a
  program of reads that keep the memory on `runtimeR`.
* **The canonical game** (`ewR_le_sqrt`): `gameR A L` is the challenge prefix, then the
  verification (`gameR_eq`, `eventWeight_bind₂`). The prefix keeps Security's linear prices
  (`eventWeight_runtimeR_le` with CostLift's `dRof`, `dPof`; record ports free), the verification's
  `3 verifyBlocks` reads are graded:
  `ewR (gameR A) L ≤ (advTerm q + verTerm q + √(twP A L + verLin q))²` on `PermGood` tables,
  with `verTerm q = 3 verifyBlocks √(verEps q)` and
  `verLin q = 3 verifyBlocks (verEps q + 2/|X| + 2/|Z|)`. The prefix's costs are among the game's
  (`totalWeight_le_bind₂`, `twP_le_twR`), so the bound holds with Security's `twR`
  (`ewR_le_sqrt_twR`).
* **Keccak sizes** (`verEps_le`, `verTerm_le`, `verLin_le`): for `q ≤ 2^64`, `verEps q ≤ 2^-128`
  (the `h` fraction `2^960 / 2^1088`; the capacity terms `3 · 18 (T+1)³ / 2^512` with `T < 2^68`
  are below `2^-174`), so `verTerm q ≤ 1194 · 2^-64` and `verLin q ≤ 3582 · 2^-128`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w u₁ v₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## A square-root step with an additive cost -/

/-- If `a ≤ (√b + √c)² + δ`, then `√(a + C) ≤ √c + √(b + (δ + C))`. -/
theorem rpow_inv_two_add_le_of_le_sq {a b c δ C : ℝ≥0∞}
    (h : a ≤ (b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) ^ 2 + δ) :
    (a + C) ^ (2⁻¹ : ℝ) ≤ c ^ (2⁻¹ : ℝ) + (b + (δ + C)) ^ (2⁻¹ : ℝ) := by
  have h' := rpow_inv_two_add_le_of_le (a := (b ^ (2⁻¹ : ℝ) + c ^ (2⁻¹ : ℝ)) ^ 2) (b := b)
    (c := c) (C := δ + C) (pow_two_rpow_inv_two _).le
  refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) h'
  rw [← add_assoc]
  exact add_le_add h le_rfl

/-! ## Programs whose calls all cost like sponge calls -/

section sqrtRun

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} (Q : Matrix R.D R.D ℂ)
  (P : ∀ (i : spec.Port) (E : QReg),
    Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ → Prop)
  (η : ℝ≥0∞) (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)

/-- **Every call costs like a sponge call, by induction on the program.** If every call presented
an operator `τ` satisfying `P` raises the event weight of its input `σ` (`τ` with the rest traced
out) to at most `(√w + √(η tr σ))² + d σ`, a program of at most `n` calls whose calls all satisfy
`P` ends with `√w ≤ ∑' j, √(e j · tr ρ) + √(w ρ + ∑ d)`, for every `e` dominating `η` below `n`. -/
theorem rpow_inv_two_tsum_potential_run_le_sqrtCalls
    (hη : ∀ i (E : QReg) (τ : Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ),
      P i E τ →
      τ.PosSemidef →
        ∑' r, potential Q ((R.step i).branch r (MatrixMap.traceRight (spec.In i × R.D) E τ)) ≤
          (potential Q (MatrixMap.traceRight (spec.In i × R.D) E τ) ^ (2⁻¹ : ℝ) +
            (η * ENNReal.ofReal (MatrixMap.traceRight (spec.In i × R.D) E τ).trace.re) ^
              (2⁻¹ : ℝ)) ^ 2 + d i (MatrixMap.traceRight (spec.In i × R.D) E τ))
    {A : QReg} (x : QuantumComp L spec Ω A) (n : ℕ) (e : ℕ → ℝ≥0∞) (he : ∀ j < n, η ≤ e j)
    (hx : IFreeM.IsChargeBound x (portCharge fun _ ↦ 1) n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hP : R.ForallQueries I P x ρ) :
    (∑' p, potential Q ((R.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      ∑' j, (e j * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n e with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Ω u) fun p hp ↦ by
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
    rw [isChargeBound_portCharge_primBind_iff] at hx
    refine (rpow_inv_two_tsum_le_of_le_add_tsum
      (L := fun b ↦ ∑' p, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
      (t := fun b ↦ potential Q (((I o).frame R.D).branch b ρ) +
        R.totalWeight I d (k b) (((I o).frame R.D).branch b ρ))
      (m := fun j b ↦ e j * ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re)
      fun b ↦ (ih b n e he (hx b) (hρb b) (hP b)).trans_eq (add_comm _ _)).trans ?_
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
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    have hn : 1 ≤ n := hx.1
    have hpot : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R Q i E ℓ r ρ
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    rw [totalWeight_queryBind]
    have hk := fun r ↦ ih r (n - 1) (fun j ↦ e (j + 1)) (fun j hj ↦ he (j + 1) (by omega))
      (hx.2 r) (hρr r) (hP.2 r)
    refine (rpow_inv_two_tsum_le_of_le_add_tsum
      (L := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
        ((R.queryStep i E ℓ).branch r ρ)))
      (t := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
        R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
      (m := fun j r ↦ e (j + 1) * ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
      fun r ↦ (hk r).trans_eq (add_comm _ _)).trans ?_
    have hq0 := hη i E _ hP.1
      ((SubInstrument.relabel (queryEquivIn ℓ R.D)).posSemidef_branch_apply () hρ)
    change ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) ≤
      (potential Q (callInput ℓ R.D ρ) ^ (2⁻¹ : ℝ) +
        (η * ENNReal.ofReal (callInput ℓ R.D ρ).trace.re) ^ (2⁻¹ : ℝ)) ^ 2 +
          d i (callInput ℓ R.D ρ) at hq0
    rw [potential_callInput, trace_callInput, ← hpot] at hq0
    have hη0 : η ≤ e 0 := he 0 (by omega)
    have hq0' : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) ≤
        (potential Q ρ ^ (2⁻¹ : ℝ) + (e 0 * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 +
          d i (callInput ℓ R.D ρ) :=
      hq0.trans (by gcongr)
    rw [ENNReal.tsum_add]
    refine (add_le_add (rpow_inv_two_add_le_of_le_sq hq0') le_rfl).trans ?_
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    calc _ ≤ (e 0 * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
          (potential Q ρ + (d i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I d (k r)
            ((R.queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) +
          ∑' j, (e (j + 1) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
          gcongr with j
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = _ := by ring

/-- **Every call costs like a sponge call**: from a positive semidefinite `ρ`, a program of at
most `n` calls, all satisfying `P`, ends with event weight `√w ≤ ∑' j, √(e j · tr ρ) + √(w ρ + ∑ d)`
for every `e` dominating `η` below `n`. -/
theorem rpow_inv_two_eventWeight_le_sqrtCalls
    (hη : ∀ i (E : QReg) (τ : Matrix ((spec.In i × R.D) × E) ((spec.In i × R.D) × E) ℂ),
      P i E τ →
      τ.PosSemidef →
        ∑' r, potential Q ((R.step i).branch r (MatrixMap.traceRight (spec.In i × R.D) E τ)) ≤
          (potential Q (MatrixMap.traceRight (spec.In i × R.D) E τ) ^ (2⁻¹ : ℝ) +
            (η * ENNReal.ofReal (MatrixMap.traceRight (spec.In i × R.D) E τ).trace.re) ^
              (2⁻¹ : ℝ)) ^ 2 + d i (MatrixMap.traceRight (spec.In i × R.D) E τ))
    {A : QReg} (x : QuantumComp L spec Ω A) (n : ℕ) (e : ℕ → ℝ≥0∞) (he : ∀ j < n, η ≤ e j)
    (hx : IFreeM.IsChargeBound x (portCharge fun _ ↦ 1) n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (hP : R.ForallQueries I P x ρ) :
    R.eventWeight I Q x ρ ^ (2⁻¹ : ℝ) ≤
      ∑' j, (e j * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  rw [eventWeight_eq_tsum_potential]
  exact rpow_inv_two_tsum_potential_run_le_sqrtCalls R I Q P η d hη x n e he hx hρ hP

end sqrtRun

/-- `∑' j, √(e j · t)` for `e` equal to `η` below `n` and `0` above: `n √(η t)`. -/
theorem tsum_rpow_inv_two_ite (n : ℕ) (η t : ℝ≥0∞) :
    ∑' j, ((if j < n then η else 0) * t) ^ (2⁻¹ : ℝ) = n * (η * t) ^ (2⁻¹ : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range n) fun j hj ↦ by
    simp only [show ¬ j < n by simpa using hj, ↓reduceIte, zero_mul]
    exact ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [Finset.sum_congr rfl (g := fun _ ↦ (η * t) ^ (2⁻¹ : ℝ)) fun j hj ↦ by
      simp only [Finset.mem_range.mp hj, ↓reduceIte],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Support through a partial trace -/

/-- A support condition read off the left factor passes to the partial trace. -/
theorem querySupportedOn_traceRight {α E Y : Type*} [Fintype E] {q : α → Y} {T : Set Y}
    {τ : Matrix (α × E) (α × E) ℂ} (h : QuerySupportedOn (fun m : α × E ↦ q m.1) T τ) :
    QuerySupportedOn q T (MatrixMap.traceRight α E τ) := by
  intro a b hab
  rw [MatrixMap.traceRight_apply] at hab
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
  exact h _ _ he

/-! ## Sequencing -/

section bind

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) (Q : Matrix R.D R.D ℂ)

/-- The event weight of a fixed-register program, summed over its return values. -/
theorem eventWeight_eq_tsum_run₂ {A B : QReg} {α : Type w} (x : QuantumComp₂ L spec A B α)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.eventWeight I Q x ρ = ∑' a, potential Q ((R.run₂ I x).branch a ρ) :=
  (eventWeight_eq_tsum_potential R I Q (X := QuantumComp₂.Leaf B α) x ρ).trans
    ((QuantumComp₂.leafEquiv B α).tsum_eq fun p ↦ potential Q ((R.run I x).branch p ρ)).symm

/-- **The event weight of a sequence**: summed over the return values `a` of `x`, the event
weight of `k a` from the branch of `x` at `a`. -/
theorem eventWeight_bind₂ {A B C : QReg} {α β : Type w} (x : QuantumComp₂ L spec A B α)
    (k : α → QuantumComp₂ L spec B C β) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.eventWeight I Q (x.bind k) ρ =
      ∑' a, R.eventWeight I Q (k a) ((R.run₂ I x).branch a ρ) := by
  simp only [eventWeight_eq_tsum_run₂]
  have h : ∀ b, (R.run₂ I (x.bind k)).branch b ρ =
      ∑' a, (R.run₂ I (k a)).branch b ((R.run₂ I x).branch a ρ) := fun b ↦ by
    rw [run₂_bind]
    exact DSubInstrument.branch_bind_apply _ _ b ρ
  simp only [h]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b ↦ potential_tsum Q (((R.run₂ I x).isCPTNIFamily.comp_eval
    (fun a ↦ (R.run₂ I (k a)).isCPTNIFamily) b).summable_apply ρ)
    fun a ↦ (R.run₂ I (k a)).posSemidef_branch_apply b ((R.run₂ I x).posSemidef_branch_apply a hρ)

/-- **A summed weight grows under sequencing**: the calls of `x` are among those of `x >>= k`. -/
theorem totalWeight_le_bind₂
    (wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) {A B C : QReg}
    {α β : Type w} (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B C β)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I wt x ρ ≤ R.totalWeight I wt (x.bind k) ρ := by
  revert ρ
  suffices h : ∀ (y : QuantumComp L spec (QuantumComp₂.Leaf B α) A)
      (ρ : Matrix (A × R.D) (A × R.D) ℂ), R.totalWeight I wt y ρ ≤
        R.totalWeight I wt (y.bind fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a) ρ from h x
  intro y
  clear x
  induction y using QuantumComp.inductionOn with
  | pure _ _ =>
    intro ρ
    rw [totalWeight_pure]
    exact zero_le
  | primBind _ o k' ih =>
    intro ρ
    rw [QuantumComp.primBind_bind, totalWeight_primBind, totalWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦ ih b _
  | queryBind _ i E ℓ k' ih =>
    intro ρ
    rw [QuantumComp.queryBind_bind, totalWeight_queryBind, totalWeight_queryBind]
    exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun r ↦ ih r _)

end bind

/-! ## The read costs from the fresh bound -/

section readCost

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [Fintype M] [DecidableEq M]

omit [Fintype X] [Fintype Z] [Fintype M] [DecidableEq M] in
/-- **The event is up-closed in every read cell** when its slices are. -/
theorem upCell_of_upClosed (S : Set (HwReg X Z M)) (hup : ∀ W m, UpClosed (slice S W m))
    (c : HwRead X Z M) : UpCell S c := by
  cases c with
  | readH z upd => exact fun s hs hS y ↦ (hup s.2.1 s.2.2).h s.1.toDbs hS z y hs
  | readK x upd => exact fun s hs hS y ↦ (hup s.2.1 s.2.2).k s.1.toDbs hS x y hs
  | readK' x upd => exact fun s hs hS y ↦ (hup s.2.1 s.2.2).k' s.1.toDbs hS x y hs

/-- A diagonal sum with coefficients at most `c` on the support: at most `c tr σ`. -/
theorem sum_mul_re_le_trace {ι : Type*} [Fintype ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (f : ι → ℝ) {c : ℝ} (hf : ∀ i, σ i i ≠ 0 → f i ≤ c) :
    ∑ i, f i * (σ i i).re ≤ c * σ.trace.re := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases h0 : σ i i = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hf i h0) (Complex.nonneg_iff.1 hσ.diag_nonneg).1

/-- A count fraction below `ε`, in reals. -/
theorem natCast_div_le_toReal {a b : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (h : (a : ℝ≥0∞) / b ≤ ε) : (a : ℝ) / b ≤ ε.toReal := by
  have h' := ENNReal.toReal_mono hεtop h
  rwa [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h'

omit [DecidableEq X] [DecidableEq Z] in
/-- The sizes of the databases are at most the grade. -/
theorem size_lt_of_dbGrade_le {D : DbReg X Z} {N : ℕ} (h : dbGrade D ≤ N) :
    D.1.size < N + 1 ∧ D.2.1.size < N + 1 ∧ D.2.2.size < N + 1 :=
  ⟨Nat.lt_succ_of_le ((le_max_left _ _).trans h),
    Nat.lt_succ_of_le (((le_max_left _ _).trans (le_max_right _ _)).trans h),
    Nat.lt_succ_of_le (((le_max_right _ _).trans (le_max_right _ _)).trans h)⟩

omit [DecidableEq M] in
/-- **The empty-cell term of a read from the fresh bound**: on states of database grade at most
`N`, for an event with up-closed slices and the fresh bound `ε` below `N + 1` entries,
`keepE ≤ ε tr σ`. A state in the event flips for no value; one outside for at most the
fraction `ε` of the values (`F/|X|` at an `h` cell). -/
theorem keepE_le_of_freshBound (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (hup : ∀ W m, UpClosed (slice S W m)) {N : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ W m, FreshBound (slice S W m) (N + 1) ε) (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hg : QuerySupportedOn (fun q : Unit × HwReg X Z M ↦ dbGrade q.2.1) (Set.Iic N) σ) :
    keepE S c σ ≤ ε.toReal * σ.trace.re := by
  have hup' := upCell_of_upClosed S hup c
  cases c with
  | readH z upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · by_cases hS : q.2 ∈ S
      · rw [show flipCnt S (.readH z upd) q = 0 from Finset.card_eq_zero.mpr
          (Finset.filter_eq_empty_iff.mpr fun b _ h ↦ h ⟨fun _ ↦ hS, fun _ ↦ hup' q.2 hq.2 hS b⟩)]
        simp
      · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
        have hf := (hε q.2.2.1 q.2.2.2).h q.2.1.toDbs hS h1 h2 h3 z hq.2
        refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
        refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
          (Nat.cast_nonneg _)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        by_contra hc
        exact hb ⟨fun h ↦ absurd h hc, fun h ↦ absurd h hS⟩
    · exact ENNReal.toReal_nonneg
  | readK x upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · by_cases hS : q.2 ∈ S
      · rw [show flipCnt S (.readK x upd) q = 0 from Finset.card_eq_zero.mpr
          (Finset.filter_eq_empty_iff.mpr fun b _ h ↦ h ⟨fun _ ↦ hS, fun _ ↦ hup' q.2 hq.2 hS b⟩)]
        simp
      · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
        have hf := (hε q.2.2.1 q.2.2.2).k q.2.1.toDbs hS h1 h2 h3 x hq.2
        refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
        refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
          (Nat.cast_nonneg _)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        by_contra hc
        exact hb ⟨fun h ↦ absurd h hc, fun h ↦ absurd h hS⟩
    · exact ENNReal.toReal_nonneg
  | readK' x upd =>
    unfold keepE
    refine sum_mul_re_le_trace hσ _ fun q hq0 ↦ ?_
    split_ifs with hq
    · by_cases hS : q.2 ∈ S
      · rw [show flipCnt S (.readK' x upd) q = 0 from Finset.card_eq_zero.mpr
          (Finset.filter_eq_empty_iff.mpr fun b _ h ↦ h ⟨fun _ ↦ hS, fun _ ↦ hup' q.2 hq.2 hS b⟩)]
        simp
      · obtain ⟨h1, h2, h3⟩ := size_lt_of_dbGrade_le (hg q q hq0).1
        have hf := (hε q.2.2.1 q.2.2.2).k' q.2.1.toDbs hS h1 h2 h3 x hq.2
        refine le_trans ?_ (natCast_div_le_toReal hεtop hf)
        refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun b hb ↦ ?_))
          (Nat.cast_nonneg _)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        by_contra hc
        exact hb ⟨fun h ↦ absurd h hc, fun h ↦ absurd h hS⟩
    · exact ENNReal.toReal_nonneg

omit [DecidableEq M] in
/-- **The recorded-cell term**: `recW ≤ (2/|X| + 2/|Z|) tr σ`. -/
theorem recW_le (c : HwRead X Z M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    recW c σ ≤ (2 / Fintype.card X + 2 / Fintype.card Z) * σ.trace.re := by
  cases c with
  | readH z upd =>
    unfold recW
    refine sum_mul_re_le_trace hσ _ fun q _ ↦ ?_
    split_ifs
    · exact le_add_of_nonneg_right (by positivity)
    · positivity
  | readK x upd =>
    unfold recW
    refine sum_mul_re_le_trace hσ _ fun q _ ↦ ?_
    split_ifs
    · exact le_add_of_nonneg_left (by positivity)
    · positivity
  | readK' x upd =>
    unfold recW
    refine sum_mul_re_le_trace hσ _ fun q _ ↦ ?_
    split_ifs
    · exact le_add_of_nonneg_left (by positivity)
    · positivity

end readCost

/-! ## The reads of `runtimeR` that keep the memory -/

section keepReads

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- `ofReal (2 / n) = 2 / n`. -/
theorem ofReal_two_div_natCast {n : ℕ} (hn : 0 < n) :
    ENNReal.ofReal (2 / (n : ℝ)) = 2 / (n : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat]

variable (X Z) in
/-- The additive cost of a read that keeps the memory, per unit of trace: `ε + 2/|X| + 2/|Z|`. -/
noncomputable def keepCost (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ε + 2 / (Fintype.card X : ℝ≥0∞) + 2 / (Fintype.card Z : ℝ≥0∞)

/-- **A read of `runtimeR` that keeps the memory costs like a sponge call**: on a state of
database grade at most `N` with no decompressed `⊥`, for an event with up-closed slices and the
fresh bound `ε` below `N + 1` entries, `∑ w' ≤ (√w + √(ε tr σ))² + (ε + 2/|X| + 2/|Z|) tr σ`
(ReadCost's `potential_readKeep_le_sqrt`, `keepE_le_of_freshBound`, `recW_le`). -/
theorem tsum_potential_readKeep_runtimeR_le (B : Set (HwReg X Z (Finset S × M)))
    [DecidablePred (· ∈ B)] (hup : ∀ W m, UpClosed (slice B W m)) (m₀ : Finset S × M)
    (c : HwRead X Z (Finset S × M)) (hk : KeepUpd c) {N : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ W m, FreshBound (slice B W m) (N + 1) ε)
    {σ : Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ}
    (hσ : σ.PosSemidef)
    (hg : QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M) ↦ dbGrade q.2.1)
      (Set.Iic N) σ)
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M)) σ)) :
    ∑' r, potential (hwProjector B) (((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ) ≤
      (potential (hwProjector B) σ ^ (2⁻¹ : ℝ) + (ε * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 +
        keepCost X Z ε * ENNReal.ofReal σ.trace.re := by
  have hstep : ∀ r, ((runtimeR m₀).step (.inl (.inl (.inr c)))).branch r σ =
      MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
    LinearMap.congr_fun (runtime2_branch m₀ (.inl (.inr c)) r) σ
  simp only [hstep]
  have hE := keepE_le_of_freshBound B hup hεtop hε c hσ hg
  have hR := recW_le c hσ
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  refine (potential_readKeep_le_sqrt B c hk (upCell_of_upClosed B hup c) hσ
    (readNoBot_of_noBot c hnb)).trans (add_le_add ?_ ?_)
  · gcongr
    refine (ENNReal.ofReal_le_ofReal hE).trans_eq ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hεtop]
  · calc ENNReal.ofReal (keepE B c σ + recW c σ)
        ≤ ENNReal.ofReal ((ε.toReal + (2 / Fintype.card X + 2 / Fintype.card Z)) *
            σ.trace.re) :=
          ENNReal.ofReal_le_ofReal (by rw [add_mul]; exact add_le_add hE hR)
      _ = keepCost X Z ε * ENNReal.ofReal σ.trace.re := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_toReal hεtop,
            ofReal_two_div_natCast Fintype.card_pos, ofReal_two_div_natCast Fintype.card_pos,
            keepCost, add_assoc]

/-- Every port of `runtimeR` raises the database grade by at most one. -/
theorem querySupportedOn_runtimeR_step' (m₀ : Finset S × M) (i : (recHwSpec X Z S M).Port)
    (r : (recHwSpec X Z S M).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z S M).In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec X Z S M).In i ×
      (runtimeR (X := X) (Z := Z) m₀).D ↦ dbGrade q.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec X Z S M).Out i ×
      (runtimeR (X := X) (Z := Z) m₀).D ↦ dbGrade q.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := X) (Z := Z) m₀).step i).branch r σ) := by
  rcases i with i | j
  · exact querySupportedOn_spongeHardwiredRuntime_step (hwEmpty X Z) m₀ i r t σ hσ
  · exact querySupportedOn_recStep j r t σ hσ

/-- **No decompressed `⊥` at the calls**: from an operator with no empty decompressed cell, every
call of a run of `runtimeR` is presented an operator whose input has none (EndReads'
`decR_step_noBot` in the decompressed basis, carried back by `ForallQueries.of_simulation`). -/
theorem forallQueries_noBot (m₀ : Finset S × M) {L : LocalSig.{u, v}} (I : L.Interp)
    {Ω : QReg → Type w} {A : QReg} (x : QuantumComp L (recHwSpec X Z S M) Ω A)
    {ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ}
    (hρ : QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M)) ρ)) :
    (runtimeR m₀).ForallQueries I (fun i E τ ↦
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M).In i)
          ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M))
            (MatrixMap.traceRight _ E τ))) x ρ := by
  have hC : compressReg X Z (Finset S × M) * compressReg X Z (Finset S × M) = 1 :=
    compressReg_mul_self
  have h1 := forallQueries_suppOn I (decR m₀) (fun s ↦ NoBot s) (fun _ ↦ True)
    (fun i _ r τ hτ ↦ decR_step_noBot m₀ i r τ hτ)
    (forallQueries_of_forall (decR m₀) I (fun _ _ _ ↦ trivial) x _) hρ
  have hstep : ∀ i r, ((runtimeRH m₀).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft ((recHwSpec X Z S M).In i) =
      (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft ((recHwSpec X Z S M).Out i) ∘ₗ
        ((decR m₀).step i).branch r := fun i r ↦ by
    rw [conjReg_branch (runtimeRH m₀) (compressReg X Z (Finset S × M)) compressReg_mul_self
      conjTranspose_compressReg i r]
    simp only [MatrixMap.amplifyLeft_conj]
    rw [← LinearMap.comp_assoc, conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
      LinearMap.id_comp]
  have hP : ∀ (i : (recHwSpec X Z S M).Port) (E : QReg)
      (τ : Matrix (((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) × E)
        (((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) × E) ℂ),
      (True ∧ SuppOn (fun p : ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) × E ↦
        NoBot p.1.2) τ) →
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M).In i)
          ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M))
            (MatrixMap.traceRight _ E (((MatrixMap.conj
              (compressReg X Z (Finset S × M))).amplifyLeft ((recHwSpec X Z S M).In i)).amplify
                E τ))) := fun i E τ hτ ↦ by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj _) (MatrixMap.traceRight _ E),
      ← MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply,
      ← LinearMap.comp_apply (MatrixMap.amplify _ E) (MatrixMap.amplify _ E),
      ← MatrixMap.amplify_comp, conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
      MatrixMap.amplify_id, LinearMap.id_apply]
    exact querySupportedOn_traceRight (q := fun m : (recHwSpec X Z S M).In i ×
      HwReg X Z (Finset S × M) ↦ m.2) hτ.2
  have h2 := ForallQueries.of_simulation I (R₁ := decR m₀) (R₂ := runtimeRH m₀)
    (V := MatrixMap.conj (compressReg X Z (Finset S × M))) hstep
    (P₂ := fun i E τ ↦
      QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
        {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M).In i)
          ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M))
            (MatrixMap.traceRight _ E τ))) hP h1
  have hρ' : (MatrixMap.conj (compressReg X Z (Finset S × M))).amplifyLeft A
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M)) ρ) = ρ := by
    rw [MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ
        compressReg X Z (Finset S × M))), conj_one_kronecker_comp_self (runtimeRH m₀) _ hC,
      LinearMap.id_apply]
  rw [hρ'] at h2
  exact h2

open scoped Classical in
variable (X Z S M) in
/-- The charge of the calls other than the reads that keep the memory. -/
noncomputable def nonKeep : (recHwSpec X Z S M).Port → ℕ
  | .inl (.inl (.inl _)) => 1
  | .inl (.inl (.inr c)) => if KeepUpd c then 0 else 1
  | .inl (.inr _) => 1
  | .inr _ => 1

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] [Fintype S] [DecidableEq S]
  [Fintype M] [DecidableEq M] in
theorem nonKeep_le_one (i : (recHwSpec X Z S M).Port) : nonKeep X Z S M i ≤ 1 := by
  rcases i with ((p | c) | c) | T
  · exact le_rfl
  · simp only [nonKeep]
    split_ifs <;> omega
  · exact le_rfl
  · exact le_rfl

/-- **A program of reads that keep the memory, on `runtimeR`**: from an operator of database grade
at most `t` with no decompressed `⊥`, a program of at most `n` calls, all reads that keep the
memory, ends with `√w ≤ ∑' j<n, √(ε tr ρ) + √(w ρ + n (ε + 2/|X| + 2/|Z|) tr ρ)` for an event
with up-closed slices and the fresh bound `ε` below `N + 1 ≥ t + n + 1` entries. -/
theorem rpow_inv_two_eventWeight_keepReads_le (B : Set (HwReg X Z (Finset S × M)))
    [DecidablePred (· ∈ B)] (hup : ∀ W m, UpClosed (slice B W m)) (m₀ : Finset S × M) {N : ℕ}
    {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshBound (slice B W m) (N + 1) ε)
    {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w} {A : QReg}
    (y : QuantumComp L (recHwSpec X Z S M) Ω A) {n t : ℕ}
    (hy : IFreeM.IsChargeBound y (portCharge fun _ ↦ 1) n)
    (hyk : IFreeM.IsChargeBound y (portCharge (nonKeep X Z S M)) 0) (htn : t + n ≤ N)
    {ρ : Matrix (A × HwReg X Z (Finset S × M)) (A × HwReg X Z (Finset S × M)) ℂ}
    (hρ : ρ.PosSemidef)
    (hg : QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ dbGrade m.2.1) (Set.Iic t) ρ)
    (hnb : QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M)) ρ)) :
    (runtimeR m₀).eventWeight I (hwProjector B) y ρ ^ (2⁻¹ : ℝ) ≤
      ∑' j, ((if j < n then ε else 0) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential (hwProjector B) ρ + n * keepCost X Z ε * ENNReal.ofReal ρ.trace.re) ^
          (2⁻¹ : ℝ) := by
  have hP := forallQueries_and
    (forallQueries_of_charge_step (runtimeR m₀) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
      (nonKeep X Z S M) (fun i r t σ hσ ↦ querySupportedOn_runtimeR_step' m₀ i r t σ hσ) I y hy
      hyk hg)
    (forallQueries_noBot m₀ I y hnb)
  refine (rpow_inv_two_eventWeight_le_sqrtCalls (runtimeR m₀) I (hwProjector B) _ ε
    (fun _ σ ↦ keepCost X Z ε * ENNReal.ofReal σ.trace.re) (fun i E τ hτ hτp ↦ ?_) y n
    (fun j ↦ if j < n then ε else 0) (fun j hj ↦ by simp [hj]) hy hρ hP).trans ?_
  · obtain ⟨⟨h0, hgr⟩, hnb'⟩ := hτ
    rcases i with ((p | c) | c) | T
    · exact absurd (h0 : (1 : ℕ) = 0) one_ne_zero
    · have hk : KeepUpd c := by
        by_contra hk
        have h1 : nonKeep X Z S M (.inl (.inl (.inr c))) = 1 := by
          simp only [nonKeep, hk, ↓reduceIte]
        omega
      exact tsum_potential_readKeep_runtimeR_le B hup m₀ c hk hεtop hε hτp.traceRight
        ((querySupportedOn_traceRight (q := fun m : Unit × HwReg X Z (Finset S × M) ↦
          dbGrade m.2.1) hgr).mono (Set.Iic_subset_Iic.mpr htn)) hnb'
    · exact absurd (h0 : (1 : ℕ) = 0) one_ne_zero
    · exact absurd (h0 : (1 : ℕ) = 0) one_ne_zero
  · refine add_le_add le_rfl (ENNReal.rpow_le_rpow (add_le_add le_rfl ?_) (by norm_num))
    refine (totalWeight_const_mul_weight (runtimeR m₀) I (keepCost X Z ε)
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) y ρ).trans_le ?_
    have h1 := totalWeight_chargeTrace_le (runtimeR m₀) I (fun _ ↦ 1) y hy hρ
    simp only [Nat.cast_one, one_mul] at h1
    calc keepCost X Z ε * (runtimeR m₀).totalWeight I (fun _ σ ↦ ENNReal.ofReal σ.trace.re) y ρ
        ≤ keepCost X Z ε * (n * ENNReal.ofReal ρ.trace.re) :=
          mul_le_mul_of_nonneg_left h1 zero_le
      _ = n * keepCost X Z ε * ENNReal.ofReal ρ.trace.re := by ring

end keepReads

/-! ## The verification's reads keep the memory -/

section verifyCharges

variable {M : Type} [Fintype M] [DecidableEq M]

open scoped Classical in
variable (M) in
/-- The charge of runtime 1's calls other than the reads that keep the memory. -/
noncomputable def nonKeepRd : (hwReadSpec X Z M).Port → ℕ
  | .inl _ => 1
  | .inr c => if c.KeepsMem then 0 else 1

omit [Fintype M] [DecidableEq M] in
/-- A lifted read that keeps the memory keeps the memory with the label. -/
theorem keepUpd_liftRead {S : Type} (c : HwRead X Z M) (hc : c.KeepsMem) :
    KeepUpd (liftRead (S := S) c) := by
  cases c with
  | readH z upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl
  | readK x upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl
  | readK' x upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem nonKeepRd_inr_keep (c : HwRead X Z M) (hc : c.KeepsMem) : nonKeepRd M (.inr c) = 0 := by
  simp only [nonKeepRd, hc, ↓reduceIte]

omit [Fintype M] [DecidableEq M] in
/-- A read that keeps the memory has charge `0`. -/
theorem chg_readCall_keep (c : HwRead X Z M) (hc : c.KeepsMem) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (nonKeepRd M)) 0 := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
      ⟨le_of_eq (nonKeepRd_inr_keep c hc), fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_read_keep {β : Type} (c : HwRead X Z M) (hc : c.KeepsMem) (B : QReg)
    (g : c.Result → List (SpongeRead X Z) → β × List (SpongeRead X Z)) :
    SChg (nonKeepRd M) (fun log ↦ (readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log) :
      StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β) 0 := by
  intro log
  show IFreeM.IsChargeBound ((readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log)) _ _
  exact FreeM₂.isChargeBound_bind (n₂ := 0) (chg_readCall_keep c hc B) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_rdRound_keep (π : Equiv.Perm (X × Z)) (B : QReg) (s : X × Z) (blk : X) :
    SChg (nonKeepRd M) (rdRound M π B s blk) 0 :=
  sChg_mono _ (sChg_bind _ (sChg_read_keep _ (by rfl) B _) fun _ ↦
    sChg_bind _ (sChg_read_keep _ (by rfl) B _) fun _ ↦
      sChg_bind _ (sChg_read_keep _ (by rfl) B _) fun _ ↦ sChg_pure _ _ 0) le_rfl

omit [Fintype M] [DecidableEq M] in
theorem sChg_readsImpl_keep (π : Equiv.Perm (X × Z)) (B : QReg) (input : HashInput) :
    SChg (nonKeepRd M) (readsImpl M π B input) 0 :=
  sChg_mono _ (sChg_map _ _ (sChg_map _ _
    (sChg_foldlM _ _ 0 (sChg_rdRound_keep π B) (blocks input) (0, 0)))) (by simp)

omit [Fintype M] [DecidableEq M] in
theorem sChg_simulateQ_keep (π : Equiv.Perm (X × Z)) (B : QReg) {α : Type}
    (x : OracleComp LeanXmss.HashSpec α) :
    SChg (nonKeepRd M) (simulateQ (readsImpl M π B) x) 0 := by
  induction x using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure]; exact sChg_pure _ x _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact sChg_bind _ (sChg_readsImpl_keep π B t) fun u ↦ ih u

omit [Fintype M] [DecidableEq M] in
/-- **The verification calls only reads that keep the memory.** -/
theorem chg_verifyT_nonKeep (pub : Pub) (v : HPos → Digest)
    (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x)) (portCharge (nonKeep X Z HPos M)) 0 := by
  unfold verifyT
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_keep (M := M) pub.perm (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep X Z HPos M (.inl (.inl (.inr (liftRead c)))) ≤ nonKeepRd M (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep X Z HPos M (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftRead (S := HPos) c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRd M (.inr c) = 1 := by simp only [nonKeepRd, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := X) (Z := Z) (S := HPos) (M := M)
        (.inl (.inl (.inr (liftRead c))))
      omega

omit [Fintype M] [DecidableEq M] in
/-- **The verification's calls**: at most `3 verifyBlocks`. -/
theorem chg_verifyT_one (pub : Pub) (v : HPos → Digest) (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x)) (portCharge fun _ ↦ 1)
      (3 * verifyBlocks) := by
  have he : rCharge M 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have hv := chg_readsProgram (M := M) 1 1 pub.perm (QReg.of Unit) (verify_cost' x.1 x.2.1)
  have hb : IFreeM.IsChargeBound (verifyT M pub x) (portCharge (tCharge M 1 1 1 1))
      (3 * verifyBlocks) := by
    unfold verifyT
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (isChargeBound_readLift 1 1 1 1 (chg_map _ Prod.fst hv)) fun _ ↦ trivial) (by omega)
  have h := isChargeBound_realizeT 1 1 1 1 v hb
  rwa [he] at h

end verifyCharges

/-! ## The canonical game -/

section game

attribute [local instance] badRDec

/-- **The fresh bound of the verification's reads**: S4's preimage rate below
`progCap + 6q + clsCap + 3 verifyBlocks + 1` entries (the prefix's calls, then the verification's;
`2^960 / 2^1088 = 2^-128` at the `h` cells, capacity scale at the `k`, `k'` cells). -/
noncomputable def verEps (q : ℕ) : ℝ≥0∞ :=
  preimageRateBound (X := X) (Z := Z) (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1)) 18
    (2 ^ 960)

/-- **The verification term**: `3 verifyBlocks · √verEps`, the verification's reads graded like
sponge calls. -/
noncomputable def verTerm (q : ℕ) : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * verEps q ^ (2⁻¹ : ℝ)

/-- **The verification's linear term**: `3 verifyBlocks (verEps + 2/|X| + 2/|Z|)`, the empty-cell
and recorded-cell terms `keepE + recW` of its reads. -/
noncomputable def verLin (q : ℕ) : ℝ≥0∞ :=
  ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q)

/-- **The classical costs of the challenge prefix** (CostLift's per-port flip costs `dRof`, `dPof`;
record ports free), summed along its run. -/
noncomputable def twP (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (dRof L) (dPof L))) (prefixR A L)
    initR

theorem verEps_ne_top (q : ℕ) : verEps q ≠ ⊤ := by
  have hX : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold verEps preimageRateBound
  exact max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hX)
    (max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ))

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The event bound at the end of the challenge prefix** (Security's linear prices). -/
theorem ewPrefix_le (L : HonestTable) (hπ : PermGood L.perm 18) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR ≤
      (advTerm q + twP A L ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_runtimeR_le (q := 6 * q) (K := clsCap) (BadR L progCap) (labelFree_badR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (empty_not_mem_bad m0) advEps
    (fun n _ ↦ advEps_ne_top n)
    (fun n _ W m ↦ freshBound_slice_badR L hπ (n + clsCap + 1) W m)
    (dRof L) (dPof L)
    (fun c σ hσ ↦ potential_hwReadKraus_le (BadR L progCap) (PRm L)
      (fun c ↦ (PRof_proj Prod.snd trialUpd L c).1) (fun c ↦ (PRof_proj Prod.snd trialUpd L c).2)
      c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR L progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    .instruments (prefixR A L) (advCalls_prefixR hperm hsign L) (clsCalls_prefixR hperm hsign L)
    (SubState.basis ())

/-- **The prefix's calls**: at most `6q + clsCap`. -/
theorem calls_prefixR (L : HonestTable) :
    IPFunctor.IFreeM.IsChargeBound (prefixR A L) (portCharge fun _ ↦ 1) (6 * q + clsCap) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixR hperm hsign L).add (clsCalls_prefixR hperm hsign L))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0)
    split_ifs <;> omega

/-- **The event bound over the whole game, the verification's reads graded like sponge calls**:
on a `PermGood` table, `ewR (gameR A) L ≤ (advTerm q + verTerm q + √(twP A L + verLin q))²`. The
challenge prefix keeps Security's linear prices (`twP`: CostLift's flip costs of its read and
program calls; record calls free); each of the `3 verifyBlocks` verification reads costs
`√verEps` in the square root (ReadCost's square-root form) plus its linear terms `keepE + recW`
(`verLin`). -/
theorem ewR_le_sqrt (L : HonestTable) (hπ : PermGood L.perm 18) :
    ewR (gameR A) L ≤ (advTerm q + verTerm q + (twP A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0R).run₂ .instruments (prefixR A L)).posSemidef_branch_apply a
    initR_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (querySupportedOn_runtimeR_step m0R) .instruments (calls_prefixR hperm hsign L)
    querySupportedOn_initR ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR m0R .instruments (prefixR A L) (SubState.basis ()).matrix
    ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (N := 6 * q + clsCap + 3 * verifyBlocks)
    (verEps_ne_top q) (fun W m ↦ freshBound_slice_badR L hπ _ W m) .instruments
    (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
    (chg_verifyT_one (pubOf L) (valueAt L) a) (chg_verifyT_nonKeep (pubOf L) (valueAt L) a)
    (t := 0 + (6 * q + clsCap)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
      initR).trace.re ≤ 1 :=
    (((runtimeR m0R).run₂ .instruments (prefixR A L)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initR_posSemidef).trans ofReal_trace_initR_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0R) .instruments
    (hwProjector (BadR L progCap)) (prefixR A L) initR
  have hm : ∑' j, (∑' a, (if j < 3 * verifyBlocks then verEps q else 0) *
      ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
        initR).trace.re) ^ (2⁻¹ : ℝ) ≤ verTerm q := by
    calc _ ≤ ∑' j, ((if j < 3 * verifyBlocks then verEps q else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTerm q := by
          unfold verTerm
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadR L progCap))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) +
      ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) *
        ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
          initR).trace.re) ≤
      (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR +
        verLin q := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * _
        ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * 1 := by gcongr
      _ = verLin q := mul_one _
  have hpre' : ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
      (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) ≤
      advTerm q + (twP A L + verLin q) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTerm q ^ 2) (δ := 0) (C := verLin q)
      (b := twP A L) (a := (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
        (prefixR A L) initR) (by
          rw [pow_two_rpow_inv_two, add_zero, add_comm]
          exact ewPrefix_le hperm hsign L hπ)
    rwa [pow_two_rpow_inv_two, zero_add] at h
  have hew : ewR (gameR A) L = ∑' a, (runtimeR m0R).eventWeight .instruments
      (hwProjector (BadR L progCap)) (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) := by
    unfold ewR
    rw [gameR_eq]
    exact eventWeight_bind₂ (runtimeR m0R) .instruments (hwProjector (BadR L progCap))
      (prefixR A L) _ initR_posSemidef
  have hfin : ewR (gameR A) L ^ (2⁻¹ : ℝ) ≤
      advTerm q + verTerm q + (twP A L + verLin q) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
          (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) + verTerm q :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTerm q + (twP A L + verLin q) ^ (2⁻¹ : ℝ) + verTerm q := add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

omit hperm hsign in
/-- The prefix's classical costs are among the game's: `twP ≤ twR`. -/
theorem twP_le_twR (A : Adversary (X × Z)) (L : HonestTable) : twP A L ≤ twR A L := by
  unfold twP twR costTot
  rw [gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR A L) _ initR

/-- **`ewR_le_sqrt` with Security's game-wide classical cost `twR`**:
`ewR (gameR A) L ≤ (advTerm q + verTerm q + √(twR A L + verLin q))²` on `PermGood` tables. -/
theorem ewR_le_sqrt_twR (L : HonestTable) (hπ : PermGood L.perm 18) :
    ewR (gameR A) L ≤ (advTerm q + verTerm q + (twR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  (ewR_le_sqrt hperm hsign L hπ).trans (by gcongr; exact twP_le_twR A L)

end game

/-! ## The verification part at Keccak sizes -/

section numbers

/-- A count fraction below `2^-k`. -/
theorem natCast_div_le_inv_two_pow {a b k : ℕ} (h : a * 2 ^ k ≤ b) :
    (a : ℝ≥0∞) / b ≤ (2 ^ k : ℝ≥0∞)⁻¹ := by
  refine ENNReal.div_le_of_le_mul ?_
  have h' : (a : ℝ≥0∞) * 2 ^ k ≤ b := by exact_mod_cast h
  have h2 : (2 ^ k : ℝ≥0∞) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 ^ k : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc (a : ℝ≥0∞) = a * 2 ^ k * (2 ^ k)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2 h2', mul_one]
    _ ≤ b * (2 ^ k)⁻¹ := by gcongr
    _ = (2 ^ k)⁻¹ * b := mul_comm _ _

/-- The entries below which the verification's fresh bound is taken: below `2^68` for
`q ≤ 2^64`. -/
theorem verEntries_le {q : ℕ} (hq : q ≤ 2 ^ 64) :
    progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1 ≤ 2 ^ 68 := by
  have h64 : q ≤ 18446744073709551616 := hq
  have hl : lifetime = 4294967296 := by simp [lifetime, layerCount, layerHeight]
  have h68 : (2 : ℕ) ^ 68 = 295147905179352825856 := by norm_num
  rw [clsCap, signBlocks_eq, verifyBlocks_eq, progCap_eq, hl, h68]
  omega

set_option exponentiation.threshold 1100 in
/-- **The verification's fresh bound at Keccak sizes**: `verEps q ≤ 2^-128` for `q ≤ 2^64` (the
`h` fraction `2^960 / 2^1088`; the capacity terms `3 · 18 (T+1)³ / 2^512 ≤ 2^-300`). -/
theorem verEps_le {q : ℕ} (hq : q ≤ 2 ^ 64) : verEps q ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (preimageRateBound_le_cube (by norm_num) _ _).trans (max_le ?_ ?_)
  · rw [card_X]
    exact natCast_div_le_inv_two_pow (pow_add 2 960 128).symm.le
  · rw [card_Z]
    refine natCast_div_le_inv_two_pow ?_
    calc 3 * 18 * (progCap + (6 * q + clsCap + 3 * verifyBlocks + 1) + 1) ^ 3 * 2 ^ 128
        ≤ 3 * 18 * (2 ^ 68) ^ 3 * 2 ^ 128 := by gcongr; exact verEntries_le hq
      _ ≤ 2 ^ 6 * (2 ^ 68) ^ 3 * 2 ^ 128 := by gcongr; norm_num
      _ = 2 ^ 338 := by rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- **The verification term at Keccak sizes**: `verTerm q ≤ 1194 · 2^-64` for `q ≤ 2^64`
(`3 verifyBlocks = 1194` reads at `√(2^-128)` each, about `2^-53.8`). -/
theorem verTerm_le {q : ℕ} (hq : q ≤ 2 ^ 64) : verTerm q ≤ 1194 * (2 ^ 64 : ℝ≥0∞)⁻¹ := by
  have h2 : ((2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ) = (2 ^ 64 : ℝ≥0∞)⁻¹ := by
    rw [show (2 ^ 128 : ℝ≥0∞) = (2 ^ 64) ^ 2 by rw [← pow_mul],
      ENNReal.inv_pow (a := (2 ^ 64 : ℝ≥0∞)) (n := 2), pow_two_rpow_inv_two]
  have h := ENNReal.rpow_le_rpow (verEps_le hq) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  rw [h2] at h
  unfold verTerm
  rw [verifyBlocks_eq]
  calc ((3 * 398 : ℕ) : ℝ≥0∞) * verEps q ^ (2⁻¹ : ℝ) ≤ ((3 * 398 : ℕ) : ℝ≥0∞) * (2 ^ 64)⁻¹ := by
        gcongr
    _ = 1194 * (2 ^ 64 : ℝ≥0∞)⁻¹ := by norm_num

/-- `2 / b ≤ 2^-k` for `2 · 2^k ≤ b`. -/
theorem two_div_natCast_le {b k : ℕ} (h : 2 * 2 ^ k ≤ b) : (2 : ℝ≥0∞) / (b : ℝ≥0∞) ≤ (2 ^ k)⁻¹ := by
  have h' := natCast_div_le_inv_two_pow (a := 2) h
  rwa [Nat.cast_ofNat] at h'

set_option exponentiation.threshold 1100 in
/-- **The verification's linear term at Keccak sizes**: `verLin q ≤ 3582 · 2^-128` for
`q ≤ 2^64` (per read and unit of trace, `keepE ≤ 2^-128` and `recW ≤ 2/2^1088 + 2/2^512`). -/
theorem verLin_le {q : ℕ} (hq : q ≤ 2 ^ 64) : verLin q ≤ 3582 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  have hE := verEps_le hq
  have hX : (2 : ℝ≥0∞) / (Fintype.card X : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_X]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have hZ : (2 : ℝ≥0∞) / (Fintype.card Z : ℝ≥0∞) ≤ (2 ^ 128)⁻¹ := by
    rw [card_Z]
    exact two_div_natCast_le ((pow_succ' 2 128).symm.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  unfold verLin keepCost
  rw [verifyBlocks_eq]
  calc ((3 * 398 : ℕ) : ℝ≥0∞) * (verEps q + 2 / (Fintype.card X : ℝ≥0∞) +
        2 / (Fintype.card Z : ℝ≥0∞)) ≤
        ((3 * 398 : ℕ) : ℝ≥0∞) * ((2 ^ 128)⁻¹ + (2 ^ 128)⁻¹ + (2 ^ 128)⁻¹) := by
        gcongr
    _ = 3582 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
        rw [show (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 128)⁻¹ + (2 ^ 128)⁻¹ = 3 * (2 ^ 128)⁻¹ by ring,
          ← mul_assoc]
        norm_num

end numbers

end Quantum.Xmss.Assembly

end
