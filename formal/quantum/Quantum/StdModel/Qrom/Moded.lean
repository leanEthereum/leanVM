module

public import Quantum.Xmss.Assembly.NoReuse
public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.StdModel.Qrom.OffTweak
public import Quantum.StdModel.Qrom.ReadGrade

@[expose] public section

/-!
# Memory-moded runs of runtime 2, in the compressed and the decompressed basis

The property bounds track the classical memory of runtime 2 (`Quantum.Xmss.Hybrid.runtime2`, the
hardwired runtime with no hardwired cell) by modes (`Quantum.Xmss.Assembly.ModedP`): the mode of a
call is the memory its input is supported on, moved by the read policies. In the decompressed
basis (`decR2`) the reads of `h` are classical projections onto the database's value at the read
cell, so a memory that logs every read outcome (`rl`) agrees with the decompressed database; a
read whose outcome contradicts the log has the zero branch (mode `none`).

* **Moded supports** (`querySupportedOn_run_moded`): if every allowed call moves the support from
  the invariant of its mode to that of the next mode, every leaf is supported on the invariants of
  the modes reaching it.
* **The decompressed invariant** (`DInv`, `nxD`, `OkD`, `decR2_step_dInv`, `dInv_init`): the
  memory, no hardwired cell, no decompressed `⊥`, and the log held by the database; kept by sponge
  calls and by reads of `h` whose policy logs the outcome (`RecordsAt`).
* **A win is in the event** (`evalDistMap_le_eventWeight_moded`): if every leaf returning `true`
  is reached in a mode whose memory is in `Won`, and the event contains the registers with memory
  in `Won`, the probability of `true` is at most the event weight.
* **The calls** (`forallQueries_runtime2_dInv`): every call of the compressed run is presented an
  operator whose decompressed form is supported on the invariant of a mode allowing it.
* **The graded bound along modes** (`rpow_inv_two_tsum_potential_runtime2_moded`): calls of
  class A (port charges, at most `nA`) and of class B (mode-dependent charges paid from a budget
  `bud`) raise the square root of the event weight by their charge times `√(η tr σ)`; doomed
  modes, whose leaves are dead, are free.
* **Reads invisible on the support** (`tsum_potential_hwReadKraus_le_of_supp`): a read none of
  whose transitions from the support of its input crosses the event adds no weight.
* **Mixed programs** (`nxM`, `modedP_toReads`, `liveImpl`, `liveRed`, `modedP_mixGame`): the
  modes of a read program come from its mixed program, whose classical algorithms are moded by
  their live runs (every read answered by any value consistent with the log).
* **The phase of the answers** (`okPhM`, `nxPhM`, `modedP_phase_mixGame`, `modedP_prod`,
  `modedP_toReads_prod`): the challenger's answers come before the adversary's first hash call
  and before any other caller's read at a cell of `Gc`.
* **Invariants and counts along live runs** (`liveRun_inv`, `liveRedRun_inv_cost`,
  `liveRedRun_count`): invariants of the modes kept by the allowed reads, and counts raised by
  each read by at most its cost.
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal Kronecker ComplexOrder

universe u v w

namespace Quantum.StdModel.Qrom

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Xmss.Assembly (ModedP NoBot NoBotDb conjReg conjReg_branch run_conjReg
  conj_one_kronecker_comp_self kron_one_mul_clsKraus_mul_kron_one one_kron_mul_hwPort_mul_one_kron
  dbs_dec_ne_zero cellRead_dec_ne_zero one_dec_ne_zero forallQueries_of_modedP_sguard)
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch kraus2)

/-! ## Moded supports along a run -/

section moded

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {Mode : Type} {ok : Mode → spec.Port → Prop}
  {nx : Mode → (i : spec.Port) → spec.Result i → Mode} (Inv : Mode → Set R.D)

/-- **One allowed call moves the support of its mode's invariant to the next mode's.** -/
theorem querySupportedOn_queryStep_moded
    (hstep : ∀ μ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), ok μ i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) (Inv μ) σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) (Inv (nx μ i r))
        ((R.step i).branch r σ))
    {A : QReg} {μ : Mode} {i : spec.Port} (hi : ok μ i) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (r : spec.Result i) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ m.2) (Inv μ) ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ m.2) (Inv (nx μ i r))
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := Inv μ) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ m.2)
    (q' := fun m : spec.Out i × R.D ↦ m.2) (fun σ hσ ↦ hstep μ i r σ hi hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- **Moded supports at the leaves**: every leaf `p` of a moded program is supported on the
invariants of the modes `μ'` with `fin p μ'`. -/
theorem querySupportedOn_run_moded
    (hstep : ∀ μ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), ok μ i →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) (Inv μ) σ →
      QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) (Inv (nx μ i r))
        ((R.step i).branch r σ))
    {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg} (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ∀ {ρ : Matrix (A × R.D) (A × R.D) ℂ},
      QuerySupportedOn (fun m : A × R.D ↦ m.2) (Inv μ) ρ → ∀ p,
        QuerySupportedOn (fun m : p.1 × R.D ↦ m.2) {d | ∃ μ', fin p μ' ∧ d ∈ Inv μ'}
          ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    intro μ hx ρ hρ p
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.imp fun d hd ↦ ⟨μ, hx, hd⟩
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    intro μ hx ρ hρ p
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c μ (hx.2 (ULift.up c))
      (QuerySupportedOn.amplify_snd (q := id) hρ _) p
  | queryBind _ i E ℓ k ih =>
    intro μ hx ρ hρ p
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun r ↦ ih r _ (hx.2 (ULift.up r))
      (querySupportedOn_queryStep_moded R Inv hstep hx.1 E ℓ r hρ) p

end moded

/-! ## Runtime 2 in the decompressed basis -/

section dec

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

/-- **The decompressed invariant of a mode**: the memory, no hardwired cell, no decompressed `⊥`,
and the log `rl` of the memory held by the `h`-database. The dead mode `none` has none. -/
def DInv (rl : M → Z → Option X) : Option M → Set (HwReg X Z M)
  | none => ∅
  | some m => {s | s.2.2 = m ∧ s.2.1 = hwEmpty X Z ∧ NoBot s ∧
      ∀ z x, rl m z = some x → s.1.1 z = some x}

/-- A read policy at cell `z` logs the outcome. -/
def RecordsAt (rl : M → Z → Option X) (z : Z) (upd : M → Option X → M) : Prop :=
  ∀ m o, rl (upd m o) = Function.update (rl m) z o

/-- **The mode after a read of `z` with value `v`**: dead if the log holds another value at `z`,
else the memory moved by the policy `u`. -/
def stepRd (rl : M → Z → Option X) (u : M → Option X → M) (z : Z) : Option M → X → Option M
  | none, _ => none
  | some m, v => if (rl m z).isSome ∧ rl m z ≠ some v then none else some (u m (some v))

/-- **The mode after a call**: a sponge call keeps the memory; a read of `h` moves it by its
policy (`stepRd`), or kills the mode if the outcome is `none` or contradicts the log. -/
def nxD (rl : M → Z → Option X) :
    Option M → (i : (hwSpec X Z M).Port) → (hwSpec X Z M).Result i → Option M
  | none, _, _ => none
  | some m, .inl (.inl _), _ => some m
  | some m, .inl (.inr (.readH z upd)), r => r.1.elim none (stepRd rl upd z (some m))
  | some m, .inl (.inr (.readK _ upd)), r => some (upd m r.1)
  | some m, .inl (.inr (.readK' _ upd)), r => some (upd m r.1)
  | some m, .inr _, _ => some m

/-- **The calls a live mode allows**: sponge calls and reads of `h` logging their outcome. -/
def OkD (rl : M → Z → Option X) : Option M → (hwSpec X Z M).Port → Prop
  | none, _ => True
  | some _, .inl (.inl _) => True
  | some _, .inl (.inr (.readH z upd)) => RecordsAt rl z upd
  | some _, _ => False

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M] in
theorem mem_dInv_none (rl : M → Z → Option X) (s : HwReg X Z M) : s ∉ DInv rl none :=
  fun h ↦ h

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem hwEmpty_fst_apply (z : Z) : (hwEmpty X Z).1 z = none :=
  rfl

/-- On an operator supported on the event, the event projector next to the identity acts as the
identity. -/
theorem conj_one_kronecker_hwProjector_of_supp {A : Type} [Fintype A] [DecidableEq A]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    {σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (h : QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) E σ) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwProjector E) σ = σ := by
  have hP : (1 : Matrix A A ℂ) ⊗ₖ hwProjector E =
      diagonal fun y : A × HwReg X Z M ↦ if y.2 ∈ E then (1 : ℂ) else 0 := by
    rw [hwProjector, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal]
    congr 1
    funext y
    by_cases hy : y.2 ∈ E <;> simp [hy]
  rw [MatrixMap.conj_apply, hP, diagonal_conjTranspose]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : σ a b = 0
  · rw [hab]
    simp
  · obtain ⟨ha, hb⟩ := h a b hab
    simp [ha, hb]

/-- **An operator supported off the event has no weight in it.** -/
theorem potential_eq_zero_of_supp {A : Type} [Fintype A] [DecidableEq A]
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)]
    {σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (h : QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) Eᶜ σ) :
    potential (hwProjector E) σ = 0 := by
  have hP : (1 : Matrix A A ℂ) ⊗ₖ hwProjector E =
      diagonal fun y : A × HwReg X Z M ↦ if y.2 ∈ E then (1 : ℂ) else 0 := by
    rw [hwProjector, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal]
    congr 1
    funext y
    by_cases hy : y.2 ∈ E <;> simp [hy]
  have h0 : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ hwProjector E) σ = 0 := by
    rw [MatrixMap.conj_apply, hP, diagonal_conjTranspose]
    ext a b
    rw [mul_diagonal, diagonal_mul]
    by_cases hab : σ a b = 0
    · rw [hab]
      simp
    · obtain ⟨ha, -⟩ := h a b hab
      simp [show a.2 ∉ E from ha]
  rw [potential, MatrixMap.amplifyLeft_conj, h0, Matrix.trace_zero, Complex.zero_re,
    ENNReal.ofReal_zero]

variable [Nonempty X] [Nonempty Z]

/-- **A decompressed read of `h`**: the memory before is the outcome's, the databases and the
hardwired cells stay, the memory moves by the policy, and the outcome is the cell's value. -/
theorem readH_dec_ne_zero (z : Z) (upd : M → Option X → M) (r : Option X × M)
    (m' m : Unit × HwReg X Z M)
    (h : (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M)) m' m ≠ 0) :
    m.2.2.2 = r.2 ∧ m'.2.1 = m.2.1 ∧ m'.2.2.1 = m.2.2.1 ∧ m'.2.2.2 = upd r.2 r.1 ∧
      (m.2.2.1.1 z).or (m.2.1.1 z) = r.1 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    readKrausH, kron_one_mul_clsKraus_mul_kron_one] at h
  have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) h).2
  rw [clsKraus_apply] at h'
  split_ifs at h' with hc
  · rw [← one_kronecker_one] at h'
    obtain ⟨h₁, h₂, h₃⟩ := dbs_dec_ne_zero h'
    obtain ⟨e₁, e₂⟩ := cellRead_dec_ne_zero h₁
    have e₃ := one_dec_ne_zero h₂
    have e₄ := one_dec_ne_zero h₃
    obtain ⟨hm, hm'⟩ := hc
    refine ⟨hm, Prod.ext e₁ (Prod.ext e₃ e₄), by rw [hm'], by rw [hm'], e₂⟩
  · exact absurd rfl h'

variable [AddCommGroup X] [AddCommGroup Z]

variable (X Z) in
/-- **Runtime 2 in the decompressed basis**: every branch conjugated by the compression. -/
noncomputable abbrev decR2 (m₀ : M) : QuantumRuntime (hwSpec X Z M) :=
  conjReg (runtime2 X Z m₀) (compressReg X Z M) compressReg_mul_self conjTranspose_compressReg

theorem decR2_branch_apply (m₀ : M) (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i)
    (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M) ((hwSpec X Z M).In i × HwReg X Z M) ℂ) :
    ((decR2 X Z m₀).step i).branch r σ = MatrixMap.conj
      (((1 : Matrix ((hwSpec X Z M).Out i) ((hwSpec X Z M).Out i) ℂ) ⊗ₖ compressReg X Z M) *
        kraus2 X Z m₀ i r *
        ((1 : Matrix ((hwSpec X Z M).In i) ((hwSpec X Z M).In i) ℂ) ⊗ₖ compressReg X Z M)) σ := by
  rw [conjReg_branch, runtime2_branch, MatrixMap.conj_mul, MatrixMap.conj_mul]
  rfl

omit [Nonempty X] [Nonempty Z] in
/-- A decompressed sponge port keeps the whole register. -/
theorem hwPort_dec_ne_zero {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read : HwReg X Z M → A → Y) (m' m : (A × Y) × HwReg X Z M)
    (h : (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) * hwPort read *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M)) m' m ≠ 0) :
    m'.2 = m.2 := by
  rw [one_kron_mul_hwPort_mul_one_kron, tableOracle_apply] at h
  split_ifs at h with he
  · rw [he]
    rfl
  · exact absurd rfl h

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
/-- **The compression keeps the hardwired cells and the memory**: a support read through them
passes between the bases. -/
theorem querySupportedOn_conj_compressReg {A : Type} [Fintype A] [DecidableEq A]
    {S : Set (HwReg X Z M)} (hS : ∀ s s' : HwReg X Z M, s.2 = s'.2 → s ∈ S → s' ∈ S)
    {σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (h : QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) S σ) :
    QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) S
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M) σ) := by
  refine QuerySupportedOn.conj h fun m' m hK hm ↦ ?_
  have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
  rw [compressReg, kroneckerMap_apply] at hK'
  have h₂ := right_ne_zero_of_mul hK'
  rw [Matrix.one_apply] at h₂
  split_ifs at h₂ with he
  · exact hS _ _ he.symm hm
  · exact absurd rfl h₂

omit [Nonempty X] [Nonempty Z] in
/-- The compression is an involution on the operators of the register. -/
theorem conj_compressReg_conj_compressReg {A : Type} [Fintype A] [DecidableEq A]
    (σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) :
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M)
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M) σ) = σ := by
  have h : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M) ∘ₗ
      MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M) = LinearMap.id := by
    rw [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self,
      one_kronecker_one, MatrixMap.conj_one]
  exact LinearMap.congr_fun h σ

/-- **Every allowed step keeps the decompressed invariant of its mode.** -/
theorem decR2_step_dInv (rl : M → Z → Option X) (m₀ : M) (μ : Option M)
    (i : (hwSpec X Z M).Port) (r : (hwSpec X Z M).Result i)
    (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M) ((hwSpec X Z M).In i × HwReg X Z M) ℂ)
    (hi : OkD rl μ i)
    (hσ : QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (DInv rl μ) σ) :
    QuerySupportedOn (fun m : (hwSpec X Z M).Out i × HwReg X Z M ↦ m.2)
      (DInv rl (nxD rl μ i r)) (((decR2 X Z m₀).step i).branch r σ) := by
  rw [decR2_branch_apply]
  refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
  rcases μ with _ | m₁
  · exact absurd hm (mem_dInv_none rl _)
  rcases i with (p | c) | c
  · have he : m'.2 = m.2 := by
      cases p <;> exact hwPort_dec_ne_zero _ m' m hK
    rw [he]
    exact hm
  · cases c with
    | readH z upd =>
      obtain ⟨hr, hD, hW, hM, ho⟩ := readH_dec_ne_zero z upd r m' m hK
      obtain ⟨hm₁, hmW, hnb, hrl⟩ := hm
      rw [hmW, hwEmpty_fst_apply, Option.none_or] at ho
      rcases hr1 : r.1 with _ | v
      · rw [hr1] at ho
        exact absurd (hnb.1 z) (by rw [ho]; simp)
      change m'.2 ∈ DInv rl (r.1.elim none (stepRd rl upd z (some m₁)))
      rw [hr1, Option.elim_some]
      rw [hr1] at ho hM
      by_cases hbad : (rl m₁ z).isSome ∧ rl m₁ z ≠ some v
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hbad.1
        exact absurd ((hx.trans (hrl z x hx).symm).trans ho) hbad.2
      · change m'.2 ∈ DInv rl (if (rl m₁ z).isSome ∧ rl m₁ z ≠ some v then none
          else some (upd m₁ (some v)))
        simp only [hbad, ↓reduceIte]
        refine ⟨by rw [hM, ← hr, hm₁], by rw [hW, hmW], ?_, fun z' x hx ↦ ?_⟩
        · change NoBotDb m'.2.1
          rw [hD]
          exact hnb
        · rw [hi, Function.update_apply] at hx
          rw [hD]
          split_ifs at hx with hz
          · subst hz
            exact ho.trans hx
          · exact hrl z' x hx
    | readK _ _ => exact absurd hi id
    | readK' _ _ => exact absurd hi id
  · exact absurd hi id

/-- The start of runtime 2 is supported on the start register. -/
theorem querySupportedOn_init (m₀ : M) {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) :
    QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2)
      {((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)}
      (ρ ⊗ₖ (runtime2 X Z m₀).init.matrix) := by
  intro m m' hm
  change (ρ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty X Z, m₀) : HwReg X Z M)).matrix) m m' ≠ 0 at hm
  rw [SubState.matrix_basis, kroneckerMap_apply] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · exact ⟨he.1.symm, he.2.symm⟩
  · exact absurd rfl h

/-- **The decompressed initial operator** is supported on the invariant of the initial memory
when its log is empty. -/
theorem dInv_init (rl : M → Z → Option X) (m₀ : M) (hrl : ∀ z, rl m₀ z = none) {A : Type}
    [Fintype A] [DecidableEq A] (ρ : Matrix A A ℂ) :
    QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) (DInv rl (some m₀))
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M)
        (ρ ⊗ₖ (runtime2 X Z m₀).init.matrix)) := by
  have h0 := querySupportedOn_init (X := X) (Z := Z) m₀ ρ
  refine QuerySupportedOn.conj h0 fun m' m hK hm ↦ ?_
  have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
  rw [Set.mem_singleton_iff] at hm
  rw [hm, compressReg, kroneckerMap_apply, compressDbs, kroneckerMap_apply,
    kroneckerMap_apply] at hK'
  have hall : ∀ {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
      (D : Database A Y), compressAll A Y D Database.empty ≠ 0 → ∀ a, (D a).isSome := by
    intro A Y _ _ _ _ D hD a
    rw [compressAll_apply_empty] at hD
    split_ifs at hD with h
    · exact Option.isSome_iff_ne_none.mpr (h a)
    · exact absurd rfl hD
  have h₁ := left_ne_zero_of_mul hK'
  have h₂ := right_ne_zero_of_mul hK'
  rw [Matrix.one_apply] at h₂
  split_ifs at h₂ with hWm
  · refine ⟨congrArg Prod.snd hWm, congrArg Prod.fst hWm,
      ⟨hall _ (left_ne_zero_of_mul h₁), hall _ (left_ne_zero_of_mul (right_ne_zero_of_mul h₁)),
        hall _ (right_ne_zero_of_mul (right_ne_zero_of_mul h₁))⟩, fun z x hx ↦ ?_⟩
    rw [hrl z] at hx
    exact absurd hx (by simp)
  · exact absurd rfl h₂

variable {Mode : Type} (rl : M → Z → Option X) (proj : Mode → Option M)
  {ok : Mode → (hwSpec X Z M).Port → Prop}
  {nx : Mode → (i : (hwSpec X Z M).Port) → (hwSpec X Z M).Result i → Mode}

/-- **A win is in the event.** Let a program be moded from a mode of memory `m₀` with an empty
log, its modes projecting (`proj`) on the decompressed modes of `nxD`, and let every leaf
returning `true` be reached in a mode whose memory is in `Won`. If the event contains every
register whose memory is in `Won`, the probability of `true` is at most the event weight. -/
theorem evalDistMap_le_eventWeight_moded (m₀ : M) (hrl : ∀ z, rl m₀ z = none)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    (E : Set (HwReg X Z M)) [DecidablePred (· ∈ E)] (Won : Set M)
    (hE : ∀ s : HwReg X Z M, s.2.2 ∈ Won → s ∈ E)
    {fin : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → Mode → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M)
      (QuantumComp₂.Leaf (QReg.of Unit) Bool) (QReg.of Unit)) (μ₀ : Mode)
    (hμ₀ : proj μ₀ = some m₀) (hx : ModedP ok nx fin μ₀ x)
    (hfin : ∀ p μ, fin p μ → p.2.2 = true → ∀ m, proj μ = some m → m ∈ Won) :
    (runtime2 X Z m₀).evalDistMap .instruments x (SubState.basis ()) (fun p ↦ p.2.2) {true} ≤
      (runtime2 X Z m₀).eventWeight .instruments (hwProjector E) x
        ((SubState.basis ()).matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) := by
  set ρ := (SubState.basis ()).matrix ⊗ₖ (runtime2 X Z m₀).init.matrix with hρ
  have hdec := querySupportedOn_run_moded (decR2 X Z m₀) .instruments
    (fun μ ↦ DInv rl (proj μ)) (fun μ i r σ hi hσ ↦ by
      rw [hnx μ i r hi]
      exact decR2_step_dInv rl m₀ (proj μ) i r σ (hok μ i hi) hσ) x μ₀ hx
    (ρ := MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ compressReg X Z M) ρ)
    (by rw [hμ₀]; exact dInv_init rl m₀ hrl _)
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true),
    QuantumRuntime.eventWeight]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [QuantumRuntime.matrix_jointPost]
  by_cases hp : p.2.2 = true
  · rw [Set.indicator_of_mem (by exact hp), Pi.one_apply, mul_one]
    have h1 := hdec p
    rw [run_conjReg] at h1
    have h2 := querySupportedOn_conj_compressReg (S := {d | d.2.2 ∈ Won}) (fun s s' he hs ↦ by
      change s'.2.2 ∈ Won
      rw [← he]
      exact hs) (h1.imp fun d ⟨μ, hμ, hd⟩ ↦ by
        rcases hpm : proj μ with _ | m
        · rw [hpm] at hd
          exact absurd hd (mem_dInv_none rl d.2)
        · rw [hpm] at hd
          change d.2.2.2 ∈ Won
          rw [hd.1]
          exact hfin p μ hμ hp m hpm)
    rw [conj_compressReg_conj_compressReg] at h2
    rw [conj_one_kronecker_hwProjector_of_supp E (h2.imp fun d hd ↦ hE d.2 hd)]
  · rw [Set.indicator_of_notMem (by simpa using hp), mul_zero]
    exact zero_le

/-- **The decompressed invariant at every call**: every call of a moded program run in runtime 2
is presented an operator whose input, decompressed, is supported on the invariant of a mode
allowing the call (so no hardwired cell, no decompressed `⊥`, and the log held). -/
theorem forallQueries_runtime2_dInv (m₀ : M) (hrl : ∀ z, rl m₀ z = none)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Mode → Prop} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (hwSpec X Z M) Ω A) (μ₀ : Mode)
    (hμ₀ : proj μ₀ = some m₀) (hx : ModedP ok nx fin μ₀ x) (ρ : Matrix A A ℂ) :
    (runtime2 X Z m₀).ForallQueries .instruments (fun i E τ ↦ ∃ μ, ok μ i ∧
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (DInv rl (proj μ))
        (MatrixMap.conj ((1 : Matrix ((hwSpec X Z M).In i) ((hwSpec X Z M).In i) ℂ) ⊗ₖ
          compressReg X Z M) (MatrixMap.traceRight _ E τ))) x
      (ρ ⊗ₖ (runtime2 X Z m₀).init.matrix) := by
  have h1 := forallQueries_of_modedP_sguard (decR2 X Z m₀) .instruments
    (fun μ ↦ DInv rl (proj μ)) (fun _ ↦ Set.univ) (fun μ i r σ hi hσ ↦ by
      rw [hnx μ i r hi]
      exact decR2_step_dInv rl m₀ (proj μ) i r σ (hok μ i hi)
        (hσ.mono Set.inter_subset_left)) x μ₀ hx
    (ρ := MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M)
      (ρ ⊗ₖ (runtime2 X Z m₀).init.matrix))
    (Quantum.Xmss.Hybrid.forallQueries_of_forall _ _ (fun _ _ _ ↦ querySupportedOn_univ _ _) _ _)
    (by rw [hμ₀]; exact dInv_init rl m₀ hrl ρ)
  have hsim : ∀ i r, ((runtime2 X Z m₀).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg X Z M)).amplifyLeft ((hwSpec X Z M).In i) =
      (MatrixMap.conj (compressReg X Z M)).amplifyLeft ((hwSpec X Z M).Out i) ∘ₗ
        ((decR2 X Z m₀).step i).branch r := by
    intro i r
    rw [conjReg_branch, MatrixMap.amplifyLeft_conj]
    refine LinearMap.ext fun τ ↦ ?_
    simp only [LinearMap.comp_apply]
    rw [conj_compressReg_conj_compressReg]
  have h2 := QuantumRuntime.ForallQueries.of_simulation .instruments (R₁ := decR2 X Z m₀)
    (R₂ := runtime2 X Z m₀) (V := MatrixMap.conj (compressReg X Z M)) hsim
    (P₂ := fun i E τ ↦ ∃ μ, ok μ i ∧
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (DInv rl (proj μ))
        (MatrixMap.conj ((1 : Matrix ((hwSpec X Z M).In i) ((hwSpec X Z M).In i) ℂ) ⊗ₖ
          compressReg X Z M) (MatrixMap.traceRight _ E τ)))
    (fun i E τ hτ ↦ by
      obtain ⟨μ, hi, hτ⟩ := hτ
      refine ⟨μ, hi, ?_⟩
      have e := LinearMap.congr_fun (MatrixMap.traceRight_comp_amplify (R := E)
        ((MatrixMap.conj (compressReg X Z M)).amplifyLeft ((hwSpec X Z M).In i))) τ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
      rw [e, MatrixMap.amplifyLeft_conj, conj_compressReg_conj_compressReg]
      exact Quantum.Xmss.Assembly.querySupportedOn_traceRight hτ) h1
  rwa [MatrixMap.amplifyLeft_conj, conj_compressReg_conj_compressReg] at h2

end dec

/-! ## Reads invisible on the support -/

section suppRead

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]

omit [AddCommGroup X] [AddCommGroup Z] [Fintype M] in
/-- **A transition of a read of `h`** changes only the database at the read cell, and moves the
memory by the policy with the outcome. -/
theorem hwReadKraus_readH_ne_zero (z : Z) (u : M → Option X → M) (r : Option X × M)
    {q' q : Unit × HwReg X Z M} (h : hwReadKraus (.readH z u) r q' q ≠ 0) :
    (∀ b, b ≠ z → q'.2.1.1 b = q.2.1.1 b) ∧ q'.2.1.2 = q.2.1.2 ∧ q'.2.2.1 = q.2.2.1 ∧
      q'.2.2.2 = u q.2.2.2 r.1 := by
  change ((1 : Matrix Unit Unit ℂ) ⊗ₖ Quantum.Sponge.readKrausH z u r) q' q ≠ 0 at h
  rw [kroneckerMap_apply] at h
  have h2 := right_ne_zero_of_mul h
  obtain ⟨hc, hk, hW⟩ := Quantum.Xmss.Assembly.readKrausH_ne_zero_rest z u r h2
  refine ⟨hc, hk, hW, ?_⟩
  rw [Quantum.Sponge.readKrausH, Quantum.Sponge.clsKraus_apply] at h2
  split_ifs at h2 with hcond
  · rw [hcond.2, hcond.1]
  · exact absurd rfl h2

/-- **A read invisible on the support costs nothing**: if no transition of the read from a
register of `T` crosses the event, the read adds no weight to an input supported on `T`. -/
theorem tsum_potential_hwReadKraus_le_of_supp (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (c : HwRead X Z M) (T : Set (HwReg X Z M))
    (hT : ∀ r (q' q : Unit × HwReg X Z M), hwReadKraus c r q' q ≠ 0 → q.2 ∈ T →
      (q'.2 ∈ S ↔ q.2 ∈ S))
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z M ↦ m.2) T σ) :
    ∑' r, potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (hwProjector S) σ := by
  have hcomm : ∀ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * hwReadKraus c r * σ =
      hwReadKraus c r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * σ := by
    intro r
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Quantum.Sponge.one_kronecker_hwProjector]
    ext q' b
    simp only [Quantum.Sponge.indProj]
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Matrix.diagonal_mul]
    by_cases hk : hwReadKraus c r q' a = 0
    · rw [hk]
      ring
    by_cases hs : σ a b = 0
    · rw [hs]
      ring
    have hind : Quantum.Sponge.ind (Quantum.Sponge.liftSet S) q' =
        Quantum.Sponge.ind (Quantum.Sponge.liftSet S) a := by
      simp only [Quantum.Sponge.ind, Quantum.Sponge.mem_liftSet, hT r q' a hk (hsupp a b hs).1]
    rw [hind]
    ring
  have hF : (∑ r, (hwReadKraus c r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) *
      hwReadKraus c r - (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * σ = 0 := by
    have hr : ∀ r, (hwReadKraus c r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) *
        hwReadKraus c r * σ = (hwReadKraus c r)ᴴ * hwReadKraus c r *
          (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * σ) := fun r ↦ by
      calc (hwReadKraus c r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) *
            hwReadKraus c r * σ
          = (hwReadKraus c r)ᴴ * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) *
            hwReadKraus c r * σ) := by simp only [Matrix.mul_assoc]
        _ = (hwReadKraus c r)ᴴ * (hwReadKraus c r *
            ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * σ) := by rw [hcomm r]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Finset.sum_mul]
    simp_rw [hr]
    rw [← Finset.sum_mul, Quantum.Sponge.sum_hwReadKraus, Matrix.one_mul, sub_self]
  have h := Quantum.Sponge.potential_hwReadKraus_le S (fun _ ↦ 0) (fun _ ↦ by simp)
    (fun _ ↦ by simp) c σ hσ
  have hc : Quantum.Sponge.flipCost S (hwReadKraus c) 0 σ = 0 := by
    simp only [Quantum.Sponge.flipCost, sub_zero, Matrix.mul_one, Matrix.one_mul, hF,
      Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero, zero_add,
      mul_zero]
    simp
  rwa [hc, add_zero] at h

end suppRead

/-! ## Moded programs: generic facts -/

section generic

variable {spec spec' : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  {Mode : Type}

open Quantum.Xmss.Assembly (modeCmdOk modeCmdNx modedP_bind)

/-- A moded program with a weaker final predicate. -/
theorem modedP_mono {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode}
    {fin fin' : (Σ u, Ω u) → Mode → Prop} (hf : ∀ p μ, fin p μ → fin' p μ) {A : QReg}
    (x : QuantumComp L spec Ω A) : ∀ μ, ModedP ok nx fin μ x → ModedP ok nx fin' μ x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun μ h ↦ hf _ μ h
  | liftBind _ c next ih => exact fun μ h ↦ ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- **From a dead mode** (allowing every call, kept by every call) every program is moded. -/
theorem modedP_of_dead {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {fin : (Σ u, Ω u) → Mode → Prop}
    (d : Mode) (hok : ∀ i, ok d i) (hnx : ∀ i r, nx d i r = d) (hfin : ∀ p, fin p d) {A : QReg}
    (x : QuantumComp L spec Ω A) : ModedP ok nx fin d x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact hfin _
  | liftBind _ c next ih =>
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b⟩
    · refine ⟨hok i, fun b ↦ ?_⟩
      change ModedP ok nx fin (nx d i b.down) (next b)
      rw [hnx]
      exact ih b

/-- **Moded substitution**: if every allowed command's tree is moded, ending in the mode the
command moves to or in a dead mode, the substituted program of a moded program is moded. -/
theorem modedP_substitute {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {ok' : Mode → spec'.Port → Prop}
    {nx' : Mode → (i : spec'.Port) → spec'.Result i → Mode}
    (h : CommandSubstitution (QuantumComp.toIPFunctor L spec) (QuantumComp.toIPFunctor L spec'))
    (d : Mode) (hok : ∀ i, ok' d i) (hnx : ∀ i r, nx' d i r = d)
    (hh : ∀ (A : QReg) (c : QuantumComp.Cmd L spec A) μ, modeCmdOk ok c μ →
      ModedP ok' nx' (fun p μ' ↦ μ' = modeCmdNx nx c μ p.2.1 ∨ μ' = d) μ (h A c))
    {fin : (Σ u, Ω u) → Mode → Prop} (hfin : ∀ p, fin p d) {A : QReg}
    (x : QuantumComp L spec Ω A) :
    ∀ μ, ModedP ok nx fin μ x → ModedP ok' nx' fin μ (x.substitute h) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun μ hx ↦ hx
  | liftBind A c next ih =>
    intro μ hx
    rw [IFreeM.substitute_liftBind]
    refine modedP_bind _ _ (hh A c μ hx.1) fun u p μ' hμ' ↦ ?_
    obtain ⟨b, e⟩ := p
    subst e
    rcases hμ' with h | h <;> rw [h]
    · exact ih b _ (hx.2 b)
    · exact modedP_of_dead d hok hnx hfin _

/-- **From a doomed mode**: if doom persists along allowed calls, the leaves of a moded program
from a doomed mode are reached in doomed modes. -/
theorem modedP_doom {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {fin : (Σ u, Ω u) → Mode → Prop}
    (doom : Mode → Prop) (hdoom : ∀ μ i r, ok μ i → doom μ → doom (nx μ i r)) {A : QReg}
    (x : QuantumComp L spec Ω A) :
    ∀ μ, doom μ → ModedP ok nx fin μ x → ModedP ok nx (fun p μ' ↦ fin p μ' ∧ doom μ') μ x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun μ hd h ↦ ⟨h, hd⟩
  | liftBind _ c next ih =>
    intro μ hd h
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b μ hd (h.2 b)⟩
    · exact ⟨h.1, fun b ↦ ih b _ (hdoom μ i b.down h.1 hd) (h.2 b)⟩

end generic

/-! ## The graded event bound along a moded program of runtime 2 -/

section sqrtModed

open Quantum.Xmss.Assembly (modeCmdOk modeCmdNx)

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {M : Type} [Fintype M] [DecidableEq M]
  {Mode : Type} (rl : M → Z → Option X) (proj : Mode → Option M)
  {ok : Mode → (hwSpec X Z M).Port → Prop}
  {nx : Mode → (i : (hwSpec X Z M).Port) → (hwSpec X Z M).Result i → Mode}

/-- An operator supported, in the decompressed basis, on the invariant of the mode `μ`. -/
def DSupp {A : Type} [Fintype A] [DecidableEq A] (μ : Mode)
    (ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ) : Prop :=
  QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) (DInv rl (proj μ))
    (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M) ρ)

theorem decR2_intertwines (m₀ : M) (i : (hwSpec X Z M).Port) :
    DSubInstrument.Intertwines
      ((MatrixMap.conj (compressReg X Z M)).amplifyLeft ((hwSpec X Z M).In i))
      (fun _ ↦ (MatrixMap.conj (compressReg X Z M)).amplifyLeft ((hwSpec X Z M).Out i))
      ((runtime2 X Z m₀).step i) ((decR2 X Z m₀).step i) := by
  intro r
  rw [conjReg_branch, MatrixMap.amplifyLeft_conj]
  refine LinearMap.ext fun τ ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [conj_compressReg_conj_compressReg]

variable {rl proj}

theorem dSupp_queryStep (m₀ : M)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    {A : QReg} {μ : Mode} {i : (hwSpec X Z M).Port} (hi : ok μ i) (E : QReg)
    (ℓ : A ≃ (hwSpec X Z M).In i × E) (r : (hwSpec X Z M).Result i)
    {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ} (hρ : DSupp rl proj μ ρ) :
    DSupp rl proj (nx μ i r) (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ) := by
  unfold DSupp at hρ ⊢
  have e := LinearMap.congr_fun (intertwines_queryStep (R₁ := runtime2 X Z m₀)
    (R₂ := decR2 X Z m₀) (decR2_intertwines m₀ i) E ℓ r) ρ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_conj,
    MatrixMap.amplifyLeft_conj] at e
  rw [← e]
  exact querySupportedOn_queryStep_moded (decR2 X Z m₀) (fun μ ↦ DInv rl (proj μ))
    (fun μ i r σ hi hσ ↦ by
      rw [hnx μ i r hi]
      exact decR2_step_dInv rl m₀ (proj μ) i r σ (hok μ i hi) hσ) hi E ℓ r hρ

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem dSupp_frame {L : LocalSig.{u, v}} {A : QReg} (o : L.Op A) (I : L.Interp) (b : L.Outcome o)
    {μ : Mode} {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ} (hρ : DSupp rl proj μ ρ) :
    DSupp rl proj μ (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ) := by
  unfold DSupp at hρ ⊢
  have e := LinearMap.congr_fun (MatrixMap.amplify_comp_amplifyLeft ((I o).branch b)
    (MatrixMap.conj (compressReg X Z M))) ρ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_conj,
    MatrixMap.amplifyLeft_conj] at e
  change QuerySupportedOn _ _ (MatrixMap.conj _ (((I o).branch b).amplify _ ρ))
  rw [← e]
  exact QuerySupportedOn.amplify_snd (q := fun s ↦ s ∈ DInv rl (proj μ)) (S := {True})
    (hρ.imp fun m hm ↦ by simpa using hm) _ |>.imp fun m hm ↦ by simpa using hm

omit [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z] in
theorem dSupp_callInput {A J E : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    [Fintype E] [DecidableEq E] (ℓ : A ≃ J × E) {μ : Mode}
    {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ} (hρ : DSupp rl proj μ ρ) :
    DSupp rl proj μ (callInput ℓ (HwReg X Z M) ρ) := by
  unfold DSupp at hρ ⊢
  have e := callInput_amplifyLeft (MatrixMap.conj (compressReg X Z M)) ℓ ρ
  rw [MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj] at e
  rw [← e]
  exact QuerySupportedOn.callInput (g := fun s ↦ s) hρ ℓ

omit [Nonempty X] [Nonempty Z] in
/-- **The memory and the hardwired cells of a decompressed support**: an operator supported, in
the decompressed basis, on the invariant of a live mode is supported on its memory and on no
hardwired cell. -/
theorem querySupportedOn_of_dSupp {A : Type} [Fintype A] [DecidableEq A] {μ : Mode} {m : M}
    (hμ : proj μ = some m) {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (hρ : DSupp rl proj μ ρ) :
    QuerySupportedOn (fun q : A × HwReg X Z M ↦ q.2) {s | s.2.2 = m ∧ s.2.1 = hwEmpty X Z} ρ := by
  unfold DSupp at hρ
  rw [hμ] at hρ
  have h := querySupportedOn_conj_compressReg (S := {s | s.2.2 = m ∧ s.2.1 = hwEmpty X Z})
    (fun s s' he hs ↦ ⟨he ▸ hs.1, he ▸ hs.2⟩)
    (hρ.imp fun s hs ↦ ⟨hs.1, hs.2.1⟩)
  rwa [conj_compressReg_conj_compressReg] at h

/-- **No decompressed `⊥` at any read** of an operator with a decompressed support. -/
theorem readNoBot_of_dSupp {μ : Mode} {m : M} (hμ : proj μ = some m)
    {ρ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hρ : DSupp rl proj μ ρ)
    (c : HwRead X Z M) : ReadNoBot c ρ := by
  unfold DSupp at hρ
  rw [hμ] at hρ
  exact readNoBot_of_noBot c (hρ.imp fun s hs ↦ hs.2.2.1)

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] [Fintype M] [DecidableEq M] in
theorem eq_zero_of_querySupportedOn_empty {α β : Type} {q : α → β} {σ : Matrix α α ℂ}
    (h : QuerySupportedOn q ∅ σ) : σ = 0 := by
  ext a b
  by_contra hab
  exact (h a b hab).1

/-- **Doomed modes have no weight**: from a doomed mode whose leaves are dead, every branch of a
moded program is zero. -/
theorem branch_eq_zero_of_doom (m₀ : M)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    (doom : Mode → Prop) (hdoom : ∀ μ i r, ok μ i → doom μ → doom (nx μ i r))
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Mode → Prop}
    (hfin : ∀ p μ, fin p μ → doom μ → proj μ = none) {L : LocalSig.{u, v}} (I : L.Interp)
    {A : QReg} (x : QuantumComp L (hwSpec X Z M) Ω A) (μ : Mode) (hd : doom μ)
    (hx : ModedP ok nx fin μ x) {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (hρ : DSupp rl proj μ ρ) (p : Σ u, Ω u) : ((runtime2 X Z m₀).run I x).branch p ρ = 0 := by
  have h := querySupportedOn_run_moded (decR2 X Z m₀) I (fun μ ↦ DInv rl (proj μ))
    (fun μ i r σ hi hσ ↦ by
      rw [hnx μ i r hi]
      exact decR2_step_dInv rl m₀ (proj μ) i r σ (hok μ i hi) hσ) x μ
    (modedP_doom doom hdoom x μ hd hx) hρ p
  rw [run_conjReg] at h
  have h0 : MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ compressReg X Z M)
      (((runtime2 X Z m₀).run I x).branch p ρ) = 0 :=
    eq_zero_of_querySupportedOn_empty (h.imp fun d ⟨μ', ⟨hf, hd'⟩, hd⟩ ↦ by
      rw [hfin p μ' hf hd'] at hd
      exact hd)
  rw [← conj_compressReg_conj_compressReg (((runtime2 X Z m₀).run I x).branch p ρ), h0,
    map_zero]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] [Fintype M] [DecidableEq M] in
/-- A sum over `ℕ` vanishing from `2` on. -/
theorem tsum_nat_two {f : ℕ → ℝ≥0∞} (hf : ∀ j, 2 ≤ j → f j = 0) : ∑' j, f j = f 0 + f 1 := by
  rw [tsum_eq_sum (s := Finset.range 2) fun j hj ↦ hf j (by simp at hj; omega),
    Finset.sum_range_succ, Finset.sum_range_one]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] [Fintype M] [DecidableEq M] in
/-- Two weighted square-root terms add up under a sum. -/
theorem rpow_inv_two_tsum_le_two {K : Type*} {L t P : K → ℝ≥0∞} (a b : ℕ) (ηA ηB T P₀ : ℝ≥0∞)
    (h : ∀ k, L k ^ (2⁻¹ : ℝ) ≤ a * (ηA * t k) ^ (2⁻¹ : ℝ) + b * (ηB * t k) ^ (2⁻¹ : ℝ) +
      P k ^ (2⁻¹ : ℝ)) (hT : ∑' k, t k ≤ T) (hP : ∑' k, P k ≤ P₀) :
    (∑' k, L k) ^ (2⁻¹ : ℝ) ≤ a * (ηA * T) ^ (2⁻¹ : ℝ) + b * (ηB * T) ^ (2⁻¹ : ℝ) +
      P₀ ^ (2⁻¹ : ℝ) := by
  set m : ℕ → K → ℝ≥0∞ := fun j k ↦ if j = 0 then (a : ℝ≥0∞) ^ 2 * (ηA * t k) else
    if j = 1 then (b : ℝ≥0∞) ^ 2 * (ηB * t k) else 0 with hm
  have hm0 : ∀ j, 2 ≤ j → ∀ k, m j k = 0 := fun j hj k ↦ by
    simp only [hm, show j ≠ 0 by omega, show j ≠ 1 by omega, ↓reduceIte]
  have h0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have h2 := rpow_inv_two_tsum_le_of_le_add_tsum (L := L) (t := P) (m := m) fun k ↦ by
    rw [tsum_nat_two (f := fun j ↦ m j k ^ (2⁻¹ : ℝ)) fun j hj ↦ by
      simp only [hm0 j hj k, h0]]
    simp only [hm, ↓reduceIte, one_ne_zero]
    rw [← natCast_mul_rpow_inv_two, ← natCast_mul_rpow_inv_two]
    exact (h k).trans_eq (by ring)
  refine h2.trans ?_
  rw [tsum_nat_two (f := fun j ↦ (∑' k, m j k) ^ (2⁻¹ : ℝ)) fun j hj ↦ by
    simp only [hm0 j hj, tsum_zero, h0]]
  simp only [hm, ↓reduceIte, one_ne_zero, ENNReal.tsum_mul_left]
  rw [← natCast_mul_rpow_inv_two, ← natCast_mul_rpow_inv_two]
  have hA : (a : ℝ≥0∞) * (ηA * ∑' k, t k) ^ (2⁻¹ : ℝ) ≤ a * (ηA * T) ^ (2⁻¹ : ℝ) := by gcongr
  have hB : (b : ℝ≥0∞) * (ηB * ∑' k, t k) ^ (2⁻¹ : ℝ) ≤ b * (ηB * T) ^ (2⁻¹ : ℝ) := by gcongr
  have hP' : (∑' k, P k) ^ (2⁻¹ : ℝ) ≤ P₀ ^ (2⁻¹ : ℝ) := by gcongr
  calc (∑' k, P k) ^ (2⁻¹ : ℝ) + ((a : ℝ≥0∞) * (ηA * ∑' k, t k) ^ (2⁻¹ : ℝ) +
        (b : ℝ≥0∞) * (ηB * ∑' k, t k) ^ (2⁻¹ : ℝ))
      ≤ P₀ ^ (2⁻¹ : ℝ) + (a * (ηA * T) ^ (2⁻¹ : ℝ) + b * (ηB * T) ^ (2⁻¹ : ℝ)) := by gcongr
    _ = _ := by ring

open scoped Classical in
/-- **The graded event bound along a moded program of runtime 2.** The calls of class `A` (port
weights `κA`, at most `nA` along every path) and of class `B` (mode-dependent weights `κB`, paid
from a budget `bud` of the modes) raise the square root of the event weight of their input by
their weight times `√(η tr σ)`; calls into doomed modes need not be paid (doom persists and the
leaves of doomed modes are dead, so they carry no weight). Then
`√w ≤ nA √(ηA tr ρ) + bud μ √(ηB tr ρ) + √(w ρ)`. -/
theorem rpow_inv_two_tsum_potential_runtime2_moded (m₀ : M)
    (hok : ∀ μ i, ok μ i → OkD rl (proj μ) i)
    (hnx : ∀ μ i r, ok μ i → proj (nx μ i r) = nxD rl (proj μ) i r)
    (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] (doom : Mode → Prop)
    (hdoom : ∀ μ i r, ok μ i → doom μ → doom (nx μ i r))
    (κA : (hwSpec X Z M).Port → ℕ) (κB : Mode → (hwSpec X Z M).Port → ℕ) (bud : Mode → ℕ)
    (hbud : ∀ μ i r, ok μ i → ¬doom (nx μ i r) → κB μ i + bud (nx μ i r) ≤ bud μ)
    (ηA ηB : ℝ≥0∞) (CInv : Mode → Set (HwReg X Z M))
    (hC : ∀ μ i r (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M)
        ((hwSpec X Z M).In i × HwReg X Z M) ℂ), ok μ i →
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (CInv μ) σ →
      QuerySupportedOn (fun m : (hwSpec X Z M).Out i × HwReg X Z M ↦ m.2) (CInv (nx μ i r))
        (((runtime2 X Z m₀).step i).branch r σ))
    (hη : ∀ μ i (σ : Matrix ((hwSpec X Z M).In i × HwReg X Z M)
        ((hwSpec X Z M).In i × HwReg X Z M) ℂ), ok μ i → ¬doom μ → σ.PosSemidef →
      DSupp rl proj μ σ →
      QuerySupportedOn (fun m : (hwSpec X Z M).In i × HwReg X Z M ↦ m.2) (CInv μ) σ →
      ∑' r, (if doom (nx μ i r) then 0 else
          potential (hwProjector S) (((runtime2 X Z m₀).step i).branch r σ)) ≤
        (potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
          κA i * (ηA * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
          κB μ i * (ηB * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2)
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Mode → Prop}
    (hfin : ∀ p μ, fin p μ → doom μ → proj μ = none) {L : LocalSig.{u, v}} (I : L.Interp)
    {A : QReg} (x : QuantumComp L (hwSpec X Z M) Ω A) :
    ∀ (nA : ℕ), IFreeM.IsChargeBound x (portCharge κA) nA → ∀ μ, ModedP ok nx fin μ x →
      ∀ {ρ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}, ρ.PosSemidef →
        DSupp rl proj μ ρ → QuerySupportedOn (fun m : A × HwReg X Z M ↦ m.2) (CInv μ) ρ →
        (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
          nA * (ηA * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
            bud μ * (ηB * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
            potential (hwProjector S) ρ ^ (2⁻¹ : ℝ) := by
  classical
  have hzero : ∀ {B : QReg} (y : QuantumComp L (hwSpec X Z M) Ω B) (μ : Mode), doom μ →
      ModedP ok nx fin μ y → ∀ {ρ : Matrix (B × HwReg X Z M) (B × HwReg X Z M) ℂ},
        DSupp rl proj μ ρ →
        ∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I y).branch p ρ) = 0 := by
    intro B y μ hd hy ρ hρ
    refine ENNReal.tsum_eq_zero.mpr fun p ↦ ?_
    rw [branch_eq_zero_of_doom m₀ hok hnx doom hdoom hfin I y μ hd hy hρ p]
    simp [potential]
  induction x using QuantumComp.inductionOn with
  | pure B y =>
    intro nA _ μ _ ρ _ _ _
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Ω u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_add_left le_rfl
  | primBind B o k ih =>
    intro nA hxA μ hx ρ hρ hs hcs
    by_cases hd : doom μ
    · rw [hzero _ μ hd hx hs, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    have hρb := fun b ↦ ((I o).frame (QReg.of (HwReg X Z M))).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential (hwProjector S) (((runtime2 X Z m₀).run I
        (QuantumComp.primBind o k)).branch p ρ) = ∑' b, potential (hwProjector S)
          (((runtime2 X Z m₀).run I (k b)).branch p
            (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ)) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact Quantum.Sponge.potential_tsum _ ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ ((runtime2 X Z m₀).run I (k b)).isCPTNIFamily) p).summable_apply ρ)
        fun b ↦ ((runtime2 X Z m₀).run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hxA
    have hch : ∀ b, (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I (k b)).branch p
        (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ))) ^ (2⁻¹ : ℝ) ≤
        nA * (ηA * ENNReal.ofReal
          (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ).trace.re) ^ (2⁻¹ : ℝ) +
        bud μ * (ηB * ENNReal.ofReal
          (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ).trace.re) ^ (2⁻¹ : ℝ) +
        potential (hwProjector S)
          (((I o).frame (QReg.of (HwReg X Z M))).branch b ρ) ^ (2⁻¹ : ℝ) := fun b ↦ by
      have hxb : ModedP ok nx fin μ (k b) := hx.2 (ULift.up b)
      exact ih b nA (hxA b) μ hxb (hρb b) (dSupp_frame o I b hs)
        (QuerySupportedOn.amplify_snd (q := id) hcs _)
    exact rpow_inv_two_tsum_le_two nA (bud μ) ηA ηB _ _ hch
      (((I o).frame _).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)
      (tsum_potential_frame_le _ (I o) hρ)
  | queryBind B i E ℓ k ih =>
    intro nA hxA μ hx ρ hρ hs hcs
    by_cases hd : doom μ
    · rw [hzero _ μ hd hx hs, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    have hρr := fun r ↦ ((runtime2 X Z m₀).queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential (hwProjector S) (((runtime2 X Z m₀).run I
        (QuantumComp.queryBind i E ℓ k)).branch p ρ) = ∑' r, potential (hwProjector S)
          (((runtime2 X Z m₀).run I (k r)).branch p
            (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ)) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact Quantum.Sponge.potential_tsum _
        ((((runtime2 X Z m₀).queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ ((runtime2 X Z m₀).run I (k r)).isCPTNIFamily) p).summable_apply ρ)
        fun r ↦ ((runtime2 X Z m₀).run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hxA
    have hi : ok μ i := hx.1
    have hxr : ∀ r, ModedP ok nx fin (nx μ i r) (k r) := fun r ↦ hx.2 (ULift.up r)
    by_cases hall : ∀ r, doom (nx μ i r)
    · rw [ENNReal.tsum_eq_zero.mpr fun r ↦ hzero (k r) _ (hall r) (hxr r)
        (dSupp_queryStep m₀ hok hnx hi E ℓ r hs), ENNReal.zero_rpow_of_pos (by norm_num)]
      exact zero_le
    obtain ⟨r₀, hr₀⟩ := not_forall.mp hall
    have hB : κB μ i ≤ bud μ := (Nat.le_add_right _ _).trans (hbud μ i r₀ hi hr₀)
    set a := nA - κA i
    set b := bud μ - κB μ i
    set tr : (hwSpec X Z M).Result i → ℝ≥0∞ := fun r ↦
      ENNReal.ofReal (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ).trace.re
    have hchild : ∀ r, (∑' p, potential (hwProjector S) (((runtime2 X Z m₀).run I (k r)).branch p
        (((runtime2 X Z m₀).queryStep i E ℓ).branch r ρ))) ^ (2⁻¹ : ℝ) ≤
        a * (ηA * tr r) ^ (2⁻¹ : ℝ) + b * (ηB * tr r) ^ (2⁻¹ : ℝ) +
          (if doom (nx μ i r) then 0 else potential (hwProjector S)
            (((runtime2 X Z m₀).step i).branch r (callInput ℓ _ ρ))) ^ (2⁻¹ : ℝ) := by
      intro r
      have hsr := dSupp_queryStep m₀ hok hnx hi E ℓ r hs
      by_cases hdr : doom (nx μ i r)
      · rw [hzero (k r) _ hdr (hxr r) hsr, ENNReal.zero_rpow_of_pos (by norm_num)]
        exact zero_le
      simp only [hdr, ↓reduceIte]
      rw [← potential_queryStep (runtime2 X Z m₀) (hwProjector S) i E ℓ r ρ]
      refine (ih r a (hxA.2 r) _ (hxr r) (hρr r) hsr
        (querySupportedOn_queryStep_moded (runtime2 X Z m₀) CInv hC hi E ℓ r hcs)).trans ?_
      have hb : bud (nx μ i r) ≤ b := by
        have := hbud μ i r hi hdr
        omega
      gcongr
    refine (rpow_inv_two_tsum_le_two a b ηA ηB (ENNReal.ofReal ρ.trace.re) _ hchild
      (((runtime2 X Z m₀).queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)
      (hη μ i _ hi hd (posSemidef_callInput ℓ hρ) (dSupp_callInput ℓ hs)
        (QuerySupportedOn.callInput (g := id) hcs ℓ))).trans ?_
    rw [potential_callInput, trace_callInput, Quantum.Xmss.Assembly.pow_two_rpow_inv_two]
    have hnA : (nA : ℝ≥0∞) = κA i + a := by
      rw [← Nat.cast_add]
      exact congrArg _ (by omega)
    have hbud' : (bud μ : ℝ≥0∞) = κB μ i + b := by
      rw [← Nat.cast_add]
      exact congrArg _ (by omega)
    rw [hnA, hbud']
    ring_nf
    exact le_rfl

end sqrtModed

/-! ## Mixed programs as moded programs -/

section mixed

open Quantum.Qrom HashSig

variable {M : Type} {T : Type}

open Quantum.Xmss.Assembly (modeCmdOk modeCmdNx modedP_bind modedP₂_bind modedP_map)

/-- **The mode after a tagged call** of a mixed program: a hash call or a coin keeps it, a hash of
`z` by the tag `c` moves it by `stepRd` with the tag's policy. -/
def nxM (upd : T → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) :
    Option M → (p : (MixSpec T).Port) → (MixSpec T).Result p → Option M
  | μ, .hash _, _ => μ
  | μ, .call (_, .inl _), _ => μ
  | μ, .call (c, .inr z), v => stepRd rl (upd c z) z μ v

/-- Every mixed command is allowed. -/
def okM : Option M → (MixSpec T).Port → Prop := fun _ _ ↦ True

theorem nxD_none (rl : M → HashDomain → Option HashOutput)
    (i : (hwSpec HashOutput HashDomain M).Port) (r : (hwSpec HashOutput HashDomain M).Result i) :
    nxD rl none i r = none :=
  rfl

theorem okD_none (rl : M → HashDomain → Option HashOutput)
    (i : (hwSpec HashOutput HashDomain M).Port) : OkD rl none i :=
  trivial

theorem nxD_readH (rl : M → HashDomain → Option HashOutput) (μ : Option M) (z : HashDomain)
    (u : M → Option HashOutput → M) (r : Option HashOutput × M) :
    nxD rl μ (.inl (.inr (.readH z u))) r = stepRd rl u z μ (r.1.getD 0) ∨
      nxD rl μ (.inl (.inr (.readH z u))) r = none := by
  rcases μ with _ | m
  · exact Or.inr rfl
  rcases r with ⟨_ | v, m'⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem nxD_sponge (rl : M → HashDomain → Option HashOutput) (μ : Option M) (p : SpongePort)
    (r : (hwSpec HashOutput HashDomain M).Result (.inl (.inl p))) :
    nxD rl μ (.inl (.inl p)) r = μ := by
  rcases μ with _ | m <;> rfl

theorem okD_sponge (rl : M → HashDomain → Option HashOutput) (μ : Option M) (p : SpongePort) :
    OkD rl μ (.inl (.inl p)) := by
  rcases μ with _ | m <;> trivial

theorem okD_readH (rl : M → HashDomain → Option HashOutput) (μ : Option M) (z : HashDomain)
    (u : M → Option HashOutput → M) (h : RecordsAt rl z u) :
    OkD rl μ (.inl (.inr (.readH z u))) := by
  rcases μ with _ | m
  · trivial
  · exact h

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

/-- **The read program of a moded mixed program is moded** (in the decompressed modes of `nxD`),
when every tag's policy logs the outcome. -/
theorem modedP_toReads (upd : T → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (hrec : ∀ c z, RecordsAt rl z (upd c z))
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option M → Prop} (hfin : ∀ p, fin p none) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec T)) Ω A)
    (μ : Option M) (hx : ModedP okM (nxM upd rl) fin μ x) :
    ModedP (OkD rl) (nxD rl) fin μ
      (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens (IFreeM.substitute (readSub upd) x)) := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute _ none (okD_none rl) (nxD_none rl) (fun A c μ _ ↦ ?_) hfin x μ hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step
    · trivial
    · exact Or.inl rfl
  · moded_step
    · exact okD_sponge rl μ _
    · exact Or.inl (nxD_sponge rl μ _ _)
  · moded_step
    · trivial
    moded_step
    · trivial
    exact Or.inl rfl
  · moded_step
    · trivial
    moded_step
    · exact okD_readH rl μ z _ (hrec tag z)
    moded_step
    · trivial
    exact nxD_readH rl μ z _ _

end mixed

/-! ## Live runs of the classical algorithms -/

section live

open Quantum.Qrom HashSig OracleComp OracleSpec
open Quantum.Xmss.Assembly (modeCmdOk modeCmdNx modedP_bind modedP₂_bind modedP_map)

variable {M : Type}

/-- **The live semantics of a classical algorithm**: coins answered freely, a hash of `z` answered
by any value `v`, the mode moved by `stepRd` with the policy `u z`. Its support holds every run
of the algorithm's read program that keeps its mode. -/
noncomputable def liveImpl (rl : M → HashDomain → Option HashOutput)
    (u : HashDomain → M → Option HashOutput → M) :
    QueryImpl romWorld.Oracles (StateT (Option M) (OracleComp romWorld.Oracles))
  | .inl n => fun μ ↦ (fun b ↦ (b, μ)) <$> liftM (romWorld.Oracles.query (.inl n))
  | .inr z => fun μ ↦ (fun v ↦ (v, stepRd rl (u z) z μ v)) <$>
      liftM (romWorld.Oracles.query (.inr z))

/-- **The live semantics of a reduction's algorithm** against the challenger `ans`, with its
transcript: its own hash calls by the policy of `.red`, the challenger's answers by that of
`.answer`, logged. -/
noncomputable def liveRed (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M) {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) :
    QueryImpl (romWorld.Oracles + R') (StateT (QueryLog R' × Option M)
      (OracleComp romWorld.Oracles))
  | .inl i => fun s ↦ (fun p ↦ (p.1, (s.1, p.2))) <$> (liveImpl rl (upd .red) i).run s.2
  | .inr q' => fun s ↦ (fun p ↦ (p.1, (s.1 ++ [⟨q', p.1⟩], p.2))) <$>
      (simulateQ (liveImpl rl (upd .answer)) (ans q')).run s.2

/-- A live run of a classical algorithm from the mode `μ`, returning `a` in the mode `μ'`. -/
def LiveRun (rl : M → HashDomain → Option HashOutput) (u : HashDomain → M → Option HashOutput → M)
    {α : Type} (oa : OracleComp romWorld.Oracles α) (μ : Option M) (a : α) (μ' : Option M) :
    Prop :=
  (a, μ') ∈ support ((simulateQ (liveImpl rl u) oa).run μ)

/-- A live run of a reduction's algorithm from the transcript `log` and the mode `μ`, returning
the value and transcript `a` in the mode `μ'`. -/
def LiveRedRun (rl : M → HashDomain → Option HashOutput)
    (upd : Caller → HashDomain → M → Option HashOutput → M) {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    {α : Type} (oa : OracleComp (romWorld.Oracles + R') α) (log : QueryLog R') (μ : Option M)
    (a : α × QueryLog R') (μ' : Option M) : Prop :=
  (a.1, (a.2, μ')) ∈ support ((simulateQ (liveRed rl upd ans) oa).run (log, μ))

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

/-- A tagged call moves the mode by its value. -/
theorem modedP_mixImpl (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (c : Caller) (B : QReg)
    (t : romWorld.Oracles.Domain) (μ : Option M) :
    ModedP okM (nxM upd rl)
      (fun p μ' ↦ μ' = nxM upd rl μ (.call (c, t)) p.2.2) μ (mixImpl c B t) := by
  moded_step
  · trivial
  moded_step
  · trivial
  rfl

theorem mem_support_liftM_query (t : romWorld.Oracles.Domain) (y : romWorld.Oracles.Range t) :
    y ∈ support (liftM (romWorld.Oracles.query t) :
      OracleComp romWorld.Oracles (romWorld.Oracles.Range t)) := by
  simp

theorem mem_support_liveImpl (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (c : Caller) (t : romWorld.Oracles.Domain)
    (μ : Option M) (y : romWorld.Oracles.Range t) :
    (y, nxM upd rl μ (.call (c, t)) y) ∈ support ((liveImpl rl (upd c) t).run μ) := by
  rcases t with n | z
  · change (y, μ) ∈ support ((fun b ↦ (b, μ)) <$> liftM (romWorld.Oracles.query (.inl n)))
    rw [support_map]
    exact ⟨y, by simp, rfl⟩
  · change (y, stepRd rl (upd c z) z μ y) ∈ support ((fun v ↦ (v, stepRd rl (upd c z) z μ v)) <$>
      liftM (romWorld.Oracles.query (.inr z)))
    rw [support_map]
    exact ⟨y, mem_support_liftM_query (.inr z) y, rfl⟩

theorem run_simulateQ_query_bind {σ α : Type} (impl : QueryImpl romWorld.Oracles
    (StateT σ (OracleComp romWorld.Oracles))) (t : romWorld.Oracles.Domain)
    (k : romWorld.Oracles.Range t → OracleComp romWorld.Oracles α) (s : σ) :
    (simulateQ impl (liftM (romWorld.Oracles.query t) >>= k)).run s =
      (impl t).run s >>= fun p ↦ (simulateQ impl (k p.1)).run p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

/-- **A classical algorithm by tagged calls is moded**, every leaf reached in a mode of a live run
of the algorithm returning the leaf's value. -/
theorem modedP_toQuantumAt_mixImpl (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (c : Caller) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (μ : Option M) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ LiveRun rl (upd c) oa μ p.2.2 μ') μ
      (oa.toQuantumAt (mixImpl c B)) := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure a =>
    change (a, μ) ∈ support ((simulateQ (liveImpl rl (upd c)) (pure a)).run μ)
    simp
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    refine modedP₂_bind (F := fun y μ' ↦ μ' = nxM upd rl μ (.call (c, t)) y)
      (F' := LiveRun rl (upd c) _ μ) _ _ (modedP_mixImpl upd rl c B t μ) fun y μ' hμ' ↦ ?_
    subst hμ'
    refine modedP_mono (fun p μ'' h ↦ ?_) _ _ (ih y _)
    unfold LiveRun at h ⊢
    rw [run_simulateQ_query_bind, mem_support_bind_iff]
    exact ⟨_, mem_support_liveImpl upd rl c t μ y, h⟩

/-- **A reduction's algorithm against the challenger is moded**, every leaf reached in a mode of
a live run (`liveRed`) returning the leaf's value and transcript. -/
theorem modedP_redImpl (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (B : QReg) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (log : QueryLog R') (μ : Option M) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ LiveRedRun rl upd ans oa log μ p.2.2 μ') μ
      ((simulateQ (redImpl ans B) oa).run log) := by
  induction oa using OracleComp.inductionOn generalizing log μ with
  | pure a =>
    change (a, (log, μ)) ∈ support ((simulateQ (liveRed rl upd ans) (pure a)).run (log, μ))
    simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ModedP okM (nxM upd rl) _ μ (QuantumComp₂.bind ((mixImpl .red B i).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2)
      refine modedP₂_bind
        (F := fun (p : romWorld.Oracles.Range i × QueryLog R') μ' ↦
          p.2 = log ∧ μ' = nxM upd rl μ (.call (.red, i)) p.1)
        (F' := LiveRedRun rl upd ans _ log μ)
        _ _ (modedP_map (F := fun (p : romWorld.Oracles.Range i × QueryLog R') μ' ↦
          p.2 = log ∧ μ' = nxM upd rl μ (.call (.red, i)) p.1) _
          (modedP_mono (fun p μ' h ↦ ⟨rfl, h⟩) _ _
          (modedP_mixImpl upd rl .red B i μ))) fun p μ' hp ↦ ?_
      obtain ⟨y, l⟩ := p
      obtain ⟨hl, rfl⟩ := hp
      change l = log at hl
      rw [hl]
      refine modedP_mono (fun p μ'' h ↦ ?_) _ _ (ih y _ _)
      unfold LiveRedRun at h ⊢
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(y, (log, nxM upd rl μ (.call (.red, i)) y)), ?_, h⟩
      change _ ∈ support ((fun p ↦ (p.1, (log, p.2))) <$> (liveImpl rl (upd .red) i).run μ)
      rw [support_map]
      exact ⟨_, mem_support_liveImpl upd rl .red i μ y, rfl⟩
    · change ModedP okM (nxM upd rl) _ μ (QuantumComp₂.bind (((ans q').toQuantumAt
          (mixImpl .answer B)).map fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
            (simulateQ (redImpl ans B) (k p.1)).run p.2)
      refine modedP₂_bind
        (F := fun (p : R'.Range q' × QueryLog R') μ' ↦ p.2 = log ++ [⟨q', p.1⟩] ∧
          LiveRun rl (upd .answer) (ans q') μ p.1 μ')
        (F' := LiveRedRun rl upd ans _ log μ)
        _ _ (modedP_map (F := fun (p : R'.Range q' × QueryLog R') μ' ↦
          p.2 = log ++ [⟨q', p.1⟩] ∧ LiveRun rl (upd .answer) (ans q') μ p.1 μ') _
          (modedP_mono (fun p μ' h ↦ ⟨rfl, h⟩) _ _
          (modedP_toQuantumAt_mixImpl upd rl .answer B (ans q') μ))) fun p μ' hp ↦ ?_
      obtain ⟨y, l⟩ := p
      obtain ⟨hl, hy⟩ := hp
      change l = log ++ [⟨q', y⟩] at hl
      rw [hl]
      refine modedP_mono (fun p μ'' h ↦ ?_) _ _ (ih y _ _)
      unfold LiveRedRun at h ⊢
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(y, (log ++ [⟨q', y⟩], μ')), ?_, h⟩
      change _ ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rl (upd .answer)) (ans q')).run μ)
      rw [support_map]
      exact ⟨_, hy, rfl⟩

/-- **The adversary's run against call trees keeping an invariant**: if every call tree from a
state satisfying `J` ends in states satisfying `J`, every leaf of the mixed run is reached in a
mode where the final state satisfies `J`. -/
theorem modedP_mixRun (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}
    {X Y : QReg → Type} (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u)
    (J : St → Option M → Prop)
    (hTr : ∀ s q (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) μ, J s μ →
      ModedP okM (nxM upd rl) (fun p μ' ↦ J p.2.2.2 μ') μ (Tr s q E ℓ))
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St) (μ : Option M) (hs : J s μ) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ ∃ u y s', J s' μ' ∧ p = ⟨u, leaf u y s'⟩) μ
      (mixRun Tr leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s μ with
  | pure u y => exact ⟨u, y, s, hs, rfl⟩
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b s μ hs⟩
    · exact ⟨trivial, fun b ↦ ih b s μ hs⟩
    · refine modedP_bind (Tr s q E ℓ) _ (hTr s q E A ℓ μ hs) fun u l μ' hl ↦ ?_
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 μ' hl

/-- **The reduction's call trees keep an invariant** of the handler state and transcript if every
live run of the handler does. -/
theorem modedP_mixTrees (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St : Type}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (σ : HHandler romWorld R R' St)
    (J : St × QueryLog R' → Option M → Prop)
    (hσ : ∀ st log μ q, J (st, log) μ → ∀ r μ',
      LiveRedRun rl upd ans (σ st q) log μ r μ' → J (r.1.2, r.2) μ')
    (s : St × QueryLog R') (q : Q) (E A : QReg)
    (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) (μ : Option M) (hs : J s μ) :
    ModedP okM (nxM upd rl) (fun p μ' ↦ J p.2.2.2 μ') μ (mixTrees ans σ s q E ℓ) := by
  refine modedP₂_bind (F := fun _ μ' ↦ μ' = μ)
    (F' := fun (r : R.Range q × (St × QueryLog R')) μ' ↦ J r.2 μ') _ _
    (Quantum.Xmss.Assembly.modedP_act (F := fun _ μ' ↦ μ' = μ) _ μ fun _ ↦ rfl) fun _ μ' hμ' ↦ ?_
  subst hμ'
  refine modedP_map (F := fun (r : R.Range q × (St × QueryLog R')) μ' ↦ J r.2 μ') _
    (modedP_mono (fun p μ'' h ↦ ?_) _ _
    (modedP_redImpl upd rl ans _ (σ s.1 q) s.2 μ'))
  exact hσ s.1 s.2 μ' q hs _ _ h

/-- **The game of a straight-line reduction as a moded mixed program**: if the live runs of the
challenger's setup, of the reduction's setup, handler and output, and of the challenger's
decision keep invariants `I0`, `J`, `Ipost`, every leaf returning `b` is reached in a mode
satisfying `Win b`. -/
theorem modedP_mixGame (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type} (E : Props.Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out) (m₀ : M)
    (I0 : E.State → Option M → Prop)
    (h0 : ∀ s μ, LiveRun rl (upd .setup) E.setup (some m₀) s μ → I0 s μ)
    (J : E.State → S0 → St × QueryLog R' → Option M → Prop)
    (hpre : ∀ s μ, I0 s μ → ∀ a μ', LiveRedRun rl upd (E.answer s) (pre (E.pub s)) [] μ a μ' →
      J s a.1 (st0 (E.pub s) a.1, a.2) μ')
    (hσ : ∀ s a st log μ q, J s a (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (σ (E.pub s) st q) log μ r μ' → J s a (r.1.2, r.2) μ')
    (Ipost : E.State → Out × QueryLog R' → Option M → Prop)
    (hpost : ∀ s a f st log μ, J s a (st, log) μ → ∀ r μ',
      LiveRedRun rl upd (E.answer s) (post (E.pub s) a f st) log μ r μ' → Ipost s r μ')
    (Win : Bool → Option M → Prop)
    (hjudge : ∀ s r μ, Ipost s r μ → ∀ b μ',
      LiveRun rl (upd .judge) (E.judge s r.2 r.1) μ b μ' → Win b μ') :
    ModedP okM (nxM upd rl) (fun p μ ↦ Win p.2.2 μ) (some m₀)
      (mixGame E pre adv st0 σ post) := by
  refine modedP₂_bind (F := I0) (F' := Win) _ _
    (modedP_mono (fun p μ h ↦ h0 _ _ h) _ _
      (modedP_toQuantumAt_mixImpl upd rl .setup _ E.setup (some m₀))) fun s μ hs ↦ ?_
  refine modedP₂_bind (F := Ipost s) (F' := Win) _ _ ?_
    fun r μ' hr ↦ modedP_mono (fun p μ'' h ↦ hjudge s r μ' hr _ μ'' h) _ _
      (modedP_toQuantumAt_mixImpl upd rl .judge _ (E.judge s r.2 r.1) μ')
  refine modedP₂_bind (F := fun a μ ↦ J s a.1 (st0 (E.pub s) a.1, a.2) μ) (F' := Ipost s) _ _
    (modedP_mono (fun p μ h ↦ hpre s _ hs _ _ h) _ _
      (modedP_redImpl upd rl (E.answer s) _ (pre (E.pub s)) [] μ)) fun a μ1 ha ↦ ?_
  refine modedP₂_bind (F := fun r μ ↦ J s a.1 (r.1.2, r.2) μ) (F' := Ipost s) _ _ ?_
    fun r μ2 hr ↦ modedP_mono (fun p μ h ↦ hpost s a.1 r.1.1 r.1.2 r.2 μ2 hr _ _ h) _ _
      (modedP_redImpl upd rl (E.answer s) _ (post (E.pub s) a.1 r.1.1 r.1.2) r.2 μ2)
  refine modedP_mono (fun p μ h ↦ ?_) _ _ (modedP_mixRun upd rl (mixTrees (E.answer s)
    (σ (E.pub s))) _ (J s a.1) (fun st q E' A ℓ μ hst ↦ modedP_mixTrees upd rl (E.answer s)
      (σ (E.pub s)) (J s a.1) (fun st log μ q h r μ' hr ↦ hσ s a.1 st log μ q h r μ' hr) st q E' A ℓ
        μ hst) (adv (E.pub s) a.1) (st0 (E.pub s) a.1, a.2) μ1 ha)
  obtain ⟨u, y, s', hJ, rfl⟩ := h
  exact hJ

end live

/-! ## The phase of the challenger's answers -/

section phase

open Quantum.Qrom HashSig OracleComp OracleSpec Common
open Quantum.Xmss.Assembly (modeCmdOk modeCmdNx modedP_bind modedP₂_bind modedP_map)

variable {M : Type} (Gc : HashDomain → Prop)

/-- Whether a mixed call is an answer of the challenger. -/
def isAns : (MixSpec Caller).Port → Bool
  | .call (c, _) => c == .answer
  | .hash _ => false

/-- **Answers only in the first phase.** -/
def okPhM (ph : Bool) (p : (MixSpec Caller).Port) : Prop := isAns p = true → ph = true

open scoped Classical in
/-- **The phase after a mixed call**: the first phase ends at a hash call of the adversary or at a
classical call of another caller than the challenger's answers at a cell of `Gc`. -/
noncomputable def nxPhM : Bool → (p : (MixSpec Caller).Port) → (MixSpec Caller).Result p → Bool
  | _, .hash _, _ => false
  | ph, .call (_, .inl _), _ => ph
  | ph, .call (c, .inr z), _ => if Gc z ∧ c ≠ .answer then false else ph

/-- The calls at cells of `Gc`. -/
noncomputable def gCost : romWorld.Oracles.Domain → ℕ
  | .inl _ => 0
  | .inr x => @ite _ (Gc x) (Classical.propDecidable _) 1 0

/-- A reduction's calls at cells of `Gc`. -/
noncomputable def gCostR {Q' : Type} {R' : OracleSpec.{0, 0} Q'} :
    (romWorld.Oracles + R').Domain → ℕ
  | .inl t => gCost Gc t
  | .inr _ => 0

/-- A reduction's calls of the challenger. -/
def ansCost {Q' : Type} {R' : OracleSpec.{0, 0} Q'} : (romWorld.Oracles + R').Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

theorem okPhM_call {c : Caller} (hc : c ≠ .answer) (ph : Bool) (t : RomOracles.Domain) :
    okPhM ph (.call (c, t)) := fun h ↦ by
  cases c <;> first | exact absurd rfl hc | simp [isAns] at h

theorem modedP_phase_mixImpl (c : Caller) (B : QReg) (t : romWorld.Oracles.Domain) (ph : Bool)
    (hc : c = .answer → ph = true) :
    ModedP okPhM (nxPhM Gc) (fun p ph' ↦ ph' = nxPhM Gc ph (.call (c, t)) p.2.2) ph
      (mixImpl c B t) := by
  moded_step
  · by_cases hca : c = .answer
    · exact fun _ ↦ hc hca
    · exact okPhM_call hca ph t
  moded_step
  · trivial
  rfl

/-- **A classical algorithm of a caller in the first phase stays in it** when it is the
challenger's answer or makes no call at a cell of `Gc`. -/
theorem modedP_phase_toQuantumAt (c : Caller) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α)
    (h : c ≠ .answer → QueryCostAtMost oa (gCost Gc) 0) :
    ModedP okPhM (nxPhM Gc) (fun _ ph ↦ ph = true) true (oa.toQuantumAt (mixImpl c B)) := by
  revert h
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun _ ↦ rfl
  | query_bind t k ih =>
    intro h
    rw [toQuantumAt_query_bind]
    refine modedP₂_bind (F := fun y ph ↦ ph = nxPhM Gc true (.call (c, t)) y)
      (F' := fun _ ph ↦ ph = true) _ _ (modedP_phase_mixImpl Gc c B t true fun _ ↦ rfl)
      fun y ph hph ↦ ?_
    have hk : c ≠ .answer → QueryCostAtMost (k y) (gCost Gc) 0 := fun hc ↦ by
      have h' := h hc
      rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h'
      have h2 := h'.2 y
      rw [h'.1.antisymm (Nat.zero_le _), Nat.sub_zero] at h2
      exact h2
    have htrue : ph = true := by
      subst hph
      rcases t with n | z
      · rfl
      · simp only [nxPhM]
        split_ifs with hz
        · exfalso
          have h' := h hz.2
          rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h'
          have := h'.1
          simp [gCost, hz.1] at this
        · rfl
    subst htrue
    exact ih y hk

/-- A classical algorithm of another caller than the answers keeps every call allowed. -/
theorem modedP_phase_toQuantumAt_any (c : Caller) (hc : c ≠ .answer) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (ph : Bool) :
    ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) ph (oa.toQuantumAt (mixImpl c B)) := by
  induction oa using OracleComp.inductionOn generalizing ph with
  | pure a => trivial
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    exact modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
      (modedP_mono (fun _ _ _ ↦ trivial) _ _
        (modedP_phase_mixImpl Gc c B t ph fun h ↦ absurd h hc)) fun y ph' _ ↦ ih y ph'

/-- **A reduction's algorithm without challenger calls keeps every call allowed.** -/
theorem modedP_phase_redImpl_any {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (B : QReg) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (h : QueryCostAtMost oa (ansCost (R' := R')) 0)
    (log : QueryLog R') (ph : Bool) :
    ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) ph ((simulateQ (redImpl ans B) oa).run log) := by
  induction oa using OracleComp.inductionOn generalizing log ph with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ModedP okPhM (nxPhM Gc) _ ph (QuantumComp₂.bind ((mixImpl .red B i).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2)
      refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
        (modedP_map (F := fun _ _ ↦ True) _ (modedP_mono (fun _ _ _ ↦ trivial) _ _
          (modedP_phase_mixImpl Gc .red B i ph fun h ↦ by cases h))) fun p ph' _ ↦ ?_
      exact ih p.1 (by have h2 := h.2 p.1; rw [Nat.zero_sub] at h2; exact h2) p.2 ph'
    · exact absurd h.1 (by simp [ansCost])

/-- **A reduction's setup in the first phase stays in it** when its own calls avoid `Gc`. -/
theorem modedP_phase_redImpl_pre {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q')) (B : QReg) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (h : QueryCostAtMost oa (gCostR Gc (R' := R')) 0)
    (log : QueryLog R') :
    ModedP okPhM (nxPhM Gc) (fun _ ph ↦ ph = true) true
      ((simulateQ (redImpl ans B) oa).run log) := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure a => rfl
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ModedP okPhM (nxPhM Gc) _ true (QuantumComp₂.bind ((mixImpl .red B i).map
          fun a ↦ (a, log)) fun p ↦ (simulateQ (redImpl ans B) (k p.1)).run p.2)
      have hi : QueryCostAtMost (liftM (romWorld.Oracles.query i) >>= fun y ↦ pure y :
          OracleComp romWorld.Oracles _) (gCost Gc) 0 := by
        rw [QueryCostAtMost, isQueryBound_query_bind_iff]
        exact ⟨by simpa [gCostR] using h.1, fun _ ↦ trivial⟩
      refine modedP₂_bind (F := fun _ ph ↦ ph = true) (F' := fun _ ph ↦ ph = true) _ _
        (modedP_map (F := fun _ ph ↦ ph = true) _ ?_) fun p ph' hph ↦ ?_
      · have hm := modedP_phase_toQuantumAt Gc .red B
          (liftM (romWorld.Oracles.query i) >>= fun y ↦ pure y) fun _ ↦ hi
        rw [toQuantumAt_query_bind] at hm
        simpa using hm
      · subst hph
        exact ih p.1 (by have h2 := h.2 p.1; rw [Nat.zero_sub] at h2; exact h2) p.2
    · change ModedP okPhM (nxPhM Gc) _ true (QuantumComp₂.bind (((ans q').toQuantumAt
          (mixImpl .answer B)).map fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦
            (simulateQ (redImpl ans B) (k p.1)).run p.2)
      refine modedP₂_bind (F := fun _ ph ↦ ph = true) (F' := fun _ ph ↦ ph = true) _ _
        (modedP_map (F := fun _ ph ↦ ph = true) _
          (modedP_phase_toQuantumAt Gc .answer B (ans q') fun h ↦ absurd rfl h))
        fun p ph' hph ↦ ?_
      subst hph
      exact ih p.1 (by have h2 := h.2 p.1; rw [Nat.zero_sub] at h2; exact h2) p.2

/-- **The adversary's run keeps every call allowed** when the call trees do. -/
theorem modedP_phase_mixRun {Q : Type} {R : OracleSpec.{0, 0} Q} {St : Type}
    {X Y : QReg → Type} (Tr : MixTrees R St) (leaf : ∀ u, X u → St → Y u)
    (hTr : ∀ s q (E A : QReg) (ℓ : A ≃ (advSpec romWorld.spec R).In (.call q) × E) ph,
      ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) ph (Tr s q E ℓ)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A)
    (s : St) (ph : Bool) :
    ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) ph (mixRun Tr leaf x s) := by
  induction x using IFreeM.inductionOn generalizing s ph with
  | pure u y => trivial
  | liftBind A cmd next ih =>
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b s ph⟩
    · exact ⟨fun h ↦ absurd h (by simp [isAns]), fun b ↦ ih b s _⟩
    · refine modedP_bind (Tr s q E ℓ) _ (hTr s q E A ℓ ph) fun u l ph' _ ↦ ?_
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 ph'

/-- **The challenger's answers come in the first phase** of the game of a straight-line
reduction whose setup and challenger setup make no call at a cell of `Gc` and whose handler and
output never call the challenger. -/
theorem modedP_phase_mixGame {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
    {R' : OracleSpec.{0, 0} Q'} {St Pub Out : Type} (E : Props.Experiment romWorld R' Pub Out)
    {S0 F : Type} (pre : Pub → OracleComp (romWorld.Oracles + R') S0)
    (adv : Pub → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Pub → S0 → St) (σ : Pub → HHandler romWorld R R' St)
    (post : Pub → S0 → F → St → OracleComp (romWorld.Oracles + R') Out)
    (hsetup : QueryCostAtMost E.setup (gCost Gc) 0)
    (hpre : ∀ p, QueryCostAtMost (pre p) (gCostR Gc (R' := R')) 0)
    (hσ : ∀ p s q, QueryCostAtMost (σ p s q) (ansCost (R' := R')) 0)
    (hpost : ∀ p a f s, QueryCostAtMost (post p a f s) (ansCost (R' := R')) 0) :
    ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) true (mixGame E pre adv st0 σ post) := by
  refine modedP₂_bind (F := fun _ ph ↦ ph = true) (F' := fun _ _ ↦ True) _ _
    (modedP_phase_toQuantumAt Gc .setup _ E.setup fun _ ↦ hsetup) fun s ph hph ↦ ?_
  subst hph
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_
    fun r ph' _ ↦ modedP_phase_toQuantumAt_any Gc .judge (by decide) _ _ ph'
  refine modedP₂_bind (F := fun _ ph ↦ ph = true) (F' := fun _ _ ↦ True) _ _
    (modedP_phase_redImpl_pre Gc (E.answer s) _ (pre (E.pub s)) (hpre _) []) fun a ph hph ↦ ?_
  subst hph
  refine modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _ ?_
    fun r ph' _ ↦ modedP_phase_redImpl_any Gc (E.answer s) _ _ (hpost _ _ _ _) r.2 ph'
  exact modedP_phase_mixRun Gc _ _ (fun st q E' A ℓ ph ↦
    modedP₂_bind (F := fun _ _ ↦ True) (F' := fun _ _ ↦ True) _ _
      (Quantum.Xmss.Assembly.modedP_act (F := fun _ _ ↦ True) _ ph fun _ ↦ trivial)
      fun _ ph' _ ↦ modedP_map (F := fun _ _ ↦ True) _
        (modedP_phase_redImpl_any Gc (E.answer s) _ _ (hσ _ _ _) st.2 ph')) _ _ true

/-! ## Memory and phase together -/

/-- The phase after a call from the memory `μ` to `μ'`: kept on a dead memory, reset when the
memory dies, else `phNew`. -/
def phStep : Option M → Option M → Bool → Bool → Bool
  | none, _, ph, _ => ph
  | some _, none, _, _ => true
  | some _, some _, _, phNew => phNew

theorem phStep_self (μ : Option M) (ph : Bool) : phStep μ μ ph ph = ph := by
  rcases μ with _ | m <;> rfl

/-- The calls a memory and phase allow: a dead memory every call, else the phase's. -/
def okP (μ : Option M × Bool) (p : (MixSpec Caller).Port) : Prop :=
  μ.1 = none ∨ okPhM μ.2 p

/-- **The memory and phase after a mixed call.** -/
noncomputable def nxP (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (μ : Option M × Bool) (p : (MixSpec Caller).Port)
    (r : (MixSpec Caller).Result p) : Option M × Bool :=
  (nxM upd rl μ.1 p r, phStep μ.1 (nxM upd rl μ.1 p r) μ.2 (nxPhM Gc μ.2 p r))

theorem nxM_none (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (p : (MixSpec Caller).Port)
    (r : (MixSpec Caller).Result p) : nxM upd rl none p r = none := by
  rcases p with p | ⟨c, n | z⟩ <;> rfl

/-- **A memory-moded and a phase-moded mixed program is moded in both.** -/
theorem modedP_prod (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Ω : QReg → Type}
    {fin : (Σ u, Ω u) → Option M → Prop} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (MixSpec Caller) Ω A) :
    ∀ μ ph ph₀, (μ = none ∨ ph₀ = ph) → ModedP okM (nxM upd rl) fin μ x →
      ModedP okPhM (nxPhM Gc) (fun _ _ ↦ True) ph x →
      ModedP okP (nxP Gc upd rl) (fun p m ↦ fin p m.1) (μ, ph₀) x := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact fun _ _ _ _ h _ ↦ h
  | liftBind _ c next ih =>
    intro μ ph ph₀ hrel h1 h2
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih b μ ph ph₀ hrel (h1.2 b) (h2.2 b)⟩
    · refine ⟨?_, fun b ↦ ?_⟩
      · rcases hrel with h | h
        · exact Or.inl h
        · exact Or.inr (h ▸ h2.1)
      refine ih b _ (nxPhM Gc ph i b.down) _ ?_ (h1.2 b) (h2.2 b)
      rcases μ with _ | m
      · exact Or.inl (nxM_none upd rl i b.down)
      · have hph : ph₀ = ph := hrel.resolve_left (by simp)
        subst hph
        change nxM upd rl (some m) i b.down = none ∨
          phStep (some m) (nxM upd rl (some m) i b.down) ph₀ (nxPhM Gc ph₀ i b.down) =
            nxPhM Gc ph₀ i b.down
        rcases nxM upd rl (some m) i b.down with _ | m'
        · exact Or.inl rfl
        · exact Or.inr rfl

/-- **The phase of the read ports**: answers only in the first phase. -/
def okPhH (upd : Caller → HashDomain → M → Option HashOutput → M) (ph : Bool) :
    (hwSpec HashOutput HashDomain M).Port → Prop
  | .inl (.inr (.readH z u)) => u = upd .answer z → ph = true
  | _ => True

open scoped Classical in
/-- **The phase after a read-program call**: the first phase ends at a sponge call or at a read
of a cell of `Gc` by another policy than the answers'. -/
noncomputable def nxPhH (upd : Caller → HashDomain → M → Option HashOutput → M) (ph : Bool) :
    (i : (hwSpec HashOutput HashDomain M).Port) → (hwSpec HashOutput HashDomain M).Result i → Bool
  | .inl (.inl _), _ => false
  | .inl (.inr (.readH z u)), _ => if Gc z ∧ u ≠ upd .answer z then false else ph
  | _, _ => ph

/-- The read ports of the policies `upd`: sponge calls and reads of `h` by a caller's policy. -/
def PolicyPort (upd : Caller → HashDomain → M → Option HashOutput → M) :
    (hwSpec HashOutput HashDomain M).Port → Prop
  | .inl (.inl _) => True
  | .inl (.inr (.readH z u)) => ∃ c, u = upd c z
  | _ => False

/-- The calls of the read program a memory and phase allow: on a live memory, the phase's calls
of the policies' ports. -/
def okD2 (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (μ : Option M × Bool)
    (i : (hwSpec HashOutput HashDomain M).Port) : Prop :=
  OkD rl μ.1 i ∧ (μ.1 = none ∨ okPhH upd μ.2 i ∧ PolicyPort upd i)

/-- **The memory and phase after a read-program call.** -/
noncomputable def nxD2 (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (μ : Option M × Bool)
    (i : (hwSpec HashOutput HashDomain M).Port) (r : (hwSpec HashOutput HashDomain M).Result i) :
    Option M × Bool :=
  (nxD rl μ.1 i r, phStep μ.1 (nxD rl μ.1 i r) μ.2 (nxPhH Gc upd μ.2 i r))

theorem nxPhH_readH (upd : Caller → HashDomain → M → Option HashOutput → M)
    (hupd : ∀ c z, c ≠ .answer → upd c z ≠ upd .answer z) (ph : Bool) (c : Caller)
    (z : HashDomain) (r : Option HashOutput × M) (v : HashOutput) :
    nxPhH Gc upd ph (.inl (.inr (.readH z (upd c z)))) r = nxPhM Gc ph (.call (c, .inr z)) v := by
  simp only [nxPhH, nxPhM]
  split_ifs with ha hb hb
  · rfl
  · exact absurd ⟨ha.1, fun h ↦ ha.2 (h ▸ rfl)⟩ hb
  · exact absurd ⟨hb.1, hupd c z hb.2⟩ ha
  · rfl

theorem nxD2_readH (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput)
    (hupd : ∀ c z, c ≠ .answer → upd c z ≠ upd .answer z) (μ : Option M × Bool) (c : Caller)
    (z : HashDomain) (r : Option HashOutput × M) :
    nxD2 Gc upd rl μ (.inl (.inr (.readH z (upd c z)))) r =
        nxP Gc upd rl μ (.call (c, .inr z)) (r.1.getD 0) ∨
      nxD2 Gc upd rl μ (.inl (.inr (.readH z (upd c z)))) r = (none, true) := by
  rcases μ with ⟨_ | m, ph⟩
  · exact Or.inl rfl
  rcases r with ⟨_ | v, m'⟩
  · exact Or.inr rfl
  · left
    change (stepRd rl (upd c z) z (some m) v, phStep (some m) (stepRd rl (upd c z) z (some m) v) ph
        (nxPhH Gc upd ph (.inl (.inr (.readH z (upd c z)))) (some v, m'))) =
      (stepRd rl (upd c z) z (some m) v, phStep (some m) (stepRd rl (upd c z) z (some m) v) ph
        (nxPhM Gc ph (.call (c, .inr z)) v))
    rw [nxPhH_readH Gc upd hupd ph c z _ v]

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step'" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

/-- **The read program of a mixed program moded in memory and phase is moded in both.** -/
theorem modedP_toReads_prod (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) (hrec : ∀ c z, RecordsAt rl z (upd c z))
    (hupd : ∀ c z, c ≠ .answer → upd c z ≠ upd .answer z)
    {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option M × Bool → Prop}
    (hfin : ∀ p, fin p (none, true)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (μ : Option M × Bool) (hx : ModedP okP (nxP Gc upd rl) fin μ x) :
    ModedP (okD2 upd rl) (nxD2 Gc upd rl) fin μ
      (IFreeM.mapLens Quantum.Xmss.Assembly.liftReadLens (IFreeM.substitute (readSub upd) x)) := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute _ (none, true) (fun i ↦ ⟨okD_none rl i, Or.inl rfl⟩)
    (fun i r ↦ rfl) (fun A c μ hc ↦ ?_) hfin x μ hx
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step'
    · trivial
    · exact Or.inl rfl
  · moded_step'
    · exact ⟨okD_sponge rl μ.1 _, Or.inr ⟨trivial, trivial⟩⟩
    · refine Or.inl (Prod.ext (nxD_sponge rl μ.1 _ _) ?_)
      change phStep μ.1 (nxD rl μ.1 _ _) μ.2 false = phStep μ.1 μ.1 μ.2 false
      rw [nxD_sponge]
  · moded_step'
    · trivial
    moded_step'
    · trivial
    exact Or.inl (Prod.ext rfl (phStep_self μ.1 μ.2).symm)
  · moded_step'
    · trivial
    moded_step'
    · refine ⟨okD_readH rl μ.1 z _ (hrec tag z), ?_⟩
      rcases hc with h | h
      · exact Or.inl h
      · refine Or.inr ⟨fun heq ↦ h ?_, ⟨tag, rfl⟩⟩
        by_cases ht : tag = .answer
        · subst ht
          rfl
        · exact absurd heq (hupd tag z ht)
    moded_step'
    · trivial
    exact nxD2_readH Gc upd rl hupd μ tag z _

/-- A live step of a read with a value consistent with the log. -/
theorem stepRd_some {rl : M → HashDomain → Option HashOutput}
    {u : M → Option HashOutput → M} {z : HashDomain} {m m' : M} {v : HashOutput}
    (h : stepRd rl u z (some m) v = some m') :
    m' = u m (some v) ∧ (rl m z = none ∨ rl m z = some v) := by
  unfold stepRd at h
  dsimp only at h
  split_ifs at h with hc
  refine ⟨(Option.some.inj h).symm, ?_⟩
  rcases hr : rl m z with _ | w
  · exact Or.inl rfl
  · rw [hr] at hc
    exact Or.inr (by_contra fun hw ↦ hc ⟨rfl, hw⟩)

/-- A live step of a read at an unlogged cell. -/
theorem stepRd_of_none {rl : M → HashDomain → Option HashOutput}
    {u : M → Option HashOutput → M} {z : HashDomain} {m : M} (h : rl m z = none)
    (v : HashOutput) : stepRd rl u z (some m) v = some (u m (some v)) := by
  unfold stepRd
  simp [h]

/-- A live run of a value. -/
theorem liveRun_pure_inv {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} {α : Type} {b a : α} {μ μ' : Option M}
    (h : LiveRun rl u (pure b : OracleComp romWorld.Oracles α) μ a μ') : a = b ∧ μ' = μ := by
  unfold LiveRun at h
  simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] using h

/-- A live run starting with a read of `x`. -/
theorem liveRun_query_bind {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} {α : Type} {t : romWorld.Oracles.Domain}
    {k : romWorld.Oracles.Range t → OracleComp romWorld.Oracles α} {μ : Option M} {a : α}
    {μ' : Option M} (h : LiveRun rl u (liftM (romWorld.Oracles.query t) >>= k) μ a μ') :
    ∃ y μ₁, (y, μ₁) ∈ support ((liveImpl rl u t).run μ) ∧ LiveRun rl u (k y) μ₁ a μ' := by
  unfold LiveRun at h
  rw [run_simulateQ_query_bind, mem_support_bind_iff] at h
  obtain ⟨⟨y, μ₁⟩, h₁, h₂⟩ := h
  exact ⟨y, μ₁, h₁, h₂⟩

/-- The mode after a live read of `x`. -/
theorem eq_stepRd_of_mem_support {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} {x : HashDomain} {y : HashOutput}
    {μ μ₁ : Option M} (h : (y, μ₁) ∈ support ((liveImpl rl u (Sum.inr x)).run μ)) :
    μ₁ = stepRd rl (u x) x μ y := by
  change (y, μ₁) ∈ support ((fun v ↦ (v, stepRd rl (u x) x μ v)) <$>
    liftM (romWorld.Oracles.query (Sum.inr x))) at h
  rw [support_map] at h
  obtain ⟨v, _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rfl

/-- A live run from the dead mode stays dead. -/
theorem liveRun_none_mode {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} {α : Type}
    (oa : OracleComp romWorld.Oracles α) {a : α} {μ' : Option M}
    (h : LiveRun rl u oa none a μ') : μ' = none := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact (liveRun_pure_inv h).2
  | query_bind t k ih =>
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    have hμ₁ : μ₁ = none := by
      rcases t with n | z
      · change (y, μ₁) ∈ support ((fun b ↦ (b, none)) <$>
          liftM (romWorld.Oracles.query (.inl n))) at h₁
        rw [support_map] at h₁
        obtain ⟨_, _, he⟩ := h₁
        exact (Prod.mk.inj he).2.symm
      · exact eq_stepRd_of_mem_support h₁
    subst hμ₁
    exact ih y h₂

/-- **An invariant of the live runs of a classical algorithm kept by every read.** -/
theorem liveRun_inv_all {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} (Φ : Option M → Prop)
    (hΦ : ∀ z μ v, Φ μ → Φ (stepRd rl (u z) z μ v)) {α : Type}
    (oa : OracleComp romWorld.Oracles α) {μ : Option M} {a : α} {μ' : Option M}
    (h : LiveRun rl u oa μ a μ') (hμ : Φ μ) : Φ μ' := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure x => exact (liveRun_pure_inv h).2 ▸ hμ
  | query_bind t k ih =>
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    refine ih y h₂ ?_
    rcases t with n | z
    · change (y, μ₁) ∈ support ((fun b ↦ (b, μ)) <$>
        liftM (romWorld.Oracles.query (.inl n))) at h₁
      rw [support_map] at h₁
      obtain ⟨_, _, he⟩ := h₁
      rw [← (Prod.mk.inj he).2]
      exact hμ
    · rw [eq_stepRd_of_mem_support h₁]
      exact hΦ z μ y hμ

/-- A live run of a value fed to a continuation. -/
theorem liveRun_pure_bind {rl : M → HashDomain → Option HashOutput}
    {u : HashDomain → M → Option HashOutput → M} {α β : Type} {b : β}
    {k : β → OracleComp romWorld.Oracles α} {μ : Option M} {a : α} {μ' : Option M}
    (h : LiveRun rl u (pure b >>= k) μ a μ') : LiveRun rl u (k b) μ a μ' := by
  rwa [pure_bind] at h

/-! ## Invariants and counts along live runs -/

/-- **An invariant of the live runs of a classical algorithm**: kept by the reads at cells outside
`Gc`, when the algorithm reads no cell of `Gc`. -/
theorem liveRun_inv (rl : M → HashDomain → Option HashOutput)
    (u : HashDomain → M → Option HashOutput → M) (Φ : Option M → Prop)
    (hΦ : ∀ z μ v, ¬ Gc z → Φ μ → Φ (stepRd rl (u z) z μ v)) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (h : QueryCostAtMost oa (gCost Gc) 0) {μ : Option M}
    {a : α} {μ' : Option M} (hrun : LiveRun rl u oa μ a μ') (hμ : Φ μ) : Φ μ' := by
  induction oa using OracleComp.inductionOn generalizing μ with
  | pure x =>
    unfold LiveRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    rw [hrun.2]
    exact hμ
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    unfold LiveRun at hrun
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, μ₁⟩, h₁, h₂⟩ := hrun
    have hμ₁ : Φ μ₁ := by
      rcases t with n | z
      · change (y, μ₁) ∈ support ((fun b ↦ (b, μ)) <$> liftM (romWorld.Oracles.query (.inl n)))
          at h₁
        rw [support_map] at h₁
        obtain ⟨_, _, he⟩ := h₁
        rw [← (Prod.mk.inj he).2]
        exact hμ
      · change (y, μ₁) ∈ support ((fun v ↦ (v, stepRd rl (u z) z μ v)) <$>
          liftM (romWorld.Oracles.query (.inr z))) at h₁
        rw [support_map] at h₁
        obtain ⟨v, _, he⟩ := h₁
        rw [← (Prod.mk.inj he).2]
        have hz : ¬ Gc z := fun hz ↦ by
          have := h.1
          simp [gCost, hz] at this
        exact hΦ z μ v hz hμ
    exact ih y (by have h2 := h.2 y; rwa [Nat.zero_sub] at h2) h₂ hμ₁

/-- **An invariant of the live runs of a reduction's algorithm**: kept by its own reads and the
challenger's answers of cost `0`, when the algorithm's calls cost `0`. -/
theorem liveRedRun_inv_cost (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (c : (romWorld.Oracles + R').Domain → ℕ) (Φ : QueryLog R' → Option M → Prop)
    (hred : ∀ z log μ v, c (.inl (.inr z)) = 0 → Φ log μ →
      Φ log (stepRd rl (upd .red z) z μ v))
    (hans : ∀ q' log μ a μ', c (.inr q') = 0 → Φ log μ →
      LiveRun rl (upd .answer) (ans q') μ a μ' → Φ (log ++ [⟨q', a⟩]) μ') {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (h : QueryCostAtMost oa c 0)
    {log : QueryLog R'} {μ : Option M} {a : α × QueryLog R'} {μ' : Option M}
    (hrun : LiveRedRun rl upd ans oa log μ a μ') (hΦ : Φ log μ) : Φ a.2 μ' := by
  induction oa using OracleComp.inductionOn generalizing log μ with
  | pure x =>
    unfold LiveRedRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    rw [hrun.2.1, hrun.2.2]
    exact hΦ
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    unfold LiveRedRun at hrun
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := hrun
    have hk : QueryCostAtMost (k y) c 0 := by have h2 := h.2 y; rwa [Nat.zero_sub] at h2
    have hc : c t = 0 := Nat.le_zero.mp h.1
    refine ih y hk h₂ ?_
    rcases t with (n | z) | q'
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd .red) (.inl n)).run μ) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      change (y', μ₂) ∈ support ((fun b ↦ (b, μ)) <$>
        liftM (romWorld.Oracles.query (.inl n))) at h₃
      rw [support_map] at h₃
      obtain ⟨_, _, he'⟩ := h₃
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      rw [← (Prod.mk.inj he').2]
      exact hΦ
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd .red) (.inr z)).run μ) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      change (y', μ₂) ∈ support ((fun v ↦ (v, stepRd rl (upd .red z) z μ v)) <$>
        liftM (romWorld.Oracles.query (.inr z))) at h₃
      rw [support_map] at h₃
      obtain ⟨v, _, he'⟩ := h₃
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      rw [← (Prod.mk.inj he').2]
      exact hred z log μ v hc hΦ
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log ++ [⟨q', p.1⟩], p.2))) <$>
        (simulateQ (liveImpl rl (upd .answer)) (ans q')).run μ) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact hans q' log μ y' μ₂ hc hΦ h₃

/-- **A count along the live runs of a reduction's algorithm without challenger calls**: raised
by each own read by at most its cost. -/
theorem liveRedRun_count (upd : Caller → HashDomain → M → Option HashOutput → M)
    (rl : M → HashDomain → Option HashOutput) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (q' : Q') → OracleComp romWorld.Oracles (R'.Range q'))
    (c : (romWorld.Oracles + R').Domain → ℕ) (f : Option M → ℕ)
    (hred : ∀ z μ v, f (stepRd rl (upd .red z) z μ v) ≤ f μ + c (.inl (.inr z))) {α : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) {k : ℕ} (h : QueryCostAtMost oa c k)
    (hna : QueryCostAtMost oa (ansCost (R' := R')) 0)
    {log : QueryLog R'} {μ : Option M} {a : α × QueryLog R'} {μ' : Option M}
    (hrun : LiveRedRun rl upd ans oa log μ a μ') : f μ' ≤ f μ + k ∧ a.2 = log := by
  induction oa using OracleComp.inductionOn generalizing log μ k with
  | pure x =>
    unfold LiveRedRun at hrun
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hrun
    rw [hrun.2.1, hrun.2.2]
    exact ⟨Nat.le_add_right _ _, rfl⟩
  | query_bind t k' ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h hna
    unfold LiveRedRun at hrun
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hrun
    obtain ⟨⟨y, log₁, μ₁⟩, h₁, h₂⟩ := hrun
    have hna' : QueryCostAtMost (k' y) (ansCost (R' := R')) 0 := by
      have h2 := hna.2 y
      rwa [Nat.zero_sub] at h2
    rcases t with (n | z) | q'
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd .red) (.inl n)).run μ) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      change (y', μ₂) ∈ support ((fun b ↦ (b, μ)) <$>
        liftM (romWorld.Oracles.query (.inl n))) at h₃
      rw [support_map] at h₃
      obtain ⟨_, _, he'⟩ := h₃
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      rw [← (Prod.mk.inj he').2] at h₂
      have := ih y (h.2 y) hna' h₂
      exact ⟨this.1.trans (Nat.add_le_add_left (Nat.sub_le _ _) _), this.2⟩
    · change (y, log₁, μ₁) ∈ support ((fun p ↦ (p.1, (log, p.2))) <$>
        (liveImpl rl (upd .red) (.inr z)).run μ) at h₁
      rw [support_map] at h₁
      obtain ⟨⟨y', μ₂⟩, h₃, he⟩ := h₁
      change (y', μ₂) ∈ support ((fun v ↦ (v, stepRd rl (upd .red z) z μ v)) <$>
        liftM (romWorld.Oracles.query (.inr z))) at h₃
      rw [support_map] at h₃
      obtain ⟨v, _, he'⟩ := h₃
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl, rfl⟩ := he
      rw [← (Prod.mk.inj he').2] at h₂
      have := ih y (h.2 y) hna' h₂
      refine ⟨this.1.trans ?_, this.2⟩
      have h1 := hred z μ v
      have h2 := h.1
      change c (.inl (.inr z)) ≤ k at h2
      omega
    · exact absurd hna.1 (by simp [ansCost])

end phase

end Quantum.StdModel.Qrom

end
