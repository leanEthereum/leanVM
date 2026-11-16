module

public import Quantum.Xmss.Assembly.GameT
public import Quantum.Xmss.Assembly.MassesR0

@[expose] public section

/-!
# The graded hybrid masked by a good set, and the read mass split by read class

* **Masked graded hybrid** (`uavg_win_runtime1R_le_graded_total_masked`, padded good sets:
  `uavg_win_runtime1R_le_graded_total_masked_pad`): Graded's `uavg_win_runtime1R_le_graded_total`
  with the masses averaged over a good set `G` only (`0` off `G`), the bad fraction of `G` paid once,
  additively, instead of once per call inside the masses (Masses' `N · bad`).
* **Sequencing** (`totalWeight_diagMass_bind₂`): diagonal masses (hence port masses) of `x.bind k`
  are those of `x` plus those of `k a` from the branches of the run of `x`.
* **Runs of realized templates** (`branch_run_realizeT`, `lazy_run`, `lazy_run_realizeT`): the run
  of `realizeT v y` against `runtimeR` is the run of `y` against the template runtime at `v`, and
  its branches are lazy in the hidden values (ViewBy's `Lazy`) from lazy initial states, for a
  template that reveals before it programs. `querySupportedOn_run_hp`: the branches of a template
  keeping GameTCalls' pending invariant (`HP`) are supported on it.
* **The verification's reads** (`totalWeight_portMass_gameT_split`, `sum_verifyMass_le`): the port
  masses of `gameT` are those of the challenge prefix plus those of the verification from the
  prefix's branches; the latter, from lazy states on the invariant, have MassSources' sources
  (`sourcesSlotInv`), so the verification's reads of hidden path cells weigh `2^-128` each,
  `3 · verifyBlocks` reads.
* **Masked averages** (`uavg_mask_le_of_injOn`, `uavg_mask_totalWeight_portMass_le_r0`,
  `uavg_mask_totalWeight_portMass_le_xmssR0`, `uavg_mask_spongeMass_le_xmssR0`): MassesR0's bounds
  over the good set only, `N (2^-128 + εA + r0Eps G + R |J| / |Z|)` with no bad fraction.
* **The read mass by read class** (`uavg_mask_readMass_le_split`, `uavg_mask_readMass_le_xmssR0`):
  `τ + 3 · verifyBlocks · 2^-128 + clsCap (εA + r0Eps G + 2 lifetime |J| / |Z|)`. Only the
  verification's reads are charged `2^-128`. The randomizer trials' (the challenge prefix's reads')
  path-cell mass is the named hypothesis `htrial` (`τ` per public datum, averaged over the hidden
  values). Its source is not MassSources' (which charges any read of a hidden path cell `2^-128`,
  the keys being public): a trial's `k'`-cell is `π (b, a)` and its `h`-cell `p.2 + c` with `a`,
  `c` the trial's own earlier read outcomes, fresh database values unless the adversary recorded
  the trial's cells (which needs the hidden randomizer base); target
  `clsCap · |path cells| / |Z|` plus the recorded-trial-cell mass (Security's `massCap`).
* **Keccak's sizes** (`kTerm_le_keccak`, `spongeConst_le_keccak`, `readConst_le_keccak`): with the
  seed paths' multiplicity `εA ≤ 2^-219`, the masked sponge constant is at most `2^-128 + 2^-189`
  per sponge call and the read mass at most `τ + 2^-117`.
-/

open IPFunctor Matrix MeasureTheory
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly

/-! ## The masked graded hybrid -/

section masked

/-- Observations of runs are subprobabilities. -/
theorem evalDistMap_apply_le_one {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    {L : LocalSig.{u, v}} (I : L.Interp) {W : QReg → Type w} {A : QReg} {β : Type*}
    [MeasurableSpace β] (x : QuantumComp L spec W A) (ρ : SubState A) (f : (Σ u, W u) → β)
    (s : Set β) : R.evalDistMap I x ρ f s ≤ 1 := by
  let : MeasurableSpace (Σ u, W u) := ⊤
  calc _ ≤ R.evalDistMap I x ρ f Set.univ := measure_mono (Set.subset_univ s)
    _ = R.evalDistMap I x ρ (fun p ↦ p) Set.univ := by
        rw [QuantumRuntime.evalDistMap_apply_univ, QuantumRuntime.evalDistMap_apply_univ]
    _ ≤ 1 := DSubInstrument.outcomeMeasure_apply_univ_le_one _ _

variable {Θ : Type*} [Fintype Θ]

/-- The average of the indicator of the complement of `G` is the bad fraction. -/
theorem uavg_ite_zero_one (G : Θ → Prop) [DecidablePred G] :
    uavg (fun θ ↦ if G θ then (0 : ℝ≥0∞) else 1) =
      (Fintype.card Θ : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ ↦ ¬G θ).card := by
  unfold uavg
  congr 1
  rw [← Finset.sum_boole]
  exact Finset.sum_congr rfl fun θ _ ↦ by by_cases h : G θ <;> simp [h]

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against `runtimeR`, averaged, the masses masked by a good set.** If the averaged
hidden mass at the sponge ports over the good set `G` (`0` off `G`) is at most `μ` and that at the
read ports at most `ν`, then `E P₁ ≤ (√(E P₂) + √(4 q μ) + √ν)² + |θ ∉ G| / |Θ|`: the bad fraction
is paid once, not per call. -/
theorem uavg_win_runtime1R_le_graded_total_masked (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M') (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (q : ℕ)
    (hq : ∀ θ, IFreeM.IsChargeBound (x θ) (portCharge fun i ↦
      if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (G : Θ → Prop) [DecidablePred G] (μ ν : ℝ≥0∞)
    (hμ : uavg (fun θ ↦ if G θ then (runtimeR m₀).totalWeight I
      (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
        ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ μ)
    (hν : uavg (fun θ ↦ if G θ then (runtimeR m₀).totalWeight I
      (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
        ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ ν) :
    uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ^ (2⁻¹ : ℝ) +
        (4 * (q * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 +
        (Fintype.card Θ : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ ↦ ¬G θ).card := by
  set P₁ : Θ → ℝ≥0∞ := fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E
    with hP₁
  set P₂ : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E with hP₂
  set T : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).totalWeight I (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hT
  set V : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).totalWeight I (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hV
  have h0 : (0 : ℝ≥0∞) ^ (2⁻¹ : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have hz : ∀ (c : ℝ≥0∞), ∑' n : ℕ, (4 * if n = 0 then c else 0) ^ (2⁻¹ : ℝ) =
      (4 * c) ^ (2⁻¹ : ℝ) := fun c ↦ by
    rw [tsum_eq_single 0 fun n hn ↦ by simp [hn, h0]]
    simp
  have hθ : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤ P₂ θ ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * if n = 0 then (q : ℝ≥0∞) * T θ else 0) ^ (2⁻¹ : ℝ) + V θ ^ (2⁻¹ : ℝ) := by
    intro θ
    rw [hz]
    refine (sqrt_win_runtime1R_le_graded I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hE).trans
      (add_le_add (add_le_add le_rfl ((tsum_rpow_kindWeight_le (runtimeR m₀) I _ (x θ) (hq θ)
        _ 4).trans_eq ?_)) le_rfl)
    simp only [hT, spongeMass_eq]
    rw [mul_left_comm]
    rfl
  have hm : ∀ θ, (if G θ then P₁ θ else 0) ^ (2⁻¹ : ℝ) ≤ (if G θ then P₂ θ else 0) ^ (2⁻¹ : ℝ) +
      ∑' n : ℕ, (4 * (fun θ n ↦ if n = 0 then (q : ℝ≥0∞) * (if G θ then T θ else 0) else 0) θ n) ^
        (2⁻¹ : ℝ) + (if G θ then V θ else 0) ^ (2⁻¹ : ℝ) := by
    intro θ
    by_cases hG : G θ
    · simp only [hG, ↓reduceIte]
      exact hθ θ
    · simp only [hG, ↓reduceIte, h0]
      exact zero_le
  have h1 := uavg_le_of_hybrid_graded _ _ _ _ hm
  have hu : ∀ n : ℕ, uavg (fun θ ↦ if n = 0 then (q : ℝ≥0∞) * (if G θ then T θ else 0) else 0) =
      if n = 0 then (q : ℝ≥0∞) * uavg (fun θ ↦ if G θ then T θ else 0) else 0 := fun n ↦ by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, uavg_const_mul]
    · simp [hn, uavg]
  simp only [hu, hz] at h1
  have hsplit : uavg P₁ ≤ uavg (fun θ ↦ if G θ then P₁ θ else 0) +
      uavg (fun θ ↦ if G θ then (0 : ℝ≥0∞) else 1) := by
    rw [← uavg_add]
    refine uavg_mono fun θ ↦ ?_
    by_cases hG : G θ
    · simp [hG]
    · simp only [hG, ↓reduceIte, zero_add]
      exact evalDistMap_apply_le_one _ I _ _ _ _
  refine hsplit.trans (add_le_add (h1.trans ?_) (uavg_ite_zero_one G).le)
  refine pow_le_pow_left₀ zero_le (add_le_add (add_le_add ?_ ?_) ?_) 2
  · refine ENNReal.rpow_le_rpow (uavg_mono fun θ ↦ ?_) (by norm_num)
    by_cases hG : G θ <;> simp [hG]
  · exact ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le)
      zero_le) (by norm_num)
  · exact ENNReal.rpow_le_rpow hν (by norm_num)

/-- **The masked graded hybrid with a padded good set**: the good set `G` lives on the table padded
by `E` (as the reparametrizations' good sets do), the masses are averaged over the padded table
(Masses' and this file's masked bounds), and the bad fraction is that of the padded table. -/
theorem uavg_win_runtime1R_le_graded_total_masked_pad {E' : Type*} [Fintype E'] [Nonempty E']
    (L : Θ → Hw X Z) (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M') (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (q : ℕ)
    (hq : ∀ θ, IFreeM.IsChargeBound (x θ) (portCharge fun i ↦
      if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (G : Θ × E' → Prop) [DecidablePred G] (μ ν : ℝ≥0∞)
    (hμ : uavg (fun t : Θ × E' ↦ if G t then (runtimeR m₀).totalWeight I
      (spongeMass (Hhθ t.1) (Hkθ t.1) (Hk'θ t.1)) (x t.1)
        ((ρ t.1).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ μ)
    (hν : uavg (fun t : Θ × E' ↦ if G t then (runtimeR m₀).totalWeight I
      (readMass (Hhθ t.1) (Hkθ t.1) (Hk'θ t.1)) (x t.1)
        ((ρ t.1).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ ν) :
    uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ^ (2⁻¹ : ℝ) +
        (4 * (q * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 +
        (Fintype.card (Θ × E') : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card := by
  have h1 : uavg (fun t : Θ × E' ↦ (runtime1R X Z (L t.1) m₀).evalDistMap I (x t.1) (ρ t.1)
      (f t.1) E) = uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) :=
    uavg_pad (P := E') fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E
  have h2 : uavg (fun t : Θ × E' ↦ (runtimeR m₀).evalDistMap I (x t.1) (ρ t.1) (f t.1) E) =
      uavg (fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) :=
    uavg_pad (P := E') fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E
  have h := uavg_win_runtime1R_le_graded_total_masked I (fun t : Θ × E' ↦ L t.1)
    (fun t ↦ Hhθ t.1) (fun t ↦ Hkθ t.1) (fun t ↦ Hk'θ t.1) (fun t ↦ hL t.1) m₀ (fun t ↦ x t.1)
    (fun t ↦ ρ t.1) (fun t ↦ f t.1) hE q (fun t ↦ hq t.1) G μ ν hμ hν
  rw [h1, h2] at h
  exact h

end masked

/-! ## Diagonal masses add under sequencing -/

section bind

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp)

/-- The diagonal mass of `C` is the trace weight of the projector on `C`, on positive
semidefinite operators. -/
theorem diagMass_eq_ofReal_trace_conj {n : Type} [Fintype n] [DecidableEq n] (C : Set n)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    diagMass C σ = ENNReal.ofReal (MatrixMap.conj (setProj C) σ).trace.re := by
  rw [MatrixMap.trace_conj_apply, conjTranspose_setProj, setProj_mul_self,
    ofReal_trace_setProj_mul C hσ]

/-- Total diagonal masses are total trace weights of the projectors, from positive semidefinite
states. -/
theorem totalWeight_diagMass_eq_conj (C : ∀ i, Set (spec.In i × R.D)) {Ω : QReg → Type w}
    {A : QReg} (x : QuantumComp L spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagMass (C i)) x ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (MatrixMap.conj (setProj (C i)) σ).trace.re) x
        ρ :=
  le_antisymm
    (totalWeight_le_totalWeight R I (fun i _ hσ ↦ (diagMass_eq_ofReal_trace_conj (C i) hσ).le) x
      hρ)
    (totalWeight_le_totalWeight R I (fun i _ hσ ↦ (diagMass_eq_ofReal_trace_conj (C i) hσ).ge) x
      hρ)

/-- **Diagonal masses add under sequencing of fixed-register programs**: the total diagonal mass
of `x.bind k` is that of `x` plus, for every return value `a` of `x`, that of `k a` from the
branch of the run of `x` at `a` (VCVio's `totalWeight_bind`). -/
theorem totalWeight_diagMass_bind₂ (C : ∀ i, Set (spec.In i × R.D)) {A B B' : QReg} {α β : Type}
    (x : QuantumComp₂ L spec A B α) (k : α → QuantumComp₂ L spec B B' β)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i ↦ diagMass (C i)) (x.bind k) ρ =
      R.totalWeight I (fun i ↦ diagMass (C i)) x ρ +
        ∑' a, R.totalWeight I (fun i ↦ diagMass (C i)) (k a) ((R.run₂ I x).branch a ρ) := by
  have hb := R.totalWeight_bind I (Φ := fun i ↦ MatrixMap.conj (setProj (C i)))
    (fun i ↦ MatrixMap.isCP_conj _) x
    (fun u (p : QuantumComp₂.Leaf B α u) ↦ p.casesOn fun h a ↦ h ▸ k a) hρ
  refine (totalWeight_diagMass_eq_conj R I C (Ω := QuantumComp₂.Leaf B' β) (x.bind k) hρ).trans
    (hb.trans (congrArg₂ (· + ·)
      (totalWeight_diagMass_eq_conj R I C (Ω := QuantumComp₂.Leaf B α) x hρ).symm ?_))
  rw [← (QuantumComp₂.leafEquiv B α).tsum_eq]
  exact tsum_congr fun a ↦ (totalWeight_diagMass_eq_conj R I C (Ω := QuantumComp₂.Leaf B' β) (k a)
    ((R.run I x).posSemidef_branch_apply _ hρ)).symm

end bind

/-! ## Lazy families along a run -/

section lazyRun

variable {S : Type} [DecidableEq S] {D : S → Type}
  {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} (I : L.Interp)
  {Ω : QReg → Type w} {Dr : QReg} (init : SubState Dr)
  (step : ((s : S) → D s) → ∀ i, SubInstrument (spec.In i × Dr) (spec.Out i × Dr) (spec.Result i))
  {lab : Dr → Finset S} {need : spec.Port → Finset S}

/-- **The branches of a lazy runtime's run are lazy**: from a lazy family of initial states whose
calls are presented operators supported above `need i`, every branch of the run is lazy. -/
theorem lazy_run (hstep : StepLazy step lab need) {A : QReg} (y : QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × Dr) (A × Dr) ℂ) (hρ : Lazy (fun p ↦ lab p.2) ρ)
    (hsupp : ∀ v, (famRuntime init step v).ForallQueries I (CallSupp lab need) y (ρ v))
    (p : Σ u, Ω u) :
    Lazy (fun q : p.1 × Dr ↦ lab q.2)
      fun v ↦ ((famRuntime init step v).run I y).branch p (ρ v) := by
  classical
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    intro a b v v' h
    simp only [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      simp only [DSubInstrument.branch_ret_self, LinearMap.id_apply]
      exact hρ a b v v' h
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      rfl
  | primBind _ o k ih =>
    intro a b v v' h
    simp only [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    have hs : ∀ u, Summable fun c ↦
        ((famRuntime init step u).run I (k c)).branch p (((I o).frame Dr).branch c (ρ u)) :=
      fun u ↦ (((I o).frame Dr).isCPTNIFamily.comp_eval
        (fun c ↦ ((famRuntime init step u).run I (k c)).isCPTNIFamily) p).summable_apply (ρ u)
    rw [Matrix.tsum_apply_apply (hs v), Matrix.tsum_apply_apply (hs v')]
    exact tsum_congr fun c ↦ ih c _ (lazy_amplify _ hρ)
      (fun u ↦ (forallQueries_primBind_iff I o k _).mp (hsupp u) c) a b v v' h
  | queryBind _ i E ℓ k ih =>
    intro a b v v' h
    simp only [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    have hs : ∀ u, Summable fun r ↦ ((famRuntime init step u).run I (k r)).branch p
        (((famRuntime init step u).queryStep i E ℓ).branch r (ρ u)) :=
      fun u ↦ (((famRuntime init step u).queryStep i E ℓ).isCPTNIFamily.comp_eval
        (fun r ↦ ((famRuntime init step u).run I (k r)).isCPTNIFamily) p).summable_apply (ρ u)
    rw [Matrix.tsum_apply_apply (hs v), Matrix.tsum_apply_apply (hs v')]
    exact tsum_congr fun r ↦ ih r _
      (lazy_queryStep hstep i E ℓ r hρ
        fun u ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp u)).1)
      (fun u ↦ ((forallQueries_queryBind_iff I i E ℓ k _).mp (hsupp u)).2 r) a b v v' h

end lazyRun

end Quantum.Xmss.Hybrid

/-! ## Runs of realized templates -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

section runReal

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  {good : LazyProg X Z S D → Prop} [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {L : LocalSig.{u, v}} (I : L.Interp) {Ω : QReg → Type w}

/-- **Running the realized program** is running the template against the template runtime at
the hidden values (a reveal's branches at other values are zero), branch by branch. -/
theorem branch_run_realizeT (m₀ : Finset S × M) (v : (s : S) → D s) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S D M good) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset S × M))) (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (p : Σ u, Ω u) :
    ((runtimeR m₀).run I (realizeT v y)).branch p ρ =
      ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I y).branch p ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ y => rfl
  | primBind _ o k ih =>
    show (((I o).frame _).bind fun b ↦ (runtimeR m₀).run I (realizeT v (k b))).branch p ρ = _
    exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun b ↦ ih b _).trans
      (DSubInstrument.branch_bind_apply ((I o).frame _)
        (fun b ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k b))
        p ρ).symm)
  | queryBind _ i E ℓ k ih =>
    rcases i with ((i | c) | ⟨p', hp⟩) | T
    · show (DSubInstrument.bind ((runtimeR m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
        fun r ↦ (runtimeR m₀).run I (realizeT v (k r))).branch p ρ = _
      exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun r ↦ ih r _).trans
        (DSubInstrument.branch_bind_apply
          ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep _ E ℓ)
          (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
          p ρ).symm)
    · show (DSubInstrument.bind ((runtimeR m₀).queryStep (.inl (.inl (.inr c.1))) E ℓ)
        fun r ↦ (runtimeR m₀).run I (realizeT v (k r))).branch p ρ = _
      exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun r ↦ ih r _).trans
        (DSubInstrument.branch_bind_apply
          ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep _ E ℓ)
          (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
          p ρ).symm)
    · cases p' with
      | programH T₀ c =>
        show (DSubInstrument.bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ)
          fun r ↦ (runtimeR m₀).run I (realizeT v (k r))).branch p ρ = _
        exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun r ↦ ih r _).trans
          (DSubInstrument.branch_bind_apply
            ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep _ E ℓ)
            (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
            p ρ).symm)
      | programK T₀ c =>
        show (DSubInstrument.bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ)
          fun r ↦ (runtimeR m₀).run I (realizeT v (k r))).branch p ρ = _
        exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun r ↦ ih r _).trans
          (DSubInstrument.branch_bind_apply
            ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep _ E ℓ)
            (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
            p ρ).symm)
      | programK' T₀ c =>
        show (DSubInstrument.bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ)
          fun r ↦ (runtimeR m₀).run I (realizeT v (k r))).branch p ρ = _
        exact (DSubInstrument.branch_bind_apply _ _ p ρ).trans ((tsum_congr fun r ↦ ih r _).trans
          (DSubInstrument.branch_bind_apply
            ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep _ E ℓ)
            (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
            p ρ).symm)
    · have he : ∀ m, ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
          (.inr T) E ℓ).branch (restrictTo T v, m) ρ =
            ((runtimeR m₀).queryStep (.inr T) E ℓ).branch m ρ := fun m ↦ by
        refine (queryStep_branch_apply (R := famRuntime (initHw X Z m₀)
          (tmplStep (good := good) m₀) v) (.inr T) E ℓ (restrictTo T v, m) ρ).trans
          (Eq.trans ?_ (queryStep_branch_apply (R := runtimeR m₀) (.inr T) E ℓ m ρ).symm)
        change (SubInstrument.relabel _).branch ()
          (((revealStep (X := X) (Z := Z) T v).branch (restrictTo T v, m)).amplify E _) = _
        rw [revealStep_branch_self]
        rfl
      have hz : ∀ (w : RevealVals D T) m, w ≠ restrictTo T v →
          ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
            (.inr T) E ℓ).branch (w, m) ρ = 0 := fun w m hw ↦ by
        refine (queryStep_branch_apply (R := famRuntime (initHw X Z m₀)
          (tmplStep (good := good) m₀) v) (.inr T) E ℓ (w, m) ρ).trans ?_
        change (SubInstrument.relabel _).branch ()
          (((revealStep (X := X) (Z := Z) T v).branch (w, m)).amplify E _) = _
        rw [revealStep_branch_of_ne T v hw m]
        simp only [MatrixMap.amplify_zero]
        exact map_zero _
      set F : RevealVals D T × (Finset S × M) → Matrix
          (QReg.of ((tmplSpec X Z S D M good).Out (.inr T) × E) × QReg.of (HwReg X Z (Finset S × M)))
          (QReg.of ((tmplSpec X Z S D M good).Out (.inr T) × E) × QReg.of (HwReg X Z (Finset S × M)))
          ℂ → Matrix (p.1 × QReg.of (HwReg X Z (Finset S × M)))
            (p.1 × QReg.of (HwReg X Z (Finset S × M))) ℂ :=
        fun r ↦ ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r)).branch p
      have key : ∑' r : RevealVals D T × (Finset S × M), F r
          (((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
            (.inr T) E ℓ).branch r ρ) =
          ∑' m : Finset S × M, F (restrictTo T v, m)
            (((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep
              (.inr T) E ℓ).branch (restrictTo T v, m) ρ) := by
        rw [tsum_fintype, tsum_fintype, Fintype.sum_prod_type,
          Finset.sum_eq_single (restrictTo T v)
            (fun w _ hw ↦ Finset.sum_eq_zero fun m _ ↦ by rw [hz w m hw]; exact map_zero _)
            (fun h ↦ absurd (Finset.mem_univ _) h)]
      refine (DSubInstrument.branch_bind_apply ((runtimeR m₀).queryStep (.inr T) E ℓ)
        (fun m ↦ (runtimeR m₀).run I (realizeT v (k (restrictTo T v, m)))) p ρ).trans
        (Eq.trans ?_ (key.symm.trans (DSubInstrument.branch_bind_apply
          ((famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).queryStep (.inr T) E ℓ)
          (fun r ↦ (famRuntime (initHw X Z m₀) (tmplStep (good := good) m₀) v).run I (k r))
          p ρ).symm))
      exact tsum_congr fun m ↦ (ih _ _).trans (congrArg _ (he m).symm)

/-- **The branches of a realized template's run are lazy**, from a lazy family of initial states,
for a template that reveals before it programs. -/
theorem lazy_run_realizeT (m₀ : Finset S × M) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z S D M good) Ω A) (T : Finset S) (hy : Disc y T)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M)))
      (A × QReg.of (HwReg X Z (Finset S × M))) ℂ)
    (hρ : Lazy (fun p ↦ p.2.2.2.1) ρ)
    (hT : ∀ v, SuppAt (fun p : A × QReg.of (HwReg X Z (Finset S × M)) ↦ p.2.2.2.1) T (ρ v))
    (p : Σ u, Ω u) :
    Lazy (fun q : p.1 × QReg.of (HwReg X Z (Finset S × M)) ↦ q.2.2.2.1)
      fun v ↦ ((runtimeR m₀).run I (realizeT v y)).branch p (ρ v) := by
  simp only [branch_run_realizeT]
  exact lazy_run I (initHw X Z m₀) (tmplStep m₀) (stepLazy_tmplStep m₀) y ρ hρ
    (fun v ↦ forallQueries_of_disc I m₀ v y T hy (ρ v) (hT v)) p

end runReal

/-! ## The read mass of the template game, split at the verification -/

section verify

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- Support of a composite's branch from the supports of the continuation's branches. -/
theorem querySupportedOn_branch_bind {A' : Type*} [Fintype A'] {ι κ : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)] (d : DSubInstrument A' ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) (ρ : Matrix A' A' ℂ) {Y : Type*}
    {q : C c → Y} {S' : Set Y} (h : ∀ i, QuerySupportedOn q S' ((k i).branch c (d.branch i ρ))) :
    QuerySupportedOn q S' ((d.bind k).branch c ρ) := by
  rw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum h

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The pending invariant along a run** of a realized template keeping it (`HP`): every
branch of the run is supported on the invariant with the final pending set. -/
theorem querySupportedOn_run_hp (m₀ : Finset HPos × M) (I : L.Interp) (pub : Pub)
    (v : HPos → Digest) {A : QReg} (y : QuantumComp L (XSpec M) Ω A) :
    ∀ C C', HP pub v y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v C s} ρ →
      ∀ p : Σ u, Ω u, QuerySupportedOn (fun m : p.1 × (runtimeR m₀).D ↦ m.2)
        {s | InvP pub v C' s} (((runtimeR m₀).run I (realizeT v y)).branch p ρ) := by
  classical
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    intro C C' hy ρ hρ p
    show QuerySupportedOn _ _
      ((DSubInstrument.ret (fun p : Σ u, Ω u ↦ p.1 × (runtimeR m₀).D) ⟨_, y⟩).branch p ρ)
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.imp fun _ h ↦ invP_mono hy h
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    intro C C' hy ρ hρ p
    show QuerySupportedOn _ _
      ((((I o).frame _).bind fun b ↦ (runtimeR m₀).run I (realizeT v (k b))).branch p ρ)
    exact querySupportedOn_branch_bind ((I o).frame _)
      (fun b ↦ (runtimeR m₀).run I (realizeT v (k b))) p ρ fun b ↦ ih b C C' (hy.2 (ULift.up b))
      _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _) p
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ p
    rcases i with ((i | c) | ⟨p', hp⟩) | T
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      exact ih r C C' (hy.2 (ULift.up r)) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inl (.inl (.inl i))) r
          (stepInv_sponge m₀ pub v i C r) E ℓ hρ) p
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inl (.inl (.inr c.1))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      exact ih r C C' (hy.2 (ULift.up r)) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inl (.inl (.inr c.1))) r
          (stepInv_read m₀ pub v c hy.1.2 C r) E ℓ hρ) p
    · cases p' with
      | programH T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programH T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
      | programK T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programK T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
      | programK' T₀ c =>
        refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r _ C' (hy.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s)
            (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) r
            (stepInv_prog m₀ pub v _ C r) E ℓ hρ) p
    · refine querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inr T) E ℓ)
        (fun m ↦ (runtimeR m₀).run I (realizeT v (k (restrictTo T v, m)))) p ρ fun m ↦ ?_
      exact ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m))) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inr T) m
          (stepInv_rec m₀ pub v T C m) E ℓ hρ) p

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- The challenge prefix keeps the invariant. -/
theorem hp_prefixT (pub : Pub) (v : HPos → Digest) (A : Adversary (X × Z)) :
    HP pub v (prefixT M upd pub A) ∅ ∅ :=
  hp_revealThen pub v _ _ fun _ ↦ hp_mono pub v _
    (hp₂_bind pub v _ _ (hp_substitute pub v _ (hp_challengeT pub v upd) _) fun _ ↦ subset_rfl)
    (revealSet_rootPos pub v) subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- The verification keeps the invariant. -/
theorem hp_verifyT (pub : Pub) (v : HPos → Digest) (x : PublicKey × (Forgery × SignLog)) :
    HP pub v (verifyT M pub x) ∅ ∅ :=
  hp₂_bind pub v _ _ (hp_readLift pub v _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- The verification programs nothing. -/
theorem disc_verifyT (pub : Pub) (x : PublicKey × (Forgery × SignLog)) (T : Finset HPos) :
    Disc (verifyT M pub x) T :=
  disc₂_bind _ _ (disc_readLift _ _) fun _ _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The verification's read and record calls**: at most `3 · verifyBlocks` (three reads per
block, no record call). -/
theorem chg_verifyT (pub : Pub) (v : HPos → Digest) (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (realizeT v (verifyT M pub x))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) (3 * verifyBlocks) := by
  have he : (fun i ↦ if readRecPort M i = true then 1 else 0) = rCharge M 0 1 0 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine isChargeBound_realizeT 0 1 0 1 v ?_
  have hv := chg_readsProgram (M := M) 0 1 pub.perm (QReg.of Unit) (verify_cost' x.1 x.2.1)
  unfold verifyT
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (isChargeBound_readLift 0 1 0 1 (chg_map _ Prod.fst hv)) fun _ ↦ trivial)
    (by rw [Nat.add_zero, Nat.mul_one])

/-- **The port masses of the template game split at the verification**: those of the challenge
prefix, plus, for every return value of the prefix, those of the verification from the prefix's
branch at it. -/
theorem totalWeight_portMass_gameT_split (Q : (recHwSpec X Z HPos M).Port → Prop)
    [DecidablePred Q] (m₀ : Finset HPos × M) (pub : Pub) (A : Adversary (X × Z))
    (v : HPos → Digest) (Hh : Set Z) (Hk Hk' : Set X)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef) :
    (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
      (realizeT v (gameT M upd pub A)) ρ =
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (realizeT v (prefixT M upd pub A)) ρ +
      ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (realizeT v (verifyT M pub a))
        (((runtimeR m₀).run₂ LocalSig.Interp.instruments
          (realizeT v (prefixT M upd pub A))).branch a ρ) := by
  rw [gameT_eq_prefixT_bind, realizeT_bind₂, portMass_eq_diagMass]
  exact totalWeight_diagMass_bind₂ (runtimeR m₀) _ _ _ _ hρ

/-- **The verification's hidden masses** (Disclose's sources, `sourcesSlotInv`, on the
verification run from the prefix's branches, which are lazy and on the invariant): summed over
the hidden values, the hidden masses at the read and record calls of the verification are at most
`2^-128` per verification read, `3 · verifyBlocks` of them. -/
theorem sum_verifyMass_le (pub : Pub) (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ) :
    ∑ v : HPos → Digest, ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH pub fun q ↦ v (.inl q))
        (hidK pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
      (realizeT v (verifyT M pub a))
      (((runtimeR m₀).run₂ LocalSig.Interp.instruments
        (realizeT v (prefixT M upd pub A))).branch a ρ) ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card (HPos → Digest)) := by
  set br : (HPos → Digest) → PublicKey × (Forgery × SignLog) →
      Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
        (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ := fun v a ↦
    ((runtimeR m₀).run₂ LocalSig.Interp.instruments (realizeT v (prefixT M upd pub A))).branch a ρ
  have hpos : ∀ v a, (br v a).PosSemidef := fun v a ↦
    ((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pub A))).posSemidef_branch_apply a hρ
  have hlazy : ∀ a, Lazy (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) fun v ↦ br v a := fun a ↦
    lazy_run_realizeT LocalSig.Interp.instruments m₀ (prefixT M upd pub A) ∅
      (disc_prefixT M upd pub A ∅) (fun _ ↦ ρ) (lazy_const _ ρ) (fun _ ↦ suppAt_empty _ ρ)
      ⟨_, rfl, a⟩
  have hinv : ∀ a v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) (fun i ↦ readRecPort M i = true) (SlotInv M pub v))
      (realizeT v (verifyT M pub a)) (br v a) := fun a v ↦
    forallQueries_of_hp (fun c ↦ readRecPort_prog c) m₀ _ pub v _ ∅ ∅ (hp_verifyT pub v a) _
      (querySupportedOn_run_hp m₀ _ pub v (prefixT M upd pub A) ∅ ∅ (hp_prefixT upd pub v A) ρ
        (hs.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha)) ⟨_, rfl, a⟩)
  have hper : ∀ a, ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH pub fun q ↦ v (.inl q))
        (hidK pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
      (realizeT v (verifyT M pub a)) (br v a) ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * ∑ v, ENNReal.ofReal (br v a).trace.re) := fun a ↦
    sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments
      (fun i ↦ readRecPort M i = true) m₀ (fun r ↦ r.2.2.1)
      (fun v ↦ realizeT v (verifyT M pub a)) (fun v ↦ br v a) (fun v ↦ hpos v a)
      (fun j ↦ (viewBy_runtimeR_of_disc LocalSig.Interp.instruments m₀ (verifyT M pub a) ∅
        (disc_verifyT pub a ∅) (fun v ↦ br v a) (hlazy a) (fun _ ↦ suppAt_empty _ _) j).viewByOn _)
      (fun v ↦ SlotInv M pub v) (hinv a) _ _ _ _ (sourcesSlotInv M pub)
      fun v ↦ chg_verifyT pub v a
  have htr : ∀ v, ∑' a, ENNReal.ofReal (br v a).trace.re ≤ 1 := fun v ↦
    (((runtimeR m₀).run₂ LocalSig.Interp.instruments
      (realizeT v (prefixT M upd pub A))).isCPTNIFamily.tsum_ofReal_trace_re_le hρ).trans hρ1
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  calc ∑' a, ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (hidH pub fun q ↦ v (.inl q))
          (hidK pub fun q ↦ v (.inl q)) (hidK' pub fun q ↦ v (.inl q)))
        (realizeT v (verifyT M pub a)) (br v a)
      ≤ ∑' a, (Fintype.card Digest : ℝ≥0∞)⁻¹ *
          (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * ∑ v, ENNReal.ofReal (br v a).trace.re) :=
        ENNReal.tsum_le_tsum hper
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) *
          ∑ v : HPos → Digest, ∑' a, ENNReal.ofReal (br v a).trace.re) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
          Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
    _ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) *
          ∑ _v : HPos → Digest, (1 : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun v _ ↦ htr v) zero_le) zero_le
    _ = (Fintype.card Digest : ℝ≥0∞)⁻¹ *
          (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card (HPos → Digest)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end verify

/-! ## Masked averages through a reparametrization -/

section maskAvg

/-- **The masked table average through an injection on a good set**: Masses'
`uavg_le_of_injOn` with `f` masked to `0` off the good set `G`, so that no bad fraction appears. -/
theorem uavg_mask_le_of_injOn {Θ E P V : Type*} [Fintype Θ] [Fintype E] [Fintype P] [Fintype V]
    (e : Θ × E → P × V) (G : Θ × E → Prop) [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card V ≤ Fintype.card (Θ × E))
    (f : Θ × E → ℝ≥0∞) (g : P → V → ℝ≥0∞) (hfg : ∀ t, G t → f t ≤ g (e t).1 (e t).2)
    (κ : ℝ≥0∞) (hg : ∀ p, ∑ v, g p v ≤ κ * Fintype.card V) :
    uavg (fun t ↦ if G t then f t else 0) ≤ κ := by
  classical
  set N : ℝ≥0∞ := (Fintype.card (Θ × E) : ℝ≥0∞)
  have hgood : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 ≤ κ * N := by
    have himg : ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2 =
        ∑ y ∈ (Finset.univ.filter G).image e, g y.1 y.2 := by
      refine (Finset.sum_image (f := fun y : P × V ↦ g y.1 y.2) ?_).symm
      intro a ha b hb h
      exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2 h
    calc ∑ t ∈ Finset.univ.filter G, g (e t).1 (e t).2
        ≤ ∑ y : P × V, g y.1 y.2 := by
          rw [himg]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ p, ∑ v, g p v := Fintype.sum_prod_type _
      _ ≤ ∑ _p : P, κ * Fintype.card V := Finset.sum_le_sum fun p _ ↦ hg p
      _ = κ * ((Fintype.card P : ℝ≥0∞) * Fintype.card V) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ κ * N := mul_le_mul_of_nonneg_left (by rw [← Nat.cast_mul]; exact Nat.cast_le.mpr hcard)
          zero_le
  unfold uavg
  rw [← Finset.sum_filter]
  calc N⁻¹ * ∑ t ∈ Finset.univ.filter G, f t
      ≤ N⁻¹ * (κ * N) := mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun t ht ↦
          hfg t (Finset.mem_filter.mp ht).2).trans hgood) zero_le
    _ = κ * (N⁻¹ * N) := by ring
    _ ≤ κ := by
        by_cases h0 : N = 0
        · simp [h0]
        · rw [ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), mul_one]

end maskAvg

/-! ## The masked hidden masses of the template game -/

section masses

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The masked averaged total hidden mass at the ports `Q`, with the mismatch**:
`uavg_totalWeight_portMass_le_r0` over the good set only, `N (κ + εK + R εB)`, with no bad
fraction. -/
theorem uavg_mask_totalWeight_portMass_le_r0 (Q : (recHwSpec X Z HPos M).Port → Prop)
    [DecidablePred Q] (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P K : Type} [Fintype E] [Fintype P] [Fintype K]
    (e : HonestTable × E → P × ((HPos → Digest) × K)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × K) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (B : P → K → Finset HPos)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ B (e t).1 (e t).2.2) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (Hhv : P → (HPos → Digest) → Set Z) (Hkv Hk'v : P → (HPos → Digest) → Set X)
    (Hhk : P → K → Set Z) (Hkk Hk'k : P → K → Set X)
    (hsub : ∀ t, G t →
      Hh t.1 ⊆ Hhv (e t).1 (e t).2.1 ∪ Hhk (e t).1 (e t).2.2 ∧
      Hk t.1 ⊆ Hkv (e t).1 (e t).2.1 ∪ Hkk (e t).1 (e t).2.2 ∧
      Hk' t.1 ⊆ Hk'v (e t).1 (e t).2.1 ∪ Hk'k (e t).1 (e t).2.2)
    (Inv : P → (HPos → Digest) → HwReg X Z (Finset HPos × M) → Prop)
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (Inv p v)) (realizeT v (gameT M upd (pubP p) A)) ρ)
    (κ : ℝ≥0∞)
    (src : ∀ p, Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (Inv p) (Hhv p) (Hkv p)
      (Hk'v p) κ)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card K)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (J : Finset HPos) (hBJ : ∀ p k, B p k ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ p, ∀ s ∈ J,
      ((Finset.univ.filter fun k ↦ s ∈ B p k).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M J)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments (portMass Q (Hh t.1) (Hk t.1) (Hk' t.1))
        (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      N * (κ + εK + R * εB) := by
  refine uavg_mask_le_of_injOn e G hinj hcard _
    (fun p w ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhv p w.1) (Hkv p w.1) (Hk'v p w.1)) (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhk p w.2) (Hkk p w.2) (Hk'k p w.2)) (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      N * revW m₀ LocalSig.Interp.instruments (B p w.2) (realizeT w.1 (gameT M upd (pubP p) A)) ρ)
    (fun t ht ↦ ?_) (N * (κ + εK + R * εB)) fun p ↦ ?_
  · obtain ⟨v, hv, hgeq⟩ := hgame t ht
    obtain ⟨h1, h2, h3⟩ := hsub t ht
    rw [hgeq]
    refine (totalWeight_portMass_le_mismatch m₀ LocalSig.Interp.instruments
      (gameT M upd (pubP (e t).1) A) (disc_gameT M upd _ A ∅) (keepsLab_gameT upd _ A) ρ hρ hs
      (B (e t).1 (e t).2.2) (Finset.disjoint_empty_left _) Q (Hh t.1) (Hk t.1) (Hk' t.1) hv
      (hN _ v)).trans (add_le_add ?_ le_rfl)
    exact (totalWeight_portMass_mono _ Q m₀ h1 h2 h3 _ hρ).trans
      (totalWeight_portMass_union_le _ Q m₀ _ _ _ _ _ _ _ hρ)
  · have hpath : ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v)) (realizeT v (gameT M upd (pubP p) A)) ρ ≤
        κ * N * Fintype.card (HPos → Digest) := by
      refine (sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments Q m₀
        (fun r ↦ r.2.2.1) (fun v ↦ realizeT v (gameT M upd (pubP p) A)) (fun _ ↦ ρ) (fun _ ↦ hρ)
        (fun j ↦ viewByOn_gameT M upd (pubP p) A m₀ ρ j) (Inv p) (hinv p) (Hhv p) (Hkv p)
        (Hk'v p) κ (src p) (fun v ↦ hN (pubP p) v)).trans ?_
      calc κ * (N * ∑ _v : HPos → Digest, ENNReal.ofReal ρ.trace.re)
          ≤ κ * (N * ∑ _v : HPos → Digest, (1 : ℝ≥0∞)) := by gcongr
        _ = κ * N * Fintype.card (HPos → Digest) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_assoc]
    have hK : ∀ v : HPos → Digest, ∑ k, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hhk p k) (Hkk p k) (Hk'k p k)) (realizeT v (gameT M upd (pubP p) A)) ρ ≤
        εK * N * Fintype.card K := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments Q m₀ _ hρ (Hhk p) (Hkk p)
        (Hk'k p) εK (hcH p) (hcK p) (hcK' p) (hN _ v)).trans
        (by calc (εK * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card K) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card K := by ring)
    have hrev : ∀ v : HPos → Digest, ∑ k, revW m₀ LocalSig.Interp.instruments (B p k)
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ R * εB * Fintype.card K := fun v ↦
      (sum_revW_le m₀ LocalSig.Interp.instruments _ hρ (B p) J (hBJ p) εB (hεB p) (hR _ v)).trans
        (by calc (Fintype.card K : ℝ≥0∞) * (R * εB * ENNReal.ofReal ρ.trace.re)
              ≤ Fintype.card K * (R * εB * 1) := by gcongr
            _ = R * εB * Fintype.card K := by ring)
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : K,
          ((runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass Q (Hhv p (v, k).1) (Hkv p (v, k).1) (Hk'v p (v, k).1))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass Q (Hhk p (v, k).2) (Hkk p (v, k).2) (Hk'k p (v, k).2))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          N * revW m₀ LocalSig.Interp.instruments (B p (v, k).2)
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ)
        ≤ ∑ v : HPos → Digest, (Fintype.card K * (runtimeR m₀).totalWeight
            LocalSig.Interp.instruments (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v))
            (realizeT v (gameT M upd (pubP p) A)) ρ +
          (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          dsimp only
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, add_assoc]
          exact add_le_add le_rfl (add_le_add (hK v) (mul_le_mul_of_nonneg_left (hrev v) zero_le))
      _ = Fintype.card K * ∑ v : HPos → Digest, (runtimeR m₀).totalWeight
            LocalSig.Interp.instruments (portMass Q (Hhv p v) (Hkv p v) (Hk'v p v))
            (realizeT v (gameT M upd (pubP p) A)) ρ +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ Fintype.card K * (κ * N * Fintype.card (HPos → Digest)) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := add_le_add (mul_le_mul_of_nonneg_left hpath zero_le) le_rfl
      _ = N * (κ + εK + R * εB) * Fintype.card ((HPos → Digest) × K) := by
          rw [Fintype.card_prod, Nat.cast_mul]
          ring

/-- **The masked read mass, split by read class.** The read mass of the template game over the
good set, on the read and record ports, is split at the verification
(`totalWeight_portMass_gameT_split`). The challenge prefix's reads (the randomizer trials) are
charged by the named hypothesis `htrial` on the template's hidden path cells (`τ` per public datum,
averaged over the hidden values); the verification's reads by Disclose's sources
(`sum_verifyMass_le`, `2^-128` each, `3 · verifyBlocks` of them); every read and record call by
the never-revealed families (`εK` per call, `N` calls) and the mismatch (`R εB` per call). No bad
fraction appears. -/
theorem uavg_mask_readMass_le_split (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    {E P K : Type} [Fintype E] [Fintype P] [Fintype K]
    (e : HonestTable × E → P × ((HPos → Digest) × K)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × K) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (B : P → K → Finset HPos)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ B (e t).1 (e t).2.2) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (Hhk : P → K → Set Z) (Hkk Hk'k : P → K → Set X)
    (hsub : ∀ t, G t →
      Hh t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hhk (e t).1 (e t).2.2 ∧
      Hk t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hkk (e t).1 (e t).2.2 ∧
      Hk' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∪ Hk'k (e t).1 (e t).2.2)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card K)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card K)
    (J : Finset HPos) (hBJ : ∀ p k, B p k ⊆ J) (εB : ℝ≥0∞)
    (hεB : ∀ p, ∀ s ∈ J,
      ((Finset.univ.filter fun k ↦ s ∈ B p k).card : ℝ≥0∞) ≤ εB * Fintype.card K)
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M J)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) N)
    (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd (pubP p) A)) ρ ≤ τ * Fintype.card (HPos → Digest)) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments (readMass (Hh t.1) (Hk t.1) (Hk' t.1))
        (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * (εK + R * εB) := by
  simp only [readMass_eq_portMass]
  refine uavg_mask_le_of_injOn e G hinj hcard _
    (fun p w ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ w.1 (.inl q))
          (hidK (pubP p) fun q ↦ w.1 (.inl q)) (hidK' (pubP p) fun q ↦ w.1 (.inl q)))
        (realizeT w.1 (prefixT M upd (pubP p) A)) ρ +
      ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ w.1 (.inl q))
          (hidK (pubP p) fun q ↦ w.1 (.inl q)) (hidK' (pubP p) fun q ↦ w.1 (.inl q)))
        (realizeT w.1 (verifyT M (pubP p) a))
        (((runtimeR m₀).run₂ LocalSig.Interp.instruments
          (realizeT w.1 (prefixT M upd (pubP p) A))).branch a ρ) +
      (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hhk p w.2) (Hkk p w.2) (Hk'k p w.2))
        (realizeT w.1 (gameT M upd (pubP p) A)) ρ +
      N * revW m₀ LocalSig.Interp.instruments (B p w.2) (realizeT w.1 (gameT M upd (pubP p) A)) ρ)
    (fun t ht ↦ ?_) _ fun p ↦ ?_
  · obtain ⟨v, hv, hgeq⟩ := hgame t ht
    obtain ⟨h1, h2, h3⟩ := hsub t ht
    dsimp only
    rw [hgeq]
    refine (totalWeight_portMass_le_mismatch m₀ LocalSig.Interp.instruments
      (gameT M upd (pubP (e t).1) A) (disc_gameT M upd _ A ∅) (keepsLab_gameT upd _ A) ρ hρ hs
      (B (e t).1 (e t).2.2) (Finset.disjoint_empty_left _) _ (Hh t.1) (Hk t.1) (Hk' t.1) hv
      (hN _ v)).trans (add_le_add ?_ le_rfl)
    exact (totalWeight_portMass_mono _ _ m₀ h1 h2 h3 _ hρ).trans
      ((totalWeight_portMass_union_le _ _ m₀ _ _ _ _ _ _ _ hρ).trans (add_le_add
        (le_of_eq (totalWeight_portMass_gameT_split upd _ m₀ _ A _ _ _ _ ρ hρ)) le_rfl))
  · have hver := sum_verifyMass_le upd (pubP p) A m₀ ρ hρ hρ1 hs
    rw [card_digest_inv] at hver
    have hK : ∀ v : HPos → Digest, ∑ k, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
        (portMass (fun i ↦ readRecPort M i = true) (Hhk p k) (Hkk p k) (Hk'k p k))
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ εK * N * Fintype.card K := fun v ↦
      (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments _ m₀ _ hρ (Hhk p) (Hkk p)
        (Hk'k p) εK (hcH p) (hcK p) (hcK' p) (hN _ v)).trans
        (by calc (εK * Fintype.card K) * (N * ENNReal.ofReal ρ.trace.re)
              ≤ (εK * Fintype.card K) * (N * 1) := by gcongr
            _ = εK * N * Fintype.card K := by ring)
    have hrev : ∀ v : HPos → Digest, ∑ k, revW m₀ LocalSig.Interp.instruments (B p k)
        (realizeT v (gameT M upd (pubP p) A)) ρ ≤ R * εB * Fintype.card K := fun v ↦
      (sum_revW_le m₀ LocalSig.Interp.instruments _ hρ (B p) J (hBJ p) εB (hεB p) (hR _ v)).trans
        (by calc (Fintype.card K : ℝ≥0∞) * (R * εB * ENNReal.ofReal ρ.trace.re)
              ≤ Fintype.card K * (R * εB * 1) := by gcongr
            _ = R * εB * Fintype.card K := by ring)
    rw [Fintype.sum_prod_type]
    calc ∑ v : HPos → Digest, ∑ k : K,
          ((runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ (v, k).1 (.inl q))
              (hidK (pubP p) fun q ↦ (v, k).1 (.inl q))
              (hidK' (pubP p) fun q ↦ (v, k).1 (.inl q)))
            (realizeT (v, k).1 (prefixT M upd (pubP p) A)) ρ +
          ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ (v, k).1 (.inl q))
              (hidK (pubP p) fun q ↦ (v, k).1 (.inl q))
              (hidK' (pubP p) fun q ↦ (v, k).1 (.inl q)))
            (realizeT (v, k).1 (verifyT M (pubP p) a))
            (((runtimeR m₀).run₂ LocalSig.Interp.instruments
              (realizeT (v, k).1 (prefixT M upd (pubP p) A))).branch a ρ) +
          (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (Hhk p (v, k).2) (Hkk p (v, k).2)
              (Hk'k p (v, k).2))
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ +
          N * revW m₀ LocalSig.Interp.instruments (B p (v, k).2)
            (realizeT (v, k).1 (gameT M upd (pubP p) A)) ρ)
        ≤ ∑ v : HPos → Digest, (Fintype.card K * ((runtimeR m₀).totalWeight
            LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
              (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
            (realizeT v (prefixT M upd (pubP p) A)) ρ +
          ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
              (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
            (realizeT v (verifyT M (pubP p) a))
            (((runtimeR m₀).run₂ LocalSig.Interp.instruments
              (realizeT v (prefixT M upd (pubP p) A))).branch a ρ)) +
          (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          dsimp only
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, add_assoc]
          exact add_le_add le_rfl (add_le_add (hK v) (mul_le_mul_of_nonneg_left (hrev v) zero_le))
      _ = Fintype.card K * (∑ v : HPos → Digest, (runtimeR m₀).totalWeight
            LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
              (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
            (realizeT v (prefixT M upd (pubP p) A)) ρ +
          ∑ v : HPos → Digest, ∑' a, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
            (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
              (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
            (realizeT v (verifyT M (pubP p) a))
            (((runtimeR m₀).run₂ LocalSig.Interp.instruments
              (realizeT v (prefixT M upd (pubP p) A))).branch a ρ)) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card K * (τ * Fintype.card (HPos → Digest) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ * (((3 * verifyBlocks : ℕ) : ℝ≥0∞) * Fintype.card (HPos → Digest))) +
          Fintype.card (HPos → Digest) * (εK * N * Fintype.card K + N * (R * εB * Fintype.card K))
          := add_le_add (mul_le_mul_of_nonneg_left (add_le_add (htrial p) hver) zero_le) le_rfl
      _ = (τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) + N * (εK + R * εB)) *
          Fintype.card ((HPos → Digest) × K) := by
          rw [Fintype.card_prod, Nat.cast_mul (Fintype.card (HPos → Digest)) (Fintype.card K)]
          ring

/-- **The masked averaged hidden mass at the ports `Q` for leanXMSS's full table** (path, seed and
randomizer-base cells): MassesR0's `uavg_totalWeight_portMass_le_xmssR0` over the good set only,
`N (2^-128 + εA + r0Eps G + R |J| / |Z|)`, the bad fraction left to the masked hybrid. -/
theorem uavg_mask_totalWeight_portMass_le_xmssR0 (Q : (recHwSpec X Z HPos M).Port → Prop)
    [DecidablePred Q] (hQ : ∀ c, ¬Q (.inl (.inr c))) (A : Adversary (X × Z))
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W))
    {R : ℕ} (hR : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (candCharge X Z M rJ)) R)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (portMass Q (pathH t.1 ∪ seedH t.1 ∪ r0H t.1) (pathK t.1 ∪ seedK t.1 ∪ r0K t.1)
        (pathK' t.1 ∪ seedK' t.1 ∪ r0K' t.1))
      (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      N * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps Gπ) +
          R * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) := by
  have e1 : (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z ≤ r0Eps Gπ := le_add_self
  have e2 : 2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ ≤ εA + r0Eps Gπ :=
    (le_self_add.trans le_self_add).trans le_add_self
  have e3 : (Fintype.card RLabel : ℝ≥0∞) * Gπ / Fintype.card Z ≤ r0Eps Gπ :=
    le_add_self.trans le_self_add
  have h := uavg_mask_totalWeight_portMass_le_r0 upd Q A m₀ ρ hρ hρ1 hs
    (fun L ↦ pathH L ∪ seedH L ∪ r0H L) (fun L ↦ pathK L ∪ seedK L ∪ r0K L)
    (fun L ↦ pathK' L ∪ seedK' L ∪ r0K' L) e G hinj hcard pubP
    (fun p k ↦ r0Bk (permP p) (parP p) k.1) hgame
    (fun p v ↦ hidH (pubP p) fun q ↦ v (.inl q)) (fun p v ↦ hidK (pubP p) fun q ↦ v (.inl q))
    (fun p v ↦ hidK' (pubP p) fun q ↦ v (.inl q))
    (fun p k ↦ r0Hk (permP p) (parP p) k.1 ∪ seedHk p k)
    (fun p k ↦ r0Kk (parP p) k.1 ∪ seedKk (parP p) k.1)
    (fun p k ↦ r0K'k Gπ (permP p) (parP p) k.1 ∪ seedK'k p k)
    (fun t ht ↦ by
      obtain ⟨p1, p2, p3⟩ := hpath t ht
      obtain ⟨r1, r2, r3, r4⟩ := hr0 t ht
      obtain ⟨s1, s2⟩ := hseed t ht
      refine ⟨?_, ?_, ?_⟩
      · rintro z ((hz | hz) | hz)
        exacts [Or.inl (p1 hz), Or.inr (Or.inr (s1 hz)), Or.inr (Or.inl (r1 hz))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p2 hx), Or.inr (Or.inr (r4 hx)), Or.inr (Or.inl (r2 hx))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p3 hx), Or.inr (Or.inr (s2 hx)), Or.inr (Or.inl (r3 hx))])
    (fun p v ↦ SlotInv M (pubP p) v) (hinv_gameT upd pubP hQ m₀ A ρ hs) _
    (fun p ↦ sourcesSlotInv M (pubP p)) (εA + r0Eps Gπ)
    (fun p z ↦ (sum_indicator_union_le _ _ z).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0Hk (permP p) (parP p) k) z _ (sum_indicator_r0Hk_le _ _ z)) (hA p z)).trans
      (add_mul_le_add_mul e1 le_rfl))
    (fun p y ↦ (sum_indicator_pad_le (fun k : RK ↦ r0Kk (parP p) k ∪ seedKk (parP p) k) y _
      (sum_indicator_kCells_le _ y)).trans (mul_le_mul_of_nonneg_right e2 zero_le))
    (fun p y ↦ (sum_indicator_union_le _ _ y).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0K'k Gπ (permP p) (parP p) k) y _ (sum_indicator_r0K'k_le _ _ _ y))
      (hA' p y)).trans (add_mul_le_add_mul e3 le_rfl))
    rJ (fun p k ↦ r0Bk_subset _ _ _) ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)
    (fun p s _ ↦ le_of_eq_of_le (card_filter_pad (W := W)
      (fun k : RK ↦ s ∈ r0Bk (permP p) (parP p) k))
      ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
        (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod]))) hR hN
  rwa [card_digest_inv] at h

/-- **Masked `hybSponge` for leanXMSS's full table**: over the good set, the averaged total hidden
mass at the sponge ports is at most `6q (2^-128 + εA + r0Eps G + 2 lifetime |J| / |Z|)`; the bad
fraction is paid once by `uavg_win_runtime1R_le_graded_total_masked`. -/
theorem uavg_mask_spongeMass_le_xmssR0 (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W)) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (spongeMass (pathH t.1 ∪ seedH t.1 ∪ r0H t.1) (pathK t.1 ∪ seedK t.1 ∪ r0K t.1)
        (pathK' t.1 ∪ seedK' t.1 ∪ r0K' t.1))
      (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps Gπ) +
          ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) := by
  have hc : (fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 0 else 1) =
      fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i = false then 1 else 0 :=
    funext fun i ↦ by cases extCls X Z (Finset HPos × M) (recSpec HPos M) i <;> rfl
  exact uavg_mask_totalWeight_portMass_le_xmssR0 upd
    (fun i ↦ extCls X Z (Finset HPos × M) (recSpec HPos M) i = false)
    (fun _ h ↦ Bool.noConfusion h) A m₀ ρ hρ hρ1 hs e G hinj hcard pubP parP permP Gπ hgame
    hpath hr0 seedHk seedK'k εA hseed hA hA' (hR_gameT upd A hperm hsign) fun pub v ↦ by
      rw [← hc]
      exact hN_sponge upd A hperm hsign pub v

/-- **Masked `hybRead` for leanXMSS's full table, split by read class**: over the good set, the
averaged total hidden mass at the read ports is at most
`τ + 3 · verifyBlocks · 2^-128 + clsCap (εA + r0Eps G + 2 lifetime |J| / |Z|)`. The verification's
reads are the only ones charged `2^-128` (`sum_verifyMass_le`); the randomizer trials' path-cell
mass is the named hypothesis `htrial` (target: `clsCap` times the path cells over `|Z|`, plus the
trace of the states whose trial cell the adversary recorded, which needs the hidden randomizer
base); every read and record call pays the never-revealed families and the mismatch. -/
theorem uavg_mask_readMass_le_xmssR0 (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ)
    {E P W : Type} [Fintype E] [Fintype P] [Fintype W]
    (e : HonestTable × E → P × ((HPos → Digest) × (RK × W))) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card ((HPos → Digest) × (RK × W)) ≤
      Fintype.card (HonestTable × E))
    (pubP : P → Pub) (parP : P → PublicParameter) (permP : P → Equiv.Perm (X × Z)) (Gπ : ℕ)
    (hgame : ∀ t, G t → ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permP (e t).1) (parP (e t).1) (e t).2.2.1) v (e t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) = realizeT v (gameT M upd (pubP (e t).1) A))
    (hpath : ∀ t, G t →
      pathH t.1 ⊆ hidH (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubP (e t).1) (fun q ↦ (e t).2.1 (.inl q)))
    (hr0 : ∀ t, G t →
      r0H t.1 ⊆ r0Hk (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parP (e t).1) (e t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k Gπ (permP (e t).1) (parP (e t).1) (e t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parP (e t).1) (e t).2.2.1)
    (seedHk : P → RK × W → Set Z) (seedK'k : P → RK × W → Set X) (εA : ℝ≥0∞)
    (hseed : ∀ t, G t → seedH t.1 ⊆ seedHk (e t).1 (e t).2.2 ∧
      seedK' t.1 ⊆ seedK'k (e t).1 (e t).2.2)
    (hA : ∀ p z, ∑ k, (seedHk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      εA * Fintype.card (RK × W))
    (hA' : ∀ p y, ∑ k, (seedK'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤
      εA * Fintype.card (RK × W))
    (τ : ℝ≥0∞)
    (htrial : ∀ p, ∑ v : HPos → Digest, (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass (fun i ↦ readRecPort M i = true) (hidH (pubP p) fun q ↦ v (.inl q))
        (hidK (pubP p) fun q ↦ v (.inl q)) (hidK' (pubP p) fun q ↦ v (.inl q)))
      (realizeT v (prefixT M upd (pubP p) A)) ρ ≤ τ * Fintype.card (HPos → Digest)) :
    uavg (fun t : HonestTable × E ↦ if G t then (runtimeR m₀).totalWeight
      LocalSig.Interp.instruments
      (readMass (pathH t.1 ∪ seedH t.1 ∪ r0H t.1) (pathK t.1 ∪ seedK t.1 ∪ r0K t.1)
        (pathK' t.1 ∪ seedK' t.1 ∪ r0K' t.1))
      (realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A)) ρ else 0) ≤
      τ + (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((εA + r0Eps Gπ) +
            ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) := by
  have e1 : (Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z ≤ r0Eps Gπ := le_add_self
  have e2 : 2 * (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ ≤ εA + r0Eps Gπ :=
    (le_self_add.trans le_self_add).trans le_add_self
  have e3 : (Fintype.card RLabel : ℝ≥0∞) * Gπ / Fintype.card Z ≤ r0Eps Gπ :=
    le_add_self.trans le_self_add
  exact uavg_mask_readMass_le_split upd A m₀ ρ hρ hρ1 hs
    (fun L ↦ pathH L ∪ seedH L ∪ r0H L) (fun L ↦ pathK L ∪ seedK L ∪ r0K L)
    (fun L ↦ pathK' L ∪ seedK' L ∪ r0K' L) e G hinj hcard pubP
    (fun p k ↦ r0Bk (permP p) (parP p) k.1) hgame
    (fun p k ↦ r0Hk (permP p) (parP p) k.1 ∪ seedHk p k)
    (fun p k ↦ r0Kk (parP p) k.1 ∪ seedKk (parP p) k.1)
    (fun p k ↦ r0K'k Gπ (permP p) (parP p) k.1 ∪ seedK'k p k)
    (fun t ht ↦ by
      obtain ⟨p1, p2, p3⟩ := hpath t ht
      obtain ⟨r1, r2, r3, r4⟩ := hr0 t ht
      obtain ⟨s1, s2⟩ := hseed t ht
      refine ⟨?_, ?_, ?_⟩
      · rintro z ((hz | hz) | hz)
        exacts [Or.inl (p1 hz), Or.inr (Or.inr (s1 hz)), Or.inr (Or.inl (r1 hz))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p2 hx), Or.inr (Or.inr (r4 hx)), Or.inr (Or.inl (r2 hx))]
      · rintro x ((hx | hx) | hx)
        exacts [Or.inl (p3 hx), Or.inr (Or.inr (s2 hx)), Or.inr (Or.inl (r3 hx))])
    (εA + r0Eps Gπ)
    (fun p z ↦ (sum_indicator_union_le _ _ z).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0Hk (permP p) (parP p) k) z _ (sum_indicator_r0Hk_le _ _ z)) (hA p z)).trans
      (add_mul_le_add_mul e1 le_rfl))
    (fun p y ↦ (sum_indicator_pad_le (fun k : RK ↦ r0Kk (parP p) k ∪ seedKk (parP p) k) y _
      (sum_indicator_kCells_le _ y)).trans (mul_le_mul_of_nonneg_right e2 zero_le))
    (fun p y ↦ (sum_indicator_union_le _ _ y).trans <| (add_le_add (sum_indicator_pad_le
      (fun k : RK ↦ r0K'k Gπ (permP p) (parP p) k) y _ (sum_indicator_r0K'k_le _ _ _ y))
      (hA' p y)).trans (add_mul_le_add_mul e3 le_rfl))
    rJ (fun p k ↦ r0Bk_subset _ _ _) ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)
    (fun p s _ ↦ le_of_eq_of_le (card_filter_pad (W := W)
      (fun k : RK ↦ s ∈ r0Bk (permP p) (parP p) k))
      ((mul_le_mul_of_nonneg_right (card_filter_r0Bk_le _ _ s) zero_le).trans_eq
        (by rw [mul_assoc, ← Nat.cast_mul, ← Fintype.card_prod])))
    (hR_gameT upd A hperm hsign) (hN_readRec upd A hperm hsign) τ htrial

end masses

/-! ## The constants at Keccak's sizes -/

section keccak

open HashSig LeanXmss

theorem inv_two_pow_eq_ofReal (n : ℕ) : (2 ^ n : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ n) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

set_option exponentiation.threshold 4096 in
/-- **The never-revealed and mismatch terms per call at Keccak's sizes** (`G = 18`): with the seed
paths' multiplicity `εA ≤ 2^-219`, `εA + r0Eps 18 + 2 lifetime |J| / |Z| ≤ 2^-189`. -/
theorem kTerm_le_keccak {εA : ℝ≥0∞} (hεA : εA ≤ ENNReal.ofReal (1 / 2 ^ 219)) :
    (εA + r0Eps 18) +
        ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z) ≤
      ENNReal.ofReal (1 / 2 ^ 189) := by
  refine (add_le_add (add_le_add hεA r0Eps_le_keccak) revTerm_le_keccak).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- **The masked sponge constant**: per sponge call, `2^-128 + εA + r0Eps 18 + 2 lifetime |J| / |Z|
≤ 2^-128 + 2^-189` (Security's `kappaS` can be `2^-128 + 2^-189` with the masked hybrid). -/
theorem spongeConst_le_keccak {εA : ℝ≥0∞} (hεA : εA ≤ ENNReal.ofReal (1 / 2 ^ 219)) :
    (2 ^ 128 : ℝ≥0∞)⁻¹ + (εA + r0Eps 18) +
        ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z) ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 189 : ℝ≥0∞)⁻¹ := by
  rw [add_assoc, inv_two_pow_eq_ofReal 189]
  exact add_le_add le_rfl (kTerm_le_keccak hεA)

set_option exponentiation.threshold 4096 in
/-- **The masked read constant without the trial term**: the verification's reads at `2^-128`
each and every classical call's never-revealed and mismatch terms,
`3 · verifyBlocks · 2^-128 + clsCap (εA + r0Eps 18 + 2 lifetime |J| / |Z|) ≤ 2^-117`. -/
theorem readConst_le_keccak {εA : ℝ≥0∞} (hεA : εA ≤ ENNReal.ofReal (1 / 2 ^ 219)) :
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ((3 * verifyBlocks : ℕ) : ℝ≥0∞) +
        ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((εA + r0Eps 18) +
            ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) ≤
      ENNReal.ofReal (1 / 2 ^ 117) := by
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left (kTerm_le_keccak hεA) zero_le)).trans ?_
  rw [inv_two_pow_eq_ofReal 128, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [verifyBlocks_eq, signBlocks_eq, progCap_eq]
  norm_num [lifetime, layerCount, layerHeight]

end keccak

end Quantum.Xmss.Assembly

end
