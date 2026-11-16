module

public import Quantum.Xmss.Assembly.RecordPorts
public import Quantum.Sponge.Oracle.Hardwired.Mixed

@[expose] public section

/-!
# The square-root hybrid graded by the sponge calls

The committed hybrids (Kraus, Coins, RecordPorts) bound `√P₁ - √P₂` by `∑ⱼ √(4 μⱼ)` over every
call index `j`. With the challenger's classical calls (about `2^67` of them) that sum is vacuous
even when each mass is tiny. This file grades the hybrid by the sponge calls and sums the classical
calls under one square root.

* **Weights of one kind of call** (`kindWeight R I cls w x ρ n`): the weight `w` of the input of the
  `n`-th call of a port with `cls i = false`, counting those calls only, summed over the paths
  (whatever the index of that call among all calls). `tsum_kindWeight`: summed over `n`, the total
  weight of the quantum ports. `kindWeight_eq_zero_of_isChargeBound`, `tsum_rpow_kindWeight_le`
  (Cauchy-Schwarz over at most `q` quantum calls), `totalWeight_trace_le_of_isChargeBound`.
* **The graded hybrid** (`rpow_inv_two_outcomeLawWith_le_graded`): for two Kraus runtimes on one
  register and a classical label `κ` of the register that both runtimes move along the same maps
  `F i r`, with the Kraus operators of the classical ports equal outside label sets `S i`,
  `√P₁ ≤ √P₂ + ∑ₙ √(kw n) + √(∑ classical masses)`. Here `kw n` is the Kraus weight of the
  difference at the `n`-th quantum call and the classical mass of a classical call the mass of the
  register states labelled in `S i` (`clsMass`). The proof is an induction on the controlled
  runtime of VCVio's hybrid, on states supported on one label: a quantum call adds to the
  distance of the branches (`tsum_dist_queryStep_le`); a classical call either has its input
  labelled outside `S i`, where both runtimes act alike and the distance does not grow, or inside,
  where the rest of the run weighs at most the trace of the branch, `√trace ≤ √(classical mass) +
  √distance`, and the classical mass joins the summed classical masses
  (`rpow_inv_two_tsum_leafW_run_le_graded`).
* **Runtime 1 against `runtimeR`** (`sqrt_win_runtime1R_le_graded`): the label is the hardwired
  cells, the classical masses are the hidden masses at the read ports (`readMass`), the program and
  record ports cost nothing, the sponge calls cost `4` times their hidden mass. Averaged over the
  table: `uavg_win_runtime1R_le_graded` (per sponge call), `uavg_win_runtime1R_le_graded_total`
  (the sponge masses summed, `√(4 q μ)`), from `uavg_le_of_hybrid_graded`.
* **Disclose's bounds relative to the calls of some ports** (`sum_queryWeight_view_le_on`,
  `sum_queryWeight_portMass_runtimeR_le`, `sum_totalWeight_portMass_runtimeR_le`): the hidden mass
  at the `j`-th call is at most `κ` times the trace of the `j`-th call restricted to the ports `Q`,
  so summed over all calls it is at most `κ` times the number of calls of `Q` (sponge calls for
  `spongeMass`, classical calls for `readMass`).
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum.Xmss.Hybrid

open Quantum QuantumRuntime

/-! ## Weights of the calls of one kind -/

section kind

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {A : QReg} (cls : spec.Port → Bool)

/-- The weight `w` of the `n`-th call of a port with `cls i = false` along the paths of a program
tree, folded into functions of the input state and index. -/
noncomputable def kindWeightAux (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L spec) X A →
      Matrix (A × R.D) (A × R.D) ℂ → ℕ → ℝ≥0∞ :=
  fun {_} x ↦ IFreeM.fold (P := QuantumComp.toIPFunctor L spec)
    (D := fun A ↦ Matrix (A × R.D) (A × R.D) ℂ → ℕ → ℝ≥0∞)
    (fun _ _ _ _ ↦ 0)
    (fun _ cmd next ↦ match cmd with
      | .prim o => fun ρ n ↦ ∑' b, next (ULift.up b) (((I o).frame R.D).branch b ρ) n
      | .query i E ℓ => fun ρ n ↦ if cls i then
          ∑' r, next (ULift.up r) ((R.queryStep i E ℓ).branch r ρ) n
        else if n = 0 then w i (callInput ℓ R.D ρ)
        else ∑' r, next (ULift.up r) ((R.queryStep i E ℓ).branch r ρ) (n - 1)) x

/-- **The weight of the `n`-th quantum call.** For a weight `w i` on the inputs of the calls, the
sum over the paths of `x`, run against `R` from `ρ`, of the weight of the input of the `n`-th call
of a port with `cls i = false` (counting those calls only, from `0`), whatever its index among all
calls. -/
noncomputable def kindWeight (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) : ℝ≥0∞ :=
  kindWeightAux R I cls w x ρ n

variable {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

@[simp]
theorem kindWeight_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls w (QuantumComp.pure (L := L) (spec := spec) y) ρ n = 0 :=
  rfl

theorem kindWeight_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls w (QuantumComp.primBind o k) ρ n =
      ∑' b, kindWeight R I cls w (k b) (((I o).frame R.D).branch b ρ) n :=
  rfl

theorem kindWeight_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls w (QuantumComp.queryBind i E ℓ k) ρ n =
      if cls i then ∑' r, kindWeight R I cls w (k r) ((R.queryStep i E ℓ).branch r ρ) n
      else if n = 0 then w i (callInput ℓ R.D ρ)
      else ∑' r, kindWeight R I cls w (k r) ((R.queryStep i E ℓ).branch r ρ) (n - 1) :=
  rfl

theorem kindWeight_queryBind_cls (i : spec.Port) (hi : cls i = true) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls w (QuantumComp.queryBind i E ℓ k) ρ n =
      ∑' r, kindWeight R I cls w (k r) ((R.queryStep i E ℓ).branch r ρ) n := by
  rw [kindWeight_queryBind]
  simp only [hi, ↓reduceIte]

theorem kindWeight_queryBind_zero (i : spec.Port) (hi : cls i = false) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    kindWeight R I cls w (QuantumComp.queryBind i E ℓ k) ρ 0 = w i (callInput ℓ R.D ρ) := by
  rw [kindWeight_queryBind]
  simp only [hi, Bool.false_eq_true, ↓reduceIte]

theorem kindWeight_queryBind_succ (i : spec.Port) (hi : cls i = false) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls w (QuantumComp.queryBind i E ℓ k) ρ (n + 1) =
      ∑' r, kindWeight R I cls w (k r) ((R.queryStep i E ℓ).branch r ρ) n := by
  rw [kindWeight_queryBind]
  simp only [hi, Bool.false_eq_true, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- On positive semidefinite inputs, the weights are monotone in `w`. -/
theorem kindWeight_mono {w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (h : ∀ i σ, σ.PosSemidef → w i σ ≤ w' i σ) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (n : ℕ) :
    kindWeight R I cls w x ρ n ≤ kindWeight R I cls w' x ρ n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [kindWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦ ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) n
  | queryBind _ i E ℓ k ih =>
    have hr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    cases hi : cls i
    · cases n with
      | zero =>
        rw [kindWeight_queryBind_zero R I cls i hi, kindWeight_queryBind_zero R I cls i hi]
        exact h i _ (posSemidef_callInput ℓ hρ)
      | succ n =>
        rw [kindWeight_queryBind_succ R I cls i hi, kindWeight_queryBind_succ R I cls i hi]
        exact ENNReal.tsum_le_tsum fun r ↦ ih r (hr r) n
    · rw [kindWeight_queryBind_cls R I cls i hi, kindWeight_queryBind_cls R I cls i hi]
      exact ENNReal.tsum_le_tsum fun r ↦ ih r (hr r) n

/-- The weights are homogeneous in `w`. -/
theorem kindWeight_const_mul (c : ℝ≥0∞) (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (n : ℕ) :
    kindWeight R I cls (fun i σ ↦ c * w i σ) x ρ n = c * kindWeight R I cls w x ρ n := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o k ih => simp only [kindWeight_primBind, ih, ENNReal.tsum_mul_left]
  | queryBind _ i E ℓ k ih =>
    cases hi : cls i
    · cases n with
      | zero => rw [kindWeight_queryBind_zero R I cls i hi, kindWeight_queryBind_zero R I cls i hi]
      | succ n =>
        rw [kindWeight_queryBind_succ R I cls i hi, kindWeight_queryBind_succ R I cls i hi]
        simp only [ih, ENNReal.tsum_mul_left]
    · rw [kindWeight_queryBind_cls R I cls i hi, kindWeight_queryBind_cls R I cls i hi]
      simp only [ih, ENNReal.tsum_mul_left]

/-- **The quantum calls summed.** The weights of the quantum calls, summed over their indices, are
the total weight of `w` restricted to the quantum ports. -/
theorem tsum_kindWeight (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    ∑' n, kindWeight R I cls w x ρ n =
      R.totalWeight I (fun i σ ↦ if cls i then 0 else w i σ) x ρ := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [kindWeight_primBind, totalWeight_primBind, ← ih]
    exact ENNReal.tsum_comm
  | queryBind _ i E ℓ k ih =>
    rw [totalWeight_queryBind]
    simp only [← ih]
    cases hi : cls i
    · rw [tsum_eq_zero_add' ENNReal.summable, kindWeight_queryBind_zero R I cls i hi]
      simp only [kindWeight_queryBind_succ R I cls i hi, Bool.false_eq_true, ↓reduceIte]
      rw [ENNReal.tsum_comm]
    · simp only [kindWeight_queryBind_cls R I cls i hi, ↓reduceIte, zero_add]
      exact ENNReal.tsum_comm

/-- With at most `q` quantum calls on every path, the weights of the later quantum calls vanish. -/
theorem kindWeight_eq_zero_of_isChargeBound (x : QuantumComp L spec X A) {q : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge fun i ↦ if cls i then 0 else 1) q)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) {n : ℕ} (hn : q ≤ n) :
    kindWeight R I cls w x ρ n = 0 := by
  induction x using QuantumComp.inductionOn generalizing q n with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [Sponge.isChargeBound_portCharge_primBind_iff] at hx
    rw [kindWeight_primBind]
    exact ENNReal.tsum_eq_zero.2 fun b ↦ ih b (hx b) _ hn
  | queryBind _ i E ℓ k ih =>
    rw [Sponge.isChargeBound_portCharge_queryBind_iff] at hx
    cases hi : cls i
    · simp only [hi, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [kindWeight_queryBind_succ R I cls i hi]
      exact ENNReal.tsum_eq_zero.2 fun r ↦ ih r (hx.2 r) _ (by omega)
    · simp only [hi, ↓reduceIte, Nat.sub_zero] at hx
      rw [kindWeight_queryBind_cls R I cls i hi]
      exact ENNReal.tsum_eq_zero.2 fun r ↦ ih r (hx.2 r) _ hn

/-- A weight bounded by the trace is bounded, at every quantum call, by the initial trace. -/
theorem kindWeight_le_ofReal_trace
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ ENNReal.ofReal σ.trace.re) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (n : ℕ) :
    kindWeight R I cls w x ρ n ≤ ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o k ih =>
    rw [kindWeight_primBind]
    exact (ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) n).trans
      ((((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ)
  | queryBind _ i E ℓ k ih =>
    have hr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have htr := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    cases hi : cls i
    · cases n with
      | zero =>
        rw [kindWeight_queryBind_zero R I cls i hi]
        simpa using hw i _ (posSemidef_callInput ℓ hρ)
      | succ n =>
        rw [kindWeight_queryBind_succ R I cls i hi]
        exact (ENNReal.tsum_le_tsum fun r ↦ ih r (hr r) n).trans htr
    · rw [kindWeight_queryBind_cls R I cls i hi]
      exact (ENNReal.tsum_le_tsum fun r ↦ ih r (hr r) n).trans htr

end kind

/-! ## Scalar and matrix helpers -/

section helpers

/-- The weight `tr (K Γ Kᴴ)` of an operator through `K`. -/
noncomputable def leafW {Y Y' : Type*} [Fintype Y] [Fintype Y'] (K : Matrix Y' Y ℂ)
    (Γ : Matrix Y Y ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (MatrixMap.conj K Γ).trace.re

theorem leafW_conj {Y Y' Y'' : Type*} [Fintype Y] [Fintype Y'] [Fintype Y'']
    (K : Matrix Y'' Y' ℂ) (V : Matrix Y' Y ℂ) (Γ : Matrix Y Y ℂ) :
    leafW K (MatrixMap.conj V Γ) = leafW (K * V) Γ := by
  rw [leafW, leafW, MatrixMap.conj_mul, LinearMap.comp_apply]

theorem leafW_tsum {Y Y' ι : Type*} [Fintype Y] [Fintype Y'] (K : Matrix Y' Y ℂ)
    {f : ι → Matrix Y Y ℂ} (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    leafW K (∑' b, f b) = ∑' b, leafW K (f b) := by
  rw [leafW, MatrixMap.map_tsum _ hf]
  exact ofReal_trace_re_tsum (MatrixMap.summable_comp _ hf)
    fun b ↦ (hpos b).mul_mul_conjTranspose_same _

theorem leafW_le {Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] {K : Matrix Y' Y ℂ}
    (hK : (1 - Kᴴ * K).PosSemidef) {Γ : Matrix Y Y ℂ} (hΓ : Γ.PosSemidef) :
    leafW K Γ ≤ ENNReal.ofReal Γ.trace.re :=
  ENNReal.ofReal_le_ofReal (MatrixMap.isTNI_conj hK Γ hΓ)

/-- A distance followed by a sequence. -/
def seqD (d : ℝ≥0∞) (e : ℕ → ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => d
  | n + 1 => e n

@[simp]
theorem seqD_zero (d : ℝ≥0∞) (e : ℕ → ℝ≥0∞) : seqD d e 0 = d :=
  rfl

@[simp]
theorem seqD_succ (d : ℝ≥0∞) (e : ℕ → ℝ≥0∞) (n : ℕ) : seqD d e (n + 1) = e n :=
  rfl

theorem tsum_seqD (d : ℝ≥0∞) (e : ℕ → ℝ≥0∞) :
    ∑' j, seqD d e j ^ (2⁻¹ : ℝ) = d ^ (2⁻¹ : ℝ) + ∑' n, e n ^ (2⁻¹ : ℝ) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  rfl

/-- A nonzero entry of a triple product has nonzero factors. -/
theorem exists_ne_zero_of_mul_mul_ne_zero {a b c d : Type*} [Fintype b] [Fintype c]
    {P : Matrix a b ℂ} {K : Matrix b c ℂ} {Q : Matrix c d ℂ} {x : a} {z : d}
    (h : (P * K * Q) x z ≠ 0) : ∃ y y', P x y ≠ 0 ∧ K y y' ≠ 0 ∧ Q y' z ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨y', -, hy'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hy'
  rw [Matrix.mul_apply] at h1
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨y, y', left_ne_zero_of_mul hy, right_ne_zero_of_mul hy, right_ne_zero_of_mul hy'⟩

variable {D : Type*} [Fintype D] [DecidableEq D] {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [Fintype D] [Fintype Y] in
theorem sel_ne_zero {b : Bool} {y y' : Y} {d d' : D} {b' : Bool}
    (h : Quantum.Hybrid.sel Y b (y, d) (y', (d', b')) ≠ 0) : y' = y ∧ d' = d ∧ b' = b := by
  simp only [Quantum.Hybrid.sel, kroneckerMap_apply, conjTranspose_apply, Quantum.Hybrid.inj,
    of_apply] at h
  by_cases hy : y = y'
  · by_cases hd : (d', b') = (d, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
      exact ⟨hy.symm, rfl, rfl⟩
    · simp [hd] at h
  · simp [Matrix.one_apply_ne hy] at h

omit [Fintype D] [Fintype Y] in
theorem conjTranspose_sel_ne_zero {b : Bool} {y y' : Y} {d d' : D} {b' : Bool}
    (h : (Quantum.Hybrid.sel Y b)ᴴ (y', (d', b')) (y, d) ≠ 0) : y' = y ∧ d' = d ∧ b' = b := by
  rw [conjTranspose_apply, star_ne_zero] at h
  exact sel_ne_zero h

theorem ctrl_ne_zero {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    {K₀ K₁ : Matrix (O × D) (J × D) ℂ} {o : O} {j : J} {d d' : D} {b b' : Bool}
    (h : Quantum.Hybrid.ctrl K₀ K₁ (o, (d', b')) (j, (d, b)) ≠ 0) :
    K₀ (o, d') (j, d) ≠ 0 ∨ K₁ (o, d') (j, d) ≠ 0 := by
  rw [Quantum.Hybrid.ctrl, Matrix.add_apply] at h
  have key : ∀ (c : Bool) (K : Matrix (O × D) (J × D) ℂ),
      ((Quantum.Hybrid.sel (D := D) O c)ᴴ * K * Quantum.Hybrid.sel J c :
        Matrix (O × (D × Bool)) (J × (D × Bool)) ℂ) (o, (d', b')) (j, (d, b)) ≠ 0 →
        K (o, d') (j, d) ≠ 0 := fun c K hc ↦ by
    obtain ⟨⟨y, e⟩, ⟨y', e'⟩, h1, h2, h3⟩ := exists_ne_zero_of_mul_mul_ne_zero hc
    obtain ⟨rfl, rfl, -⟩ := conjTranspose_sel_ne_zero h1
    obtain ⟨rfl, rfl, -⟩ := sel_ne_zero h3
    exact h2
  by_cases h0 : ((Quantum.Hybrid.sel (D := D) O false)ᴴ * K₀ * Quantum.Hybrid.sel J false :
      Matrix (O × (D × Bool)) (J × (D × Bool)) ℂ) (o, (d', b')) (j, (d, b)) = 0
  · rw [h0, zero_add] at h
    exact Or.inr (key true K₁ h)
  · exact Or.inl (key false K₀ h0)

end helpers

/-! ## The graded hybrid -/

section graded

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {D : QReg}
  {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  (σ₀ σ₁ : SubState D)
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
  (cls : spec.Port → Bool) {Λ : Type*} (κ : D → Λ) (F : ∀ i, spec.Result i → Λ → Λ)
  (S : spec.Port → Set Λ)

/-- **The classical mass**: at a port with `cls i = true`, the diagonal mass of the register states
whose label lies in `S i`; `0` at the other ports. -/
noncomputable def clsMass : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if cls i then diagMass {p : spec.In i × D | κ p.2 ∈ S i} σ else 0

/-- Support on one label passes to a branch of the controlled operator. -/
theorem querySupportedOn_conj_sel {B : QReg} (T : Set Λ) (b : Bool)
    {Γ : Matrix (B × (D × Bool)) (B × (D × Bool)) ℂ}
    (h : QuerySupportedOn (fun m : B × (D × Bool) ↦ κ m.2.1) T Γ) :
    QuerySupportedOn (fun m : B × D ↦ κ m.2) T (MatrixMap.conj (Quantum.Hybrid.sel B b) Γ) :=
  h.conj fun m' m hK hm ↦ by
    obtain ⟨y, d, b'⟩ := m
    obtain ⟨-, rfl, -⟩ := sel_ne_zero (D := D) (Y := B) (y := m'.1) (d := m'.2) hK
    exact hm

/-- Support on one label of the controlled operator of `ρ`. -/
theorem querySupportedOn_conj_add {B : QReg} (T : Set Λ) {ρ : Matrix (B × D) (B × D) ℂ}
    (h : QuerySupportedOn (fun m : B × D ↦ κ m.2) T ρ) :
    QuerySupportedOn (fun m : B × (D × Bool) ↦ κ m.2.1) T
      (MatrixMap.conj ((Quantum.Hybrid.sel B false)ᴴ + (Quantum.Hybrid.sel B true)ᴴ) ρ) :=
  h.conj fun m' m hK hm ↦ by
    obtain ⟨y', d', b'⟩ := m'
    rw [Matrix.add_apply] at hK
    by_cases h0 : (Quantum.Hybrid.sel B false)ᴴ (y', (d', b')) m = 0
    · rw [h0, zero_add] at hK
      obtain ⟨-, rfl, -⟩ := conjTranspose_sel_ne_zero (D := D) (y := m.1) (d := m.2) hK
      exact hm
    · obtain ⟨-, rfl, -⟩ := conjTranspose_sel_ne_zero (D := D) (y := m.1) (d := m.2) h0
      exact hm

/-- One call of a runtime moving support from `T` to `T'` at every step. -/
theorem querySupportedOn_queryStep {Λ' : Type*} (R : QuantumRuntime spec) (g : R.D → Λ')
    {T T' : Set Λ'} (i : spec.Port) (r : spec.Result i)
    (hR : ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) T σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) T' ((R.step i).branch r σ))
    {B : QReg} (E : QReg) (ℓ : B ≃ spec.In i × E) {ρ : Matrix (B × R.D) (B × R.D) ℂ}
    (h : QuerySupportedOn (fun m : B × R.D ↦ g m.2) T ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2) T'
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := T) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ g m.2)
    (q' := fun m : spec.Out i × R.D ↦ g m.2) (fun σ hσ ↦ hR σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

variable {cls κ F S}

/-- The diagonal mass of a set containing the support is the trace. -/
theorem diagMass_eq_of_querySupportedOn {B : Type} [Fintype B] [DecidableEq B] {g : B → Λ}
    {T : Set Λ} {σ : Matrix B B ℂ} (hσ : σ.PosSemidef) (h : QuerySupportedOn g T σ) :
    diagMass {p | g p ∈ T} σ = ENNReal.ofReal σ.trace.re := by
  rw [← ofReal_trace_setProj_mul _ hσ]
  congr 3
  ext a b
  rw [setProj, diagonal_mul]
  by_cases ha : g a ∈ T
  · simp [ha]
  · have h0 : σ a b = 0 := by
      by_contra hne
      exact ha (h a b hne).1
    simp [h0]

/-- At a classical call outside its difference set, the two runtimes agree on the input. -/
theorem krausWeight_eq_zero_of_not_mem
    (hS : ∀ i, cls i = true → ∀ r o d' j d, κ d ∉ S i →
      U i r (o, d') (j, d) = W i r (o, d') (j, d))
    (i : spec.Port) (hi : cls i = true) {l : Λ} (hl : l ∉ S i)
    {σ : Matrix (spec.In i × D) (spec.In i × D) ℂ}
    (h : QuerySupportedOn (fun m : spec.In i × D ↦ κ m.2) {l} σ) :
    krausWeight (fun i r ↦ U i r - W i r) i σ = 0 := by
  rw [krausWeight]
  refine ENNReal.tsum_eq_zero.2 fun r ↦ ?_
  have h0 : (U i r - W i r) * σ = 0 := by
    ext ⟨o, d'⟩ m'
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun ⟨j, d⟩ _ ↦ ?_
    by_cases hσ : σ (j, d) m' = 0
    · rw [hσ, mul_zero]
    · have hd : κ d = l := (h _ _ hσ).1
      rw [Matrix.sub_apply, hS i hi r o d' j d (hd ▸ hl), sub_self, zero_mul]
  rw [MatrixMap.conj_apply, h0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
    ENNReal.ofReal_zero]

theorem tsum_seqD_comm {K : Type*} (d : K → ℝ≥0∞) (e : K → ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' r, seqD (d r) (e r) j = seqD (∑' r, d r) (fun n ↦ ∑' r, e r n) j := by
  cases j <;> rfl

theorem tsum_seqD_le_of_le {d d' : ℝ≥0∞} {e e' : ℕ → ℝ≥0∞} (hd : d' ^ (2⁻¹ : ℝ) ≤ d ^ (2⁻¹ : ℝ))
    (he : ∀ n, e' n ≤ e n) :
    ∑' j, seqD d' e' j ^ (2⁻¹ : ℝ) ≤ ∑' j, seqD d e j ^ (2⁻¹ : ℝ) := by
  rw [tsum_seqD, tsum_seqD]
  gcongr with n
  exact he n

theorem tsum_seqD_le_of_le_add {d d' k : ℝ≥0∞} {e e' : ℕ → ℝ≥0∞}
    (hd : d' ^ (2⁻¹ : ℝ) ≤ d ^ (2⁻¹ : ℝ) + k ^ (2⁻¹ : ℝ)) (he0 : e 0 = k)
    (he : ∀ n, e' n = e (n + 1)) :
    ∑' j, seqD d' e' j ^ (2⁻¹ : ℝ) ≤ ∑' j, seqD d e j ^ (2⁻¹ : ℝ) := by
  rw [tsum_seqD, tsum_seqD, tsum_eq_zero_add' (f := fun n ↦ e n ^ (2⁻¹ : ℝ)) ENNReal.summable,
    he0]
  simp only [he]
  calc d' ^ (2⁻¹ : ℝ) + ∑' n, e (n + 1) ^ (2⁻¹ : ℝ)
      ≤ d ^ (2⁻¹ : ℝ) + k ^ (2⁻¹ : ℝ) + ∑' n, e (n + 1) ^ (2⁻¹ : ℝ) := by gcongr
    _ = _ := add_assoc _ _ _

/-- The zero substate, the initial state of runtimes that are only run from given operators. -/
noncomputable def zeroSt (B : QReg) : SubState B :=
  ⟨0, Matrix.PosSemidef.zero, by simp⟩

/-- The leaves of the branch `true` weigh at most the trace of the branch `true`. -/
theorem tsum_leafW_ctrl_true_le (σ : SubState (QReg.of (D × Bool)))
    {Zt : (Σ u, X u) → Type*} [∀ p, Fintype (Zt p)] (O : ∀ p : Σ u, X u, Matrix (Zt p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {A : QReg} (x : QuantumComp L spec X A)
    {Γ : Matrix (A × (D × Bool)) (A × (D × Bool)) ℂ} (hΓ : Γ.PosSemidef) :
    ∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 true)
        (((ctrlRuntime σ hU hW).run I x).branch p Γ)) ≤
      ENNReal.ofReal (MatrixMap.conj (Quantum.Hybrid.sel A true) Γ).trace.re := by
  have hsim : ∀ p, MatrixMap.conj (Quantum.Hybrid.sel p.1 true)
      (((ctrlRuntime σ hU hW).run I x).branch p Γ) =
        ((QuantumRuntime.mk D (zeroSt D) s₁).run I x).branch p
          (MatrixMap.conj (Quantum.Hybrid.sel A true) Γ) := fun p ↦ by
    have h := LinearMap.congr_fun (QuantumRuntime.simulation I (R₁ := ctrlRuntime σ hU hW)
      (R₂ := QuantumRuntime.mk D (zeroSt D) s₁) (V := MatrixMap.conj (Quantum.Hybrid.inj D true)ᴴ)
      (ctrlRuntime_simulation_true σ (zeroSt D) hU hW) x p) Γ
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    rw [Quantum.Hybrid.conj_sel, Quantum.Hybrid.conj_sel]
    exact h.symm
  have hρ : (MatrixMap.conj (Quantum.Hybrid.sel A true) Γ).PosSemidef :=
    hΓ.mul_mul_conjTranspose_same _
  calc _ ≤ ∑' p, ENNReal.ofReal (((QuantumRuntime.mk D (zeroSt D) s₁).run I x).branch p
        (MatrixMap.conj (Quantum.Hybrid.sel A true) Γ)).trace.re :=
        ENNReal.tsum_le_tsum fun p ↦ by
          rw [hsim p]
          exact leafW_le (hO p)
            (((QuantumRuntime.mk D (zeroSt D) s₁).run I x).posSemidef_branch_apply p hρ)
    _ ≤ _ := ((QuantumRuntime.mk D (zeroSt D) s₁).run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hρ

/-- **The graded hybrid, by induction on the program.** Along the run of the controlled runtime
from `Γ`, supported on one label `l`, the square root of the leaf weights of the branch `true`
(the second runtime) is at most the square root of those of the branch `false` (the first runtime)
plus the classical masses of the run of the first runtime, plus the square roots of the distance
of the branches and of the Kraus weights of the quantum calls, indexed by their count. -/
theorem rpow_inv_two_tsum_leafW_run_le_graded
    (hFU : ∀ i r o d' j d, U i r (o, d') (j, d) ≠ 0 → κ d' = F i r (κ d))
    (hFW : ∀ i r o d' j d, W i r (o, d') (j, d) ≠ 0 → κ d' = F i r (κ d))
    (hS : ∀ i, cls i = true → ∀ r o d' j d, κ d ∉ S i →
      U i r (o, d') (j, d) = W i r (o, d') (j, d))
    (σ : SubState (QReg.of (D × Bool))) {Zt : (Σ u, X u) → Type*} [∀ p, Fintype (Zt p)]
    (O : ∀ p : Σ u, X u, Matrix (Zt p) (p.1 × D) ℂ) (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef)
    {A : QReg} (x : QuantumComp L spec X A) {Γ : Matrix (A × (D × Bool)) (A × (D × Bool)) ℂ}
    (hΓ : Γ.PosSemidef) (l : Λ)
    (hl : QuerySupportedOn (fun m : A × (D × Bool) ↦ κ m.2.1) {l} Γ) :
    (∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 true)
        (((ctrlRuntime σ hU hW).run I x).branch p Γ))) ^ (2⁻¹ : ℝ) ≤
      (∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 false)
          (((ctrlRuntime σ hU hW).run I x).branch p Γ)) +
        (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S) x
          (MatrixMap.conj (Quantum.Hybrid.sel A false) Γ)) ^ (2⁻¹ : ℝ) +
      ∑' j, seqD (Quantum.Hybrid.branchDist Γ)
        (kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls (krausWeight fun i r ↦ U i r - W i r) x
          (MatrixMap.conj (Quantum.Hybrid.sel A false) Γ)) j ^ (2⁻¹ : ℝ) := by
  induction x using QuantumComp.inductionOn generalizing l with
  | pure B y =>
    rw [run_pure]
    rw [tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, map_zero]
        simp [leafW],
      tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, map_zero]
        simp [leafW],
      DSubInstrument.branch_ret_self, LinearMap.id_apply, totalWeight_pure, add_zero]
    refine (Quantum.Hybrid.ofReal_trace_conj_sel_true_rpow_le (O ⟨_, y⟩) (hO _) hΓ).trans
      (add_le_add le_rfl ?_)
    exact ENNReal.le_tsum (f := fun j ↦ seqD _ _ j ^ (2⁻¹ : ℝ)) 0
  | primBind B o k ih =>
    have hΓb := fun b ↦ ((I o).frame (ctrlRuntime σ hU hW).D).posSemidef_branch_apply b hΓ
    have hlb : ∀ b, QuerySupportedOn (fun m : L.next o b × (D × Bool) ↦ κ m.2.1) {l}
        (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ) :=
      fun b ↦ hl.amplify_snd (q := fun d : D × Bool ↦ κ d.1) _
    have hL : ∀ c : Bool, ∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 c)
        (((ctrlRuntime σ hU hW).run I (QuantumComp.primBind o k)).branch p Γ)) =
          ∑' b, ∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 c)
            (((ctrlRuntime σ hU hW).run I (k b)).branch p
              (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ))) := fun c ↦ by
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun p ↦ ?_
      rw [run_primBind, DSubInstrument.branch_bind_apply, leafW_conj]
      simp only [leafW_conj]
      exact leafW_tsum _ ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ ((ctrlRuntime σ hU hW).run I (k b)).isCPTNIFamily) p).summable_apply Γ)
        fun b ↦ ((ctrlRuntime σ hU hW).run I (k b)).posSemidef_branch_apply p (hΓb b)
    have hsb : ∀ b, MatrixMap.conj (Quantum.Hybrid.sel (L.next o b) false)
        (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ) =
          ((I o).frame D).branch b (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) :=
      fun b ↦ Quantum.Hybrid.conj_sel_amplify ((I o).branch b) false Γ
    have hT : (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S)
        (QuantumComp.primBind o k) (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) =
          ∑' b, (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S) (k b)
            (MatrixMap.conj (Quantum.Hybrid.sel (L.next o b) false)
              (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ)) := by
      rw [totalWeight_primBind]
      exact tsum_congr fun b ↦ by rw [hsb b]
    have hK : ∀ n, kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls
        (krausWeight fun i r ↦ U i r - W i r) (QuantumComp.primBind o k)
          (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) n =
        ∑' b, kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls
          (krausWeight fun i r ↦ U i r - W i r) (k b)
            (MatrixMap.conj (Quantum.Hybrid.sel (L.next o b) false)
              (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ)) n := fun n ↦ by
      rw [kindWeight_primBind]
      exact tsum_congr fun b ↦ by rw [hsb b]
    rw [hL true, hL false, hT]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun b ↦ ih b (hΓb b) l (hlb b)).trans ?_
    rw [ENNReal.tsum_add]
    refine add_le_add le_rfl ?_
    simp only [tsum_seqD_comm]
    refine tsum_seqD_le_of_le (ENNReal.rpow_le_rpow ?_ (by norm_num)) fun n ↦ (hK n).ge
    calc ∑' b, Quantum.Hybrid.branchDist (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ)
        = ∑' b, ENNReal.ofReal (((I o).frame D).branch b
            (MatrixMap.conj (Quantum.Hybrid.seld B) Γ)).trace.re :=
          tsum_congr fun b ↦ Quantum.Hybrid.branchDist_amplify ((I o).branch b) Γ
      _ ≤ Quantum.Hybrid.branchDist Γ :=
          ((I o).frame D).isCPTNIFamily.tsum_ofReal_trace_re_le
            (hΓ.mul_mul_conjTranspose_same _)
  | queryBind B i E ℓ k ih =>
    have hΓr := fun r ↦ ((ctrlRuntime σ hU hW).queryStep i E ℓ).posSemidef_branch_apply r hΓ
    have hlr : ∀ r, QuerySupportedOn (fun m : (spec.Out i × E) × (D × Bool) ↦ κ m.2.1)
        {F i r l} (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ) := fun r ↦
      querySupportedOn_queryStep (ctrlRuntime σ hU hW) (fun d : D × Bool ↦ κ d.1) i r
        (fun σ' hσ' ↦ by
          change QuerySupportedOn _ _ (MatrixMap.conj (Quantum.Hybrid.ctrl (U i r) (W i r)) σ')
          refine hσ'.conj fun m' m hK hm ↦ ?_
          obtain ⟨o, d', b'⟩ := m'
          obtain ⟨j, d, b⟩ := m
          have hm' : κ d = l := hm
          refine Set.mem_singleton_iff.2 ?_
          rcases ctrl_ne_zero hK with h | h
          · exact (hFU i r o d' j d h).trans (congrArg (F i r) hm')
          · exact (hFW i r o d' j d h).trans (congrArg (F i r) hm')) E ℓ hl
    have hL : ∀ c : Bool, ∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 c)
        (((ctrlRuntime σ hU hW).run I (QuantumComp.queryBind i E ℓ k)).branch p Γ)) =
          ∑' r, ∑' p, leafW (O p) (MatrixMap.conj (Quantum.Hybrid.sel p.1 c)
            (((ctrlRuntime σ hU hW).run I (k r)).branch p
              (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ))) := fun c ↦ by
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun p ↦ ?_
      rw [run_queryBind, DSubInstrument.branch_bind_apply, leafW_conj]
      simp only [leafW_conj]
      exact leafW_tsum _ ((((ctrlRuntime σ hU hW).queryStep i E ℓ).isCPTNIFamily.comp_eval
        (fun r ↦ ((ctrlRuntime σ hU hW).run I (k r)).isCPTNIFamily) p).summable_apply Γ)
        fun r ↦ ((ctrlRuntime σ hU hW).run I (k r)).posSemidef_branch_apply p (hΓr r)
    have hsel : ∀ r, MatrixMap.conj (Quantum.Hybrid.sel (QReg.of (spec.Out i × E)) false)
        (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ) =
          ((QuantumRuntime.mk D σ₀ s₀).queryStep i E ℓ).branch r
            (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) := fun r ↦ by
      have h := LinearMap.congr_fun (QuantumRuntime.intertwines_queryStep
        (R₁ := ctrlRuntime σ hU hW) (R₂ := QuantumRuntime.mk D σ₀ s₀)
        (V := MatrixMap.conj (Quantum.Hybrid.inj D false)ᴴ)
        (ctrlRuntime_simulation_false σ σ₀ hU hW i) E ℓ r) Γ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [Quantum.Hybrid.conj_sel, Quantum.Hybrid.conj_sel]
      exact h.symm
    have hσf : QuerySupportedOn (fun m : spec.In i × D ↦ κ m.2) {l}
        (callInput ℓ D (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ)) :=
      (querySupportedOn_conj_sel κ {l} false hl).callInput ℓ
    have hT : (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S)
        (QuantumComp.queryBind i E ℓ k) (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) =
          clsMass cls κ S i (callInput ℓ D (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ)) +
          ∑' r, (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S) (k r)
            (MatrixMap.conj (Quantum.Hybrid.sel (QReg.of (spec.Out i × E)) false)
              (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ)) := by
      rw [totalWeight_queryBind]
      exact congrArg _ (tsum_congr fun r ↦ by rw [hsel r])
    have hKr : ∀ n, ∑' r, kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls
        (krausWeight fun i r ↦ U i r - W i r) (k r)
          (((QuantumRuntime.mk D σ₀ s₀).queryStep i E ℓ).branch r
            (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ)) n =
        ∑' r, kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls
          (krausWeight fun i r ↦ U i r - W i r) (k r)
            (MatrixMap.conj (Quantum.Hybrid.sel (QReg.of (spec.Out i × E)) false)
              (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ)) n := fun n ↦
      tsum_congr fun r ↦ by rw [hsel r]
    have hdist := Quantum.QuantumRuntime.tsum_dist_queryStep_le σ hU hW i E ℓ hΓ
    cases hi : cls i
    · -- A quantum call.
      have hc0 : clsMass cls κ S i
          (callInput ℓ D (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ)) = 0 := by
        simp [clsMass, hi]
      rw [hL true, hL false, hT, hc0, zero_add]
      refine (rpow_inv_two_tsum_le_of_le_add_tsum fun r ↦ ih r (hΓr r) (F i r l) (hlr r)).trans ?_
      rw [ENNReal.tsum_add]
      refine add_le_add le_rfl ?_
      simp only [tsum_seqD_comm]
      refine tsum_seqD_le_of_le_add hdist
        (kindWeight_queryBind_zero _ I cls i hi E ℓ k _) fun n ↦ ?_
      rw [kindWeight_queryBind_succ _ I cls i hi E ℓ k, hKr n]
    · by_cases hlS : l ∈ S i
      · -- A classical call in its difference set: bounded by its mass.
        have hpos : (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ).PosSemidef :=
          hΓ.mul_mul_conjTranspose_same _
        have hmass : ENNReal.ofReal (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ).trace.re ≤
            (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S)
              (QuantumComp.queryBind i E ℓ k) (MatrixMap.conj (Quantum.Hybrid.sel B false) Γ) := by
          rw [hT]
          refine le_trans (le_of_eq ?_) le_self_add
          simp only [clsMass, hi, ↓reduceIte]
          rw [diagMass_eq_of_querySupportedOn (posSemidef_callInput ℓ hpos)
            (hσf.mono (Set.singleton_subset_iff.2 hlS)), trace_callInput]
        have hone : (1 - (1 : Matrix (B × D) (B × D) ℂ)ᴴ * 1).PosSemidef := by
          simpa using Matrix.PosSemidef.zero
        have htf := Quantum.Hybrid.ofReal_trace_conj_sel_true_rpow_le
          (1 : Matrix (B × D) (B × D) ℂ) hone hΓ
        simp only [MatrixMap.conj_one, LinearMap.id_apply] at htf
        calc _ ≤ ENNReal.ofReal (MatrixMap.conj (Quantum.Hybrid.sel B true) Γ).trace.re ^
              (2⁻¹ : ℝ) :=
            ENNReal.rpow_le_rpow (tsum_leafW_ctrl_true_le I hU hW σ O hO _ hΓ) (by norm_num)
          _ ≤ _ := htf.trans (add_le_add (ENNReal.rpow_le_rpow (hmass.trans le_add_self)
              (by norm_num)) (ENNReal.le_tsum (f := fun j ↦ seqD _ _ j ^ (2⁻¹ : ℝ)) 0))
      · -- A classical call outside its difference set: the two runtimes agree.
        have hkw := krausWeight_eq_zero_of_not_mem hS i hi hlS hσf
        rw [hkw, ENNReal.zero_rpow_of_pos (by norm_num), add_zero] at hdist
        rw [hL true, hL false]
        refine (rpow_inv_two_tsum_le_of_le_add_tsum fun r ↦ ih r (hΓr r) (F i r l) (hlr r)).trans ?_
        refine add_le_add (ENNReal.rpow_le_rpow ?_ (by norm_num)) ?_
        · rw [ENNReal.tsum_add, hT]
          gcongr
          exact le_add_self
        · simp only [tsum_seqD_comm]
          refine tsum_seqD_le_of_le hdist fun n ↦ le_of_eq ?_
          rw [kindWeight_queryBind_cls _ I cls i hi E ℓ k, hKr n]

include hU hW in
/-- **The graded square-root hybrid.** Two runtimes on one register `D` and initial state `σ₀`, with
Kraus operators `U` (the first, against which the masses are computed) and `W`, run a program to
laws whose square roots differ by at most
* the square roots of the Kraus weights of `U - W` at the quantum calls (`cls i = false`), indexed
  by their count `n` (the `n`-th quantum call, whatever its index among all calls), and
* the square root of the classical mass summed over all calls: at a classical call (`cls i = true`)
  the mass of the register states whose label `κ` lies in `S i`, outside which `U` and `W` agree.

The labels must be classical: every Kraus operator of both runtimes moves the label of a basis state
along the same map `F i r`, and the initial state carries one label `l₀`. -/
theorem rpow_inv_two_outcomeLawWith_le_graded {γ : Type*} [MeasurableSpace γ]
    (hFU : ∀ i r o d' j d, U i r (o, d') (j, d) ≠ 0 → κ d' = F i r (κ d))
    (hFW : ∀ i r o d' j d, W i r (o, d') (j, d) ≠ 0 → κ d' = F i r (κ d))
    (hS : ∀ i, cls i = true → ∀ r o d' j d, κ d ∉ S i →
      U i r (o, d') (j, d) = W i r (o, d') (j, d))
    (l₀ : Λ) (hσ₀ : QuerySupportedOn κ {l₀} σ₀.matrix) {A : QReg}
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' n, kindWeight (QuantumRuntime.mk D σ₀ s₀) I cls (krausWeight fun i r ↦ U i r - W i r)
          x (ρ.matrix ⊗ₖ σ₀.matrix) n ^ (2⁻¹ : ℝ) +
        (QuantumRuntime.mk D σ₀ s₀).totalWeight I (clsMass cls κ S) x
          (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) := by
  classical
  have hρ : QuerySupportedOn (fun m : A × D ↦ κ m.2) {l₀} (ρ.matrix ⊗ₖ σ₀.matrix) :=
    fun m m' hm ↦ hσ₀ m.2 m'.2 (right_ne_zero_of_mul (by rwa [kroneckerMap_apply] at hm))
  have hΓ : (MatrixMap.conj ((Quantum.Hybrid.sel (D := D) A false)ᴴ +
      (Quantum.Hybrid.sel A true)ᴴ) (ρ.matrix ⊗ₖ σ₀.matrix)).PosSemidef :=
    (ρ.prod σ₀).posSemidef.mul_mul_conjTranspose_same _
  have h := rpow_inv_two_tsum_leafW_run_le_graded I σ₀ hU hW hFU hFW hS (zeroSt _)
    (fun p ↦ if f p ∈ s then (1 : Matrix (p.1 × D) (p.1 × D) ℂ) else 0)
    (fun p ↦ by by_cases hp : f p ∈ s <;> simp [hp, Matrix.PosSemidef.one, Matrix.PosSemidef.zero])
    x hΓ l₀ (querySupportedOn_conj_add κ {l₀} hρ)
  have he : ∀ p, ((QuantumRuntime.mk D σ₀ s₀).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix) =
      MatrixMap.conj (Quantum.Hybrid.sel p.1 false)
        (((ctrlRuntime (zeroSt _) hU hW).run I x).branch p (MatrixMap.conj
          ((Quantum.Hybrid.sel A false)ᴴ + (Quantum.Hybrid.sel A true)ᴴ)
            (ρ.matrix ⊗ₖ σ₀.matrix))) ∧
      ((QuantumRuntime.mk D σ₀ s₁).run I x).branch p (ρ.matrix ⊗ₖ σ₀.matrix) =
      MatrixMap.conj (Quantum.Hybrid.sel p.1 true)
        (((ctrlRuntime (zeroSt _) hU hW).run I x).branch p (MatrixMap.conj
          ((Quantum.Hybrid.sel A false)ᴴ + (Quantum.Hybrid.sel A true)ᴴ)
            (ρ.matrix ⊗ₖ σ₀.matrix))) := fun p ↦ by
    have h₀ := LinearMap.congr_fun
      (QuantumRuntime.simulation I (R₁ := ctrlRuntime (zeroSt _) hU hW)
        (R₂ := QuantumRuntime.mk D σ₀ s₀) (V := MatrixMap.conj (Quantum.Hybrid.inj D false)ᴴ)
        (ctrlRuntime_simulation_false (zeroSt _) σ₀ hU hW) x p)
      (MatrixMap.conj ((Quantum.Hybrid.sel A false)ᴴ + (Quantum.Hybrid.sel A true)ᴴ)
        (ρ.matrix ⊗ₖ σ₀.matrix))
    have h₁ := LinearMap.congr_fun
      (QuantumRuntime.simulation I (R₁ := ctrlRuntime (zeroSt _) hU hW)
        (R₂ := QuantumRuntime.mk D σ₀ s₁) (V := MatrixMap.conj (Quantum.Hybrid.inj D true)ᴴ)
        (ctrlRuntime_simulation_true (zeroSt _) σ₀ hU hW) x p)
      (MatrixMap.conj ((Quantum.Hybrid.sel A false)ᴴ + (Quantum.Hybrid.sel A true)ᴴ)
        (ρ.matrix ⊗ₖ σ₀.matrix))
    simp only [LinearMap.comp_apply, ← Quantum.Hybrid.conj_sel,
      Quantum.Hybrid.conj_sel_conj_add] at h₀ h₁
    exact ⟨h₀, h₁⟩
  simp only [← fun p ↦ (he p).1, ← fun p ↦ (he p).2, Quantum.Hybrid.conj_sel_conj_add,
    Quantum.Hybrid.branchDist, Quantum.Hybrid.conj_seld_conj_add, Matrix.trace_zero,
    Complex.zero_re, ENNReal.ofReal_zero, tsum_seqD,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), zero_add] at h
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs, QuantumRuntime.evalDistMap_apply _ _ _ _ _ hs]
  have hind : ∀ p (M : Matrix (p.1 × D) (p.1 × D) ℂ), ENNReal.ofReal M.trace.re *
      s.indicator 1 (f p) = leafW (if f p ∈ s then (1 : Matrix (p.1 × D) (p.1 × D) ℂ) else 0)
        M := fun p M ↦ by
    by_cases hp : f p ∈ s <;> simp [hp, leafW]
  simp only [QuantumRuntime.matrix_jointPost, hind]
  refine h.trans ?_
  rw [add_right_comm]
  exact add_le_add (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)) le_rfl

end graded

/-! ## Programs with a budget of quantum calls -/

section budget

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {A : QReg} (cls : spec.Port → Bool)
  {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- With at most `q` quantum calls on every path, the sum over the quantum calls stops at `q`. -/
theorem tsum_rpow_kindWeight_eq_sum (x : QuantumComp L spec X A) {q : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge fun i ↦ if cls i then 0 else 1) q)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (c : ℝ≥0∞) :
    ∑' n, (c * kindWeight R I cls w x ρ n) ^ (2⁻¹ : ℝ) =
      ∑ n ∈ Finset.range q, (c * kindWeight R I cls w x ρ n) ^ (2⁻¹ : ℝ) :=
  tsum_eq_sum fun n hn ↦ by
    rw [kindWeight_eq_zero_of_isChargeBound R I cls x hx ρ (by simpa using hn), mul_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- **Cauchy-Schwarz over the quantum calls.** With at most `q` quantum calls on every path, the
sum of the square roots of their weights is at most the square root of `q` times the total weight
of the quantum ports. -/
theorem tsum_rpow_kindWeight_le (x : QuantumComp L spec X A) {q : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge fun i ↦ if cls i then 0 else 1) q)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (c : ℝ≥0∞) :
    ∑' n, (c * kindWeight R I cls w x ρ n) ^ (2⁻¹ : ℝ) ≤
      ((q : ℝ≥0∞) * (c * R.totalWeight I (fun i σ ↦ if cls i then 0 else w i σ) x ρ)) ^
        (2⁻¹ : ℝ) := by
  rw [tsum_rpow_kindWeight_eq_sum R I cls x hx ρ c, ← tsum_kindWeight, ← ENNReal.tsum_mul_left,
    ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ n ∈ Finset.range q, (c * kindWeight R I cls w x ρ n) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.range q).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ n ∈ Finset.range q, ((c * kindWeight R I cls w x ρ n) ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = (q : ℝ≥0∞) * ∑ n ∈ Finset.range q, c * kindWeight R I cls w x ρ n := by
        simp only [Finset.card_range, rpow_inv_two_rpow_two]
        norm_num
    _ ≤ _ := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-- With at most `q` quantum calls on every path, the inputs of the quantum calls weigh at most `q`
times the initial trace. -/
theorem totalWeight_trace_le_of_isChargeBound (x : QuantumComp L spec X A) {q : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge fun i ↦ if cls i then 0 else 1) q)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i σ ↦ if cls i then 0 else ENNReal.ofReal σ.trace.re) x ρ ≤
      q * ENNReal.ofReal ρ.trace.re := by
  rw [← tsum_kindWeight (w := fun _ σ ↦ ENNReal.ofReal σ.trace.re),
    tsum_eq_sum (s := Finset.range q) fun n hn ↦
      kindWeight_eq_zero_of_isChargeBound R I cls x hx ρ (by simpa using hn)]
  calc ∑ n ∈ Finset.range q,
        kindWeight R I cls (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x ρ n
      ≤ ∑ _n ∈ Finset.range q, ENNReal.ofReal ρ.trace.re :=
        Finset.sum_le_sum fun n _ ↦ kindWeight_le_ofReal_trace R I cls (fun _ _ _ ↦ le_rfl) x hρ n
    _ = _ := by simp

/-- `totalWeight_trace_le_of_isChargeBound` for the calls of the ports `Q`. -/
theorem totalWeight_trace_le_of_isChargeBound' (Q : spec.Port → Prop) [DecidablePred Q]
    (x : QuantumComp L spec X A) {q : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge fun i ↦ if Q i then 1 else 0) q)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0) x ρ ≤
      q * ENNReal.ofReal ρ.trace.re := by
  have hc : (fun i ↦ if Q i then 1 else 0) =
      fun i ↦ if (fun i ↦ !decide (Q i)) i then 0 else 1 :=
    funext fun i ↦ by by_cases h : Q i <;> simp [h]
  have hw : (fun i (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ) ↦
      if Q i then ENNReal.ofReal σ.trace.re else 0) =
      fun i σ ↦ if (fun i ↦ !decide (Q i)) i then 0 else ENNReal.ofReal σ.trace.re :=
    funext fun i ↦ funext fun σ ↦ by by_cases h : Q i <;> simp [h]
  rw [hc] at hx
  rw [hw]
  exact totalWeight_trace_le_of_isChargeBound R I _ x hx hρ

end budget

/-! ## The view lemma relative to the calls of some ports -/

section view

variable {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)]
  {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **`sum_queryWeight_cut_le` relative to the calls of the ports `Q`**: when the sets `C v` are
empty at the other ports, the masses at the states labelled `T` are at most `κ` times the masses of
the states labelled `T` at the calls of the ports `Q` only. -/
theorem sum_queryWeight_cut_le_on [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j) (Q : spec.Port → Prop)
    [DecidablePred Q] (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D))
    (hCP : ∀ v i, ¬ P i → C v i = ∅) (hCQ : ∀ v i, ¬ Q i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) (T : Finset S) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I (fun i σ ↦ if Q i then
        diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j := by
  classical
  obtain ⟨v₀⟩ : Nonempty ((s : S) → D s) := inferInstance
  set N : ℝ≥0∞ := ∑ u, if Agree T v₀ u then 1 else 0 with hN
  have hNv : ∀ v, ∑ u, (if Agree T v u then (1 : ℝ≥0∞) else 0) = N :=
    fun v ↦ sum_agree_eq T v v₀
  have hN1 : 1 ≤ N := by
    have h := Finset.single_le_sum (f := fun u ↦ if Agree T v₀ u then (1 : ℝ≥0∞) else 0)
      (fun _ _ ↦ by simp) (Finset.mem_univ v₀)
    simp only [show Agree T v₀ v₀ from fun _ _ ↦ rfl, ↓reduceIte] at h
    exact h
  have hN0 : N ≠ 0 := (zero_lt_one.trans_le hN1).ne'
  have hNtop : N ≠ ⊤ := by
    rw [hN]
    exact ENNReal.sum_ne_top.mpr fun u _ ↦ by split_ifs <;> simp
  have hv : ∀ v, ∑ u, (if Agree T v u then
      R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) ≤
        κ * N * R.queryWeight I (fun i σ ↦ if Q i then
          diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j := by
    intro v
    have hstep : ∀ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j else 0) =
          R.queryWeight I (fun i σ ↦ if Agree T v u then
            diagMass (C u i ∩ {p | lab p.2 = T}) σ else 0) (x v) (ρ v) j := by
      intro u
      by_cases h : Agree T v u
      · simp only [h, ↓reduceIte]
        exact (hview T v u h (fun i ↦ C u i ∩ {p | lab p.2 = T}) (fun i p hp ↦ hp.2)
          fun i hi ↦ by rw [hCP u i hi, Set.empty_inter]).symm
      · simp only [h, ↓reduceIte]
        exact (queryWeight_zero_weight R I (x v) (ρ v) j).symm
    simp only [hstep]
    rw [← queryWeight_fintype_sum, ← R.queryWeight_const_mul]
    refine R.queryWeight_mono I (fun i σ _ ↦ ?_) (x v) (hρ v) j
    by_cases hQ : Q i
    · simp only [hQ, ↓reduceIte]
      have h := sum_agree_diagMass_le (fun p : spec.In i × R.D ↦ lab p.2) T v (fun u ↦ C u i)
        (srcs i) (F i) (hF i) (fun u p hp ↦ hsrc u i p hp) κ (fun p u ↦ hκ i p u) σ
      rwa [hNv v] at h
    · have h0 : ∀ u, C u i = ∅ := fun u ↦ hCQ u i hQ
      simp [hQ, h0, diagMass]
  have h1 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j = ∑ v, ∑ u, (if Agree T v u then
        R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u) (ρ u) j
          else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [← hNv u, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hs : Agree T u v ↔ Agree T v u := ⟨Agree.symm, Agree.symm⟩
    by_cases h : Agree T v u <;> simp [h, hs]
  have h2 : N * ∑ u, R.queryWeight I (fun i ↦ diagMass (C u i ∩ {p | lab p.2 = T})) (x u)
      (ρ u) j ≤ N * (κ * ∑ v, R.queryWeight I (fun i σ ↦ if Q i then
        diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j) := by
    rw [h1, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ ↦ (hv v).trans_eq (by ring)
  exact (ENNReal.mul_le_mul_iff_right hN0 hNtop).mp h2

/-- **The adaptive view lemma relative to the calls of the ports `Q`** (`sum_queryWeight_view_le`
with the masses `0` outside `Q`): the masses of `C v` at the `j`-th call add up, over the hidden
values, to at most `κ` times the traces of the inputs of the `j`-th call when it is a call of a
port of `Q`. Summed over the calls (`sum_totalWeight_le_of_forall`), the total masses are at most
`κ` times the number of calls of the ports `Q`, not of all calls. -/
theorem sum_queryWeight_view_le_on [∀ s, Nonempty (D s)] (lab : R.D → Finset S)
    (x : ((s : S) → D s) → QuantumComp L spec Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × R.D) (A × R.D) ℂ) (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (P : spec.Port → Prop) (hview : ViewByOn R I P lab x ρ j) (Q : spec.Port → Prop)
    [DecidablePred Q] (C : ((s : S) → D s) → ∀ i, Set (spec.In i × R.D))
    (hCP : ∀ v i, ¬ P i → C v i = ∅) (hCQ : ∀ v i, ¬ Q i → C v i = ∅)
    (srcs : ∀ i, spec.In i × R.D → Finset S)
    (F : ∀ i, spec.In i × R.D → (s : S) → ((s : S) → D s) → Finset (D s))
    (hF : ∀ i p s v d, F i p s (Function.update v s d) = F i p s v)
    (hsrc : ∀ v i p, p ∈ C v i → ∃ s ∈ srcs i p, s ∉ lab p.2 ∧ v s ∈ F i p s v)
    (κ : ℝ≥0∞)
    (hκ : ∀ i p v, ∑ s ∈ srcs i p,
      ((F i p s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0)
        (x v) (ρ v) j := by
  classical
  have hpart : ∀ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j =
      ∑ T, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v) (ρ v) j :=
    fun v ↦ by
      rw [← queryWeight_fintype_sum]
      refine congrArg (fun w ↦ R.queryWeight I w (x v) (ρ v) j) (funext fun i ↦ funext fun σ ↦ ?_)
      exact diagMass_eq_sum_label (fun p ↦ lab p.2) (C v i) σ
  have hT := fun T ↦ sum_queryWeight_cut_le_on R I lab x ρ hρ j P hview Q C hCP hCQ srcs F hF
    hsrc κ hκ T
  have htr : ∀ v, ∑ T, R.queryWeight I (fun i σ ↦ if Q i then
      diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j ≤
        R.queryWeight I (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0)
          (x v) (ρ v) j := fun v ↦ by
    rw [← queryWeight_fintype_sum]
    refine R.queryWeight_mono I (fun i σ hσ ↦ ?_) (x v) (hρ v) j
    by_cases hQ : Q i
    · simp only [hQ, ↓reduceIte]
      have h := diagMass_eq_sum_label (fun p : spec.In i × R.D ↦ lab p.2) Set.univ σ
      simp only [Set.univ_inter] at h
      rw [← h]
      exact diagMass_le _ hσ
    · simp [hQ]
  calc ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i)) (x v) (ρ v) j
      = ∑ T, ∑ v, R.queryWeight I (fun i ↦ diagMass (C v i ∩ {p | lab p.2 = T})) (x v)
          (ρ v) j := by
        simp only [hpart]
        exact Finset.sum_comm
    _ ≤ ∑ T, κ * ∑ v, R.queryWeight I (fun i σ ↦ if Q i then
          diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j :=
        Finset.sum_le_sum fun T _ ↦ hT T
    _ = κ * ∑ v, ∑ T, R.queryWeight I (fun i σ ↦ if Q i then
          diagMass {p : spec.In i × R.D | lab p.2 = T} σ else 0) (x v) (ρ v) j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
        gcongr with v
        exact htr v

/-- **Per-call bounds summed over the calls.** -/
theorem sum_totalWeight_le_of_forall {V : Type*} [Fintype V]
    (w : V → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (c : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : V → QuantumComp L spec Ω A) (ρ : V → Matrix (A × R.D) (A × R.D) ℂ) (κ : ℝ≥0∞)
    (h : ∀ j, ∑ v, R.queryWeight I (w v) (x v) (ρ v) j ≤
      κ * ∑ v, R.queryWeight I c (x v) (ρ v) j) :
    ∑ v, R.totalWeight I (w v) (x v) (ρ v) ≤ κ * ∑ v, R.totalWeight I c (x v) (ρ v) := by
  simp only [totalWeight]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable,
    ← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum h

end view

/-! ## Averages over the table -/

section avg

variable {Θ : Type*} [Fintype Θ]

/-- **The graded hybrid averaged over the table.** If, for every table `θ`,
`√P₁ θ ≤ √P₂ θ + ∑ₙ √(4 μₙ θ) + √(ν θ)`, then
`E P₁ ≤ (√(E P₂) + ∑ₙ √(4 E μₙ) + √(E ν))²` (`uavg_le_of_hybrid`). -/
theorem uavg_le_of_hybrid_graded (P₁ P₂ : Θ → ℝ≥0∞) (μ : Θ → ℕ → ℝ≥0∞) (ν : Θ → ℝ≥0∞)
    (h : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤
      P₂ θ ^ (2⁻¹ : ℝ) + ∑' n, (4 * μ θ n) ^ (2⁻¹ : ℝ) + ν θ ^ (2⁻¹ : ℝ)) :
    uavg P₁ ≤ (uavg P₂ ^ (2⁻¹ : ℝ) + ∑' n, (4 * uavg (fun θ ↦ μ θ n)) ^ (2⁻¹ : ℝ) +
      uavg ν ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h4 : ∀ y : ℝ≥0∞, 4 * (4⁻¹ * y) = y := fun y ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hs : ∀ (a : ℝ≥0∞) (e : ℕ → ℝ≥0∞), ∑' j, (4 * seqD (4⁻¹ * a) e j) ^ (2⁻¹ : ℝ) =
      a ^ (2⁻¹ : ℝ) + ∑' n, (4 * e n) ^ (2⁻¹ : ℝ) := fun a e ↦ by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [seqD_zero, seqD_succ, h4]
  have hu : ∀ j, uavg (fun θ ↦ seqD (4⁻¹ * ν θ) (μ θ) j) =
      seqD (4⁻¹ * uavg ν) (fun n ↦ uavg fun θ ↦ μ θ n) j := fun j ↦ by
    cases j <;> simp [uavg_const_mul]
  refine (uavg_le_of_hybrid P₁ P₂ (fun θ j ↦ seqD (4⁻¹ * ν θ) (μ θ) j) fun θ ↦ ?_).trans_eq ?_
  · simp only [hs]
    exact (h θ).trans_eq (by ring)
  · simp only [hu, hs]
    ring

end avg


/-! ## Runtime 1 against `runtimeR` -/

section runtimeR

open Quantum.Sponge Quantum.Xmss.Assembly

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A port of the hardwired runtime keeps the classical data. -/
theorem hwPort_ne_zero_snd
    {M : Type} [Fintype M] [DecidableEq M] {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (read : HwReg X Z M → A → Y) {a a' : A × Y}
    {s s' : HwReg X Z M} (h : hwPort read (a', s') (a, s) ≠ 0) : s'.2 = s.2 := by
  rw [hwPort_eq_liftBlocks] at h
  obtain ⟨D', b'⟩ := s'
  obtain ⟨D, b⟩ := s
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply] at h
  split_ifs at h with hb
  · exact hb
  · exact absurd rfl h

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

/-- The classical label of the hybrid: the hardwired cells of the register. -/
def hwLab (s : HwReg X Z (Finset S × M')) : Hw X Z :=
  s.2.1

/-- The label map: a program port hardwires its cell, every other port keeps the cells. -/
def hwLabMap : ∀ i : (recHwSpec X Z S M').Port, (recHwSpec X Z S M').Result i → Hw X Z → Hw X Z
  | .inl (.inr c), _ => progUpdate c
  | _, _ => id

/-- The difference sets of the classical ports: at a read port, the hardwired cells for which the
read cell is hidden and not hardwired; empty at the program and record ports. -/
def readHidSet (Hh : Set Z) (Hk Hk' : Set X) : (recHwSpec X Z S M').Port → Set (Hw X Z)
  | .inl (.inl (.inr (.readH z _))) => {W | z ∈ Hh ∧ W.1 z = none}
  | .inl (.inl (.inr (.readK x _))) => {W | x ∈ Hk ∧ W.2.1 x = none}
  | .inl (.inl (.inr (.readK' x _))) => {W | x ∈ Hk' ∧ W.2.2 x = none}
  | _ => ∅

/-- **The hidden mass at the ports satisfying `Q`**, `0` at the others. -/
noncomputable def portMass (Q : (recHwSpec X Z S M').Port → Prop) [DecidablePred Q]
    (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M')))
        ((recHwSpec X Z S M').In i × QReg.of (HwReg X Z (Finset S × M'))) ℂ → ℝ≥0∞ :=
  fun i σ ↦ if Q i then extWeight (hiddenMass Hh Hk Hk') i σ else 0

/-- **The hidden mass at the classical ports**: the hidden mass (`hiddenMass`) at the read ports,
`0` at the sponge, program and record ports. -/
noncomputable def readMass (Hh : Set Z) (Hk Hk' : Set X) :=
  portMass (S := S) (M' := M') (fun i ↦ extCls X Z (Finset S × M') (recSpec S M') i = true)
    Hh Hk Hk'

/-- **The hidden mass at the sponge ports**: the hidden mass at the sponge ports, `0` at the
classical ports. -/
noncomputable def spongeMass (Hh : Set Z) (Hk Hk' : Set X) :=
  portMass (S := S) (M' := M') (fun i ↦ extCls X Z (Finset S × M') (recSpec S M') i = false)
    Hh Hk Hk'

theorem spongeMass_eq (Hh : Set Z) (Hk Hk' : Set X) :
    spongeMass (S := S) (M' := M') Hh Hk Hk' = fun i σ ↦
      if extCls X Z (Finset S × M') (recSpec S M') i then 0 else
        extWeight (hiddenMass Hh Hk Hk') i σ := by
  funext i σ
  cases h : extCls X Z (Finset S × M') (recSpec S M') i <;> simp [spongeMass, portMass, h]

theorem clsMass_readHidSet (Hh : Set Z) (Hk Hk' : Set X) :
    clsMass (D := QReg.of (HwReg X Z (Finset S × M')))
      (extCls X Z (Finset S × M') (recSpec S M')) hwLab (readHidSet Hh Hk Hk') =
      readMass Hh Hk Hk' := by
  funext i σ
  rcases i with ((i | c) | c) | T
  · rfl
  · cases c <;> rfl
  · simp [clsMass, readMass, portMass, readHidSet, extCls, hwCls, extWeight, sumWeight,
      hiddenMass, diagMass]
  · simp [clsMass, readMass, portMass, readHidSet, extCls, extWeight, sumWeight, diagMass]

variable [AddCommGroup X] [AddCommGroup Z]

/-- The Kraus operators of `runtimeR` move the hardwired cells along `hwLabMap`. -/
theorem hwLab_sumKraus2 (m₀ : Finset S × M') (i : (recHwSpec X Z S M').Port)
    (r : (recHwSpec X Z S M').Result i) (o : (recHwSpec X Z S M').Out i)
    (d' : HwReg X Z (Finset S × M')) (j : (recHwSpec X Z S M').In i)
    (d : HwReg X Z (Finset S × M'))
    (h : sumKraus (kraus2 X Z m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m) i r (o, d') (j, d) ≠
      0) :
    hwLab d' = hwLabMap i r (hwLab d) := by
  rcases i with ((i | c) | c) | T
  · cases i <;> exact congrArg Prod.fst (hwPort_ne_zero_snd _ h)
  · cases c with
    | readH z upd =>
      simp only [sumKraus, kraus2, hwReadKraus, readKrausH] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
    | readK x upd =>
      simp only [sumKraus, kraus2, hwReadKraus, readKrausK] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
    | readK' x upd =>
      simp only [sumKraus, kraus2, hwReadKraus, readKrausK'] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
  · exact congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (s := d) (s' := d') h)
  · rw [hwLab, eq_of_recKraus_ne_zero h]
    rfl

/-- The Kraus operators of `runtime1R` move the hardwired cells along `hwLabMap`. -/
theorem hwLab_sumKraus1 (L : Hw X Z) (m₀ : Finset S × M') (i : (recHwSpec X Z S M').Port)
    (r : (recHwSpec X Z S M').Result i) (o : (recHwSpec X Z S M').Out i)
    (d' : HwReg X Z (Finset S × M')) (j : (recHwSpec X Z S M').In i)
    (d : HwReg X Z (Finset S × M'))
    (h : sumKraus (kraus1 X Z L m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m) i r (o, d')
      (j, d) ≠ 0) :
    hwLab d' = hwLabMap i r (hwLab d) := by
  rcases i with ((i | c) | c) | T
  · cases i <;> exact congrArg Prod.fst (hwPort_ne_zero_snd _ h)
  · cases c with
    | readH z upd =>
      simp only [sumKraus, kraus1, hwReadKraus1, readKraus1H] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
    | readK x upd =>
      simp only [sumKraus, kraus1, hwReadKraus1, readKraus1K] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
    | readK' x upd =>
      simp only [sumKraus, kraus1, hwReadKraus1, readKraus1K'] at h
      rw [hwLab, (clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2).2]
      rfl
  · exact congrArg Prod.fst (hwProgKraus_ne_zero_snd c r (s := d) (s' := d') h)
  · rw [hwLab, eq_of_recKraus_ne_zero h]
    rfl

variable {Hh : Set Z} {Hk Hk' : Set X}

/-- At a classical port, `runtimeR` and `runtime1R` agree outside the difference sets. -/
theorem sumKraus_eq_of_not_mem_readHidSet (L : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk') (i : (recHwSpec X Z S M').Port)
    (hi : extCls X Z (Finset S × M') (recSpec S M') i = true)
    (r : (recHwSpec X Z S M').Result i) (o : (recHwSpec X Z S M').Out i)
    (d' : HwReg X Z (Finset S × M')) (j : (recHwSpec X Z S M').In i)
    (d : HwReg X Z (Finset S × M')) (hd : hwLab d ∉ readHidSet Hh Hk Hk' i) :
    sumKraus (kraus2 X Z m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m) i r (o, d') (j, d) =
      sumKraus (kraus1 X Z L m₀) (fun T m ↦ recKraus (X := X) (Z := Z) T m) i r (o, d') (j, d) := by
  obtain ⟨hLh, hLk, hLk'⟩ := hL
  rcases i with ((i | c) | c) | T
  · simp [extCls, hwCls] at hi
  · cases c with
    | readH z upd =>
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) (o, d') (j, d) =
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1H L z upd r) (o, d') (j, d)
      simp only [kroneckerMap_apply, readKrausH, readKraus1H, clsKraus_apply]
      rw [cellRead_congr (w := d.2.1.1) (w' := (hwView d.2.1 L).1) (a := z)
        (by simp only [hwView, hwView_or_eq (w := d.2.1.1) (a := z) hLh hd])]
    | readK x upd =>
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r) (o, d') (j, d) =
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K L x upd r) (o, d') (j, d)
      simp only [kroneckerMap_apply, readKrausK, readKraus1K, clsKraus_apply]
      rw [cellRead_congr (w := d.2.1.2.1) (w' := (hwView d.2.1 L).2.1) (a := x)
        (by simp only [hwView, hwView_or_eq (w := d.2.1.2.1) (a := x) hLk hd])]
    | readK' x upd =>
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r) (o, d') (j, d) =
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKraus1K' L x upd r) (o, d') (j, d)
      simp only [kroneckerMap_apply, readKrausK', readKraus1K', clsKraus_apply]
      rw [cellRead_congr (w := d.2.1.2.2) (w' := (hwView d.2.1 L).2.2) (a := x)
        (by simp only [hwView, hwView_or_eq (w := d.2.1.2.2) (a := x) hLk' hd])]
  · rfl
  · rfl

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The initial state carries no hardwired cell. -/
theorem querySupportedOn_initHw (m₀ : Finset S × M') :
    QuerySupportedOn (hwLab (X := X) (Z := Z) (S := S) (M' := M')) {hwEmpty X Z}
      (initHw X Z m₀).matrix := by
  intro a b h
  rw [initHw, SubState.matrix_basis, Matrix.single_apply] at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact ⟨rfl, rfl⟩
  · exact absurd rfl h

variable [Nonempty X] [Nonempty Z]

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against `runtimeR`, graded.** `√P₁ ≤ √P₂ + ∑ₙ √(4 μₙ) + √ν`, where `μₙ` is the
hidden mass of the `n`-th sponge call (counting the sponge calls only) of the run against
`runtimeR`, and `ν` the hidden mass at the read ports summed over all calls. The program and record
ports cost nothing. -/
theorem sqrt_win_runtime1R_le_graded (L : Hw X Z) (m₀ : Finset S × M') (hL : Covers L Hh Hk Hk')
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) :
    (runtime1R X Z L m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      (runtimeR m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' n, (4 * kindWeight (runtimeR m₀) I (extCls X Z (Finset S × M') (recSpec S M'))
          (extWeight (hiddenMass Hh Hk Hk')) x
            (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n) ^ (2⁻¹ : ℝ) +
        (runtimeR m₀).totalWeight I (readMass Hh Hk Hk') x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
  have h := rpow_inv_two_outcomeLawWith_le_graded I (initHw X Z m₀)
    (extend_branch_eq_conj (runtime2 X Z m₀) recStep (runtime2_branch m₀)
      fun T r ↦ recStep_branch T r)
    (extend_branch_eq_conj (runtime1 X Z L m₀) recStep (runtime1_branch L m₀)
      fun T r ↦ recStep_branch T r)
    (cls := extCls X Z (Finset S × M') (recSpec S M')) (κ := hwLab) (F := hwLabMap)
    (S := readHidSet Hh Hk Hk') (hwLab_sumKraus2 m₀) (hwLab_sumKraus1 L m₀)
    (sumKraus_eq_of_not_mem_readHidSet L m₀ hL) (hwEmpty X Z) (querySupportedOn_initHw m₀)
    x ρ f hE
  rw [clsMass_readHidSet] at h
  refine h.trans (add_le_add (add_le_add le_rfl
    (ENNReal.tsum_le_tsum fun n ↦ ENNReal.rpow_le_rpow ?_ (by norm_num))) le_rfl)
  rw [← kindWeight_const_mul]
  exact kindWeight_mono _ I _ (fun i σ hσ ↦ krausWeight_le_hidden_extend L m₀ hL _ i hσ) x
    (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef n

/-- **Runtime 1 against `runtimeR`, graded, averaged over the table.** If the averaged hidden mass
of the `n`-th sponge call is at most `μ n` and the averaged hidden mass at the read ports, summed
over all calls, at most `ν`, then `E P₁ ≤ (√(E P₂) + ∑ₙ √(4 μ n) + √ν)²`. -/
theorem uavg_win_runtime1R_le_graded {Θ : Type*} [Fintype Θ] (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M') (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E)
    (μ : ℕ → ℝ≥0∞) (ν : ℝ≥0∞)
    (hμ : ∀ n, uavg (fun θ ↦ kindWeight (runtimeR m₀) I
      (extCls X Z (Finset S × M') (recSpec S M')) (extWeight (hiddenMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)))
        (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) n) ≤ μ n)
    (hν : uavg (fun θ ↦ (runtimeR m₀).totalWeight I (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) ≤ ν) :
    uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ^ (2⁻¹ : ℝ) +
        ∑' n, (4 * μ n) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (uavg_le_of_hybrid_graded _ _ _ _ fun θ ↦ sqrt_win_runtime1R_le_graded I (L θ) m₀ (hL θ)
    (x θ) (ρ θ) (f θ) hE).trans ?_
  exact pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl (ENNReal.tsum_le_tsum fun n ↦
    ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (hμ n) zero_le) (by norm_num)))
    (ENNReal.rpow_le_rpow hν (by norm_num))) 2

/-- **Runtime 1 against `runtimeR`, averaged, with the sponge masses summed** (Cauchy-Schwarz over
at most `q` sponge calls on every path, `tsum_rpow_kindWeight_le`): if the averaged hidden mass at
the sponge ports, summed over all calls, is at most `μ`, and that at the read ports at most `ν`,
then `E P₁ ≤ (√(E P₂) + √(4 q μ) + √ν)²`. Disclose-style bounds relative to the calls of the sponge
ports (`sum_queryWeight_portMass_runtimeR_le`, `sum_totalWeight_le_of_forall`) give `μ ≤ q κ`. -/
theorem uavg_win_runtime1R_le_graded_total {Θ : Type*} [Fintype Θ] (L : Θ → Hw X Z)
    (Hhθ : Θ → Set Z) (Hkθ Hk'θ : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (m₀ : Finset S × M') (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : Θ → SubState A) (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (q : ℕ)
    (hq : ∀ θ, IFreeM.IsChargeBound (x θ) (portCharge fun i ↦
      if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (μ ν : ℝ≥0∞)
    (hμ : uavg (fun θ ↦ (runtimeR m₀).totalWeight I (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) ≤ μ)
    (hν : uavg (fun θ ↦ (runtimeR m₀).totalWeight I (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) ≤ ν) :
    uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ^ (2⁻¹ : ℝ) +
        (4 * (q * μ)) ^ (2⁻¹ : ℝ) + ν ^ (2⁻¹ : ℝ)) ^ 2 := by
  set T : Θ → ℝ≥0∞ := fun θ ↦ (runtimeR m₀).totalWeight I (spongeMass (Hhθ θ) (Hkθ θ) (Hk'θ θ))
    (x θ) ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) with hT
  have hz : ∀ (c : ℝ≥0∞), ∑' n : ℕ, (4 * if n = 0 then c else 0) ^ (2⁻¹ : ℝ) =
      (4 * c) ^ (2⁻¹ : ℝ) := fun c ↦ by
    rw [tsum_eq_single 0 fun n hn ↦ by
      simp [hn, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]]
    simp
  have hθ : ∀ θ, (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E ^ (2⁻¹ : ℝ) ≤
      (runtimeR m₀).evalDistMap I (x θ) (ρ θ) (f θ) E ^ (2⁻¹ : ℝ) +
        ∑' n : ℕ, (4 * if n = 0 then (q : ℝ≥0∞) * T θ else 0) ^ (2⁻¹ : ℝ) +
        (runtimeR m₀).totalWeight I (readMass (Hhθ θ) (Hkθ θ) (Hk'θ θ)) (x θ)
          ((ρ θ).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ) := by
    intro θ
    rw [hz]
    refine (sqrt_win_runtime1R_le_graded I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hE).trans
      (add_le_add (add_le_add le_rfl ((tsum_rpow_kindWeight_le (runtimeR m₀) I _ (x θ) (hq θ)
        _ 4).trans_eq ?_)) le_rfl)
    simp only [hT, spongeMass_eq]
    rw [mul_left_comm]
    rfl
  refine (uavg_le_of_hybrid_graded _ _ _ _ hθ).trans ?_
  have hu : ∀ n : ℕ, uavg (fun θ ↦ if n = 0 then (q : ℝ≥0∞) * T θ else 0) =
      if n = 0 then (q : ℝ≥0∞) * uavg T else 0 := fun n ↦ by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, uavg_const_mul]
    · simp [hn, uavg]
  simp only [hu, hz]
  exact pow_le_pow_left₀ zero_le (add_le_add (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hμ zero_le)
      zero_le) (by norm_num)))
    (ENNReal.rpow_le_rpow hν (by norm_num))) 2

variable {Sv : Type} [Fintype Sv] [DecidableEq Sv] {Dv : Sv → Type} [∀ s, Fintype (Dv s)]
  [∀ s, DecidableEq (Dv s)] [∀ s, Nonempty (Dv s)]

/-- **Disclose's per-call hidden-mass bound for `runtimeR`, relative to the calls of the ports
`Q`** (`sum_queryWeight_hiddenMass_runtimeR_le` with the masses `portMass Q`): under
`viewByOn_gameT`'s `ViewByOn` (the ports of runtime 2), the hidden masses at the `j`-th call, summed
over the hidden values, are at most `κ` times the traces of the inputs of the `j`-th call when it
calls a port of `Q`. With `Q` the sponge ports (`spongeMass`) or the classical ports (`readMass`)
and summed over the calls (`sum_totalWeight_le_of_forall`), this bounds the masses of
`uavg_win_runtime1R_le_graded_total` by `κ` times the number of sponge calls, resp. classical
calls (`totalWeight_trace_le_of_isChargeBound`). -/
theorem sum_queryWeight_portMass_runtimeR_le (Q : (recHwSpec X Z S M').Port → Prop)
    [DecidablePred Q] (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset Sv)
    (x : ((s : Sv) → Dv s) → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : ((s : Sv) → Dv s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M')))
      (A × QReg.of (HwReg X Z (Finset S × M'))) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (runtimeR m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hhv : ((s : Sv) → Dv s) → Set Z) (Hkv Hk'v : ((s : Sv) → Dv s) → Set X)
    (sh : Z → HwReg X Z (Finset S × M') → Finset Sv)
    (sk sk' : X → HwReg X Z (Finset S × M') → Finset Sv)
    (Fh : Z → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s))
    (Fk Fk' : X → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s))
    (hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v)
    (hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v)
    (hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v)
    (hh : ∀ v z r, z ∈ Hhv v → r.2.1.1 z = none → ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v)
    (hk : ∀ v y r, y ∈ Hkv v → r.2.1.2.1 y = none →
      ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v)
    (hk' : ∀ v y r, y ∈ Hk'v v → r.2.1.2.2 y = none →
      ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v)
    (κ : ℝ≥0∞)
    (hκh : ∀ z r v, ∑ s ∈ sh z r,
      ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk : ∀ y r v, ∑ s ∈ sk y r,
      ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk' : ∀ y r v, ∑ s ∈ sk' y r,
      ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, (runtimeR m₀).queryWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) j ≤
      κ * ∑ v, (runtimeR m₀).queryWeight I
        (fun i σ ↦ if Q i then ENNReal.ofReal σ.trace.re else 0) (x v) (ρ v) j := by
  have hw : ∀ v, (runtimeR m₀).queryWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) j =
      (runtimeR m₀).queryWeight I (fun i ↦ diagMass
        (if Q i then extHidSet (Hhv v) (Hkv v) (Hk'v v) i else ∅)) (x v) (ρ v) j := fun v ↦
    congrArg (fun w ↦ (runtimeR m₀).queryWeight I w (x v) (ρ v) j)
      (funext fun i ↦ funext fun σ ↦ by
        by_cases hQi : Q i
        · simp only [portMass, hQi, ↓reduceIte]
          exact congrFun (congrFun (extWeight_hiddenMass_eq _ _ _) i) σ
        · simp only [portMass, hQi, ↓reduceIte]
          exact (Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).symm)
  rw [Finset.sum_congr rfl fun v _ ↦ hw v]
  refine sum_queryWeight_view_le_on (runtimeR m₀) I lab x ρ hρ j _ hview Q
    (fun v i ↦ if Q i then extHidSet (Hhv v) (Hkv v) (Hk'v v) i else ∅)
    (fun v i hi ↦ ?_) (fun v i hi ↦ by simp only [hi, ↓reduceIte])
    (sumPort (liftCells sh sk sk' ∅) fun _ _ ↦ ∅)
    (sumPort (liftCells Fh Fk Fk' fun _ _ ↦ ∅) fun _ _ _ _ ↦ ∅) (fun i p s v d ↦ ?_)
    (fun v i p hp ↦ ?_) κ (fun i p v ↦ ?_)
  · rcases i with i | T
    · exact absurd rfl hi
    · by_cases hQi : Q (Sum.inr T)
      · simp only [hQi, ↓reduceIte]
        rfl
      · simp only [hQi, ↓reduceIte]
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · rfl
    · rfl
  · by_cases hQi : Q i
    · simp only [hQi, ↓reduceIte] at hp
      rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
      · exact hh v _ _ hp.1 hp.2
      · exact hk v _ _ hp.1 hp.2
      · exact hk' v _ _ hp.1 hp.2
      · exact hh v _ _ hp.1 hp.2
      · exact hk v _ _ hp.1 hp.2
      · exact hk' v _ _ hp.1 hp.2
      · exact hp.elim
      · exact hp.elim
    · simp only [hQi, ↓reduceIte] at hp
      exact hp.elim
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | T
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · simp [sumPort, liftCells]
    · simp [sumPort]

/-- **The total hidden mass at the ports `Q` for `runtimeR`**
(`sum_queryWeight_portMass_runtimeR_le` at every call, summed): with at most `q` calls of the ports
`Q` on every path, the hidden masses at the ports `Q` summed over all calls and over the hidden
values are at most `κ q` times the traces.
With `Q` the sponge ports this bounds the `μ` of `uavg_win_runtime1R_le_graded_total`, with `Q` the
classical ports its `ν`. -/
theorem sum_totalWeight_portMass_runtimeR_le (Q : (recHwSpec X Z S M').Port → Prop)
    [DecidablePred Q] (m₀ : Finset S × M') (lab : HwReg X Z (Finset S × M') → Finset Sv)
    (x : ((s : Sv) → Dv s) → QuantumComp Λ (recHwSpec X Z S M') Xf A)
    (ρ : ((s : Sv) → Dv s) → Matrix (A × QReg.of (HwReg X Z (Finset S × M')))
      (A × QReg.of (HwReg X Z (Finset S × M'))) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef)
    (hview : ∀ j, ViewByOn (runtimeR m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hhv : ((s : Sv) → Dv s) → Set Z) (Hkv Hk'v : ((s : Sv) → Dv s) → Set X)
    (sh : Z → HwReg X Z (Finset S × M') → Finset Sv)
    (sk sk' : X → HwReg X Z (Finset S × M') → Finset Sv)
    (Fh : Z → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s))
    (Fk Fk' : X → HwReg X Z (Finset S × M') → (s : Sv) → ((s : Sv) → Dv s) → Finset (Dv s))
    (hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v)
    (hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v)
    (hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v)
    (hh : ∀ v z r, z ∈ Hhv v → r.2.1.1 z = none → ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v)
    (hk : ∀ v y r, y ∈ Hkv v → r.2.1.2.1 y = none →
      ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v)
    (hk' : ∀ v y r, y ∈ Hk'v v → r.2.1.2.2 y = none →
      ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v)
    (κ : ℝ≥0∞)
    (hκh : ∀ z r v, ∑ s ∈ sh z r,
      ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk : ∀ y r v, ∑ s ∈ sk y r,
      ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk' : ∀ y r v, ∑ s ∈ sk' y r,
      ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (Dv s) : ℝ≥0∞)⁻¹ ≤ κ) {q : ℕ}
    (hq : ∀ v, IFreeM.IsChargeBound (x v) (portCharge fun i ↦ if Q i then 1 else 0) q) :
    ∑ v, (runtimeR m₀).totalWeight I (portMass Q (Hhv v) (Hkv v) (Hk'v v)) (x v) (ρ v) ≤
      κ * (q * ∑ v, ENNReal.ofReal (ρ v).trace.re) := by
  refine (sum_totalWeight_le_of_forall (runtimeR m₀) I _ _ x ρ κ fun j ↦
    sum_queryWeight_portMass_runtimeR_le I Q m₀ lab x ρ hρ j (hview j) Hhv Hkv Hk'v sh sk sk' Fh
      Fk Fk' hFh hFk hFk' hh hk hk' κ hκh hκk hκk').trans
    (mul_le_mul_of_nonneg_left ?_ zero_le)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ ↦
    totalWeight_trace_le_of_isChargeBound' (runtimeR m₀) I Q (x v) (hq v) (hρ v)

end runtimeR

end Quantum.Xmss.Hybrid

end
