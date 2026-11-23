module

public import Quantum.StdModel.Decide
public import Quantum.StdModel.Props.Prf
public import Quantum.Xmss.Hybrid.Seed
public import Quantum.Qrom.TableLaw
public import VCVio.Quantum.VC.Emulated

@[expose] public section

/-!
# QROM bounds of the PRF properties (design D1, D2)

At `romWorld`, averaged over the uniform table, the signed PRF advantage of a property adversary
making at most `q` hash calls (`cmdCharge hashCharge`) is at most `4 q √κ` in absolute value, `κ`
the largest probability over the hidden key that a given cell is keyed.

* **Two tables** (`sqrt_tabProb_le`): against the oracles of two functions that agree outside a
  set `C`, the square roots of the laws differ, both ways, by `∑ⱼ √(4 μⱼ)`, `μⱼ` the mass in `C`
  of the `j`-th query against the first (VCVio's square-root hybrid). Averaged over hidden data
  `θ` with `Pr_θ[z ∈ C θ] ≤ κ` for every cell `z` (`uavg_hybrid_tables`): `E P₁ ≤ (√E P₂ + d)²`
  and `E P₂ ≤ (√E P₁ + d)²` with `d = q √(4 κ)`, so `|E P₁ - E P₂| ≤ 2 d`.
* **The games at a fixed table** (`succAt_prfReal`, `succAt_prfIdeal`): averages over the key or
  the function of the game `fixExp g` whose challenger answers `x` by `g x`; a challenger's answer
  matters only through its sampler at the table (`run_substitute_answerSub_congr`).
* **The keyed cells reprogrammed** (`uavg_tab_eq_fill`, from `LazyTable.sum_sum_fill`): averaging
  the real game over the table is averaging over uniform values `v` the game `fixExp (trunc ∘ v)`
  against the table with the keyed cells overwritten by `v`; the ideal game runs the same program
  against the table itself.
* Main statements (all hash calls of the adversary charged, its classical PRF queries free):
  `abs_avg_kimPrfAdv_le` (`4 q √(N / |Key|)`), `abs_avg_derivedKimPrfAdv_le`
  (`4 q √(1 / |Seed| + N / |HashOutput|)`), `abs_avg_prfMsgAdv_le` (`4 q √(N / |Key|)`), with `N`
  bounding the keys that make a given string a keyed input (`card_filter_kimInput_le`: the number
  of prefix lengths, for injective keys of one length). The `slRed` forms charge the reduction's
  honest hash calls like the adversary's (`isChargeBound_slRed_hash`).
-/

open IPFunctor OracleComp OracleSpec Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.StdModel.Qrom

open Quantum Quantum.Qrom Props HashSig
open Quantum.Xmss.Hybrid (diagMass uavg uavg_le_of_hybrid tsum_ofReal_trace_conj_sub_le
  sub_eq_sub_mul_setProj)

/-! ## Uniform averages -/

section avg

variable {α β : Type*} [Fintype α] [Fintype β]

theorem uavg_prod (f : α × β → ℝ≥0∞) : uavg f = uavg fun a ↦ uavg fun b ↦ f (a, b) := by
  unfold uavg
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _))
    (.inl (ENNReal.natCast_ne_top _)), Fintype.sum_prod_type, mul_assoc]
  simp only [Finset.mul_sum]

theorem uavg_comm (f : α → β → ℝ≥0∞) :
    (uavg fun a ↦ uavg fun b ↦ f a b) = uavg fun b ↦ uavg fun a ↦ f a b := by
  simp only [uavg, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

theorem uavg_equiv (e : α ≃ β) (f : β → ℝ≥0∞) : (uavg fun a ↦ f (e a)) = uavg f := by
  unfold uavg
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

theorem uavg_const [Nonempty α] (c : ℝ≥0∞) : (uavg fun _ : α ↦ c) = c := by
  unfold uavg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_mul]

theorem uavg_le_of_sum_le' [Nonempty α] (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∑ a, f a ≤ c * Fintype.card α) : uavg f ≤ c := by
  have h0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uavg
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * (c * Fintype.card α) := by gcongr
    _ = c := by rw [mul_comm c, ← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _),
      one_mul]

theorem uavg_le_one [Nonempty α] {f : α → ℝ≥0∞} (h : ∀ a, f a ≤ 1) : uavg f ≤ 1 :=
  (Quantum.Xmss.Hybrid.uavg_mono h).trans_eq (uavg_const 1)

theorem toReal_uavg {f : α → ℝ≥0∞} (h : ∀ a, f a ≠ ⊤) :
    (uavg f).toReal = ∑ a, (Fintype.card α : ℝ)⁻¹ * (f a).toReal := by
  unfold uavg
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun a _ ↦ h a, Finset.mul_sum]

/-- **Reprogramming the cells of a lazy table**: averaging over the table a function of the table
and its values is averaging over values `v` and tables the function at `v` and the table with the
cells of `v` overwritten by `v`. -/
theorem uavg_tab_eq_fill {Pos D Y : Type} [Fintype Pos] [DecidableEq Pos] [Fintype D]
    [DecidableEq D] [Fintype Y] [Zero Y] (T : LazyTable Pos D Y)
    (F : (Pos → Y) → (D → Y) → ℝ≥0∞) :
    (uavg fun H ↦ F (T.tab H) H) = uavg fun v ↦ uavg fun H ↦ F v (T.fill v v H) := by
  have hc : (Fintype.card (Pos → Y) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hs := T.sum_sum_fill F
  unfold uavg
  simp only [← Finset.mul_sum]
  rw [hs, nsmul_eq_mul, mul_left_comm _ (Fintype.card (Pos → Y) : ℝ≥0∞), ← mul_assoc,
    ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _), one_mul]

end avg

/-! ## Two tables -/

section tables

variable {D Y : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The probability that a program returns `true` against the oracle of `H`. -/
noncomputable def tabProb (H : D → Y)
    (x : QComp (qromSpec D Y) (QReg.of Unit) (QReg.of Unit) Bool) : ℝ≥0∞ :=
  (additiveOracleRuntime H).evalDistMap .instruments x (SubState.basis ()) (fun p ↦ p.2.2) {true}

/-- **The hit mass of a set of cells**: the mass of the query inputs in `C`. -/
noncomputable def hitW (C : Set D) (i : (qromSpec D Y).Port)
    (σ : Matrix ((qromSpec D Y).In i × QReg.of Unit) ((qromSpec D Y).In i × QReg.of Unit) ℂ) :
    ℝ≥0∞ :=
  diagMass {p : (D × Y) × Unit | p.1.1 ∈ C} σ

/-- The joint initial operator of a run on the trivial register. -/
noncomputable abbrev rho0 : Matrix (QReg.of Unit × QReg.of Unit) (QReg.of Unit × QReg.of Unit) ℂ :=
  (SubState.basis () : SubState (QReg.of Unit)).matrix ⊗ₖ
    (SubState.basis () : SubState (QReg.of Unit)).matrix

theorem rho0_posSemidef : (rho0 : Matrix (QReg.of Unit × QReg.of Unit) _ ℂ).PosSemidef :=
  ((SubState.basis () : SubState (QReg.of Unit)).prod (SubState.basis ())).posSemidef

theorem ofReal_trace_rho0_le_one : ENNReal.ofReal (rho0 : Matrix (QReg.of Unit × QReg.of Unit)
    (QReg.of Unit × QReg.of Unit) ℂ).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis () : SubState (QReg.of Unit)).prod (SubState.basis ())).trace_re_le_one

/-- The query of `H` is the Kraus map of its oracle unitary beside the trivial register. -/
theorem branch_additiveOracleRuntime (H : D → Y) (i : (qromSpec D Y).Port)
    (r : (qromSpec D Y).Result i) :
    ((additiveOracleRuntime H).step i).branch r =
      MatrixMap.conj (oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ)) := by
  rw [additiveOracleRuntime_step, DSubInstrument.branch_frame_apply, branch_oracleQuery_apply,
    MatrixMap.amplify_conj]

/-- **The Kraus weight of two tables that agree outside `C`**: at most `4` times the hit mass. -/
theorem krausWeight_oracle_le (C : Set D) {H H' : D → Y} (hH : ∀ z, z ∉ C → H z = H' z)
    (σ : Matrix ((D × Y) × Unit) ((D × Y) × Unit) ℂ) (hσ : σ.PosSemidef) :
    ∑' _r : Unit, ENNReal.ofReal (MatrixMap.conj (oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ) -
      oracleUnitary H' ⊗ₖ (1 : Matrix Unit Unit ℂ)) σ).trace.re ≤
        4 * diagMass {p : (D × Y) × Unit | p.1.1 ∈ C} σ := by
  have hK : ∀ G : D → Y, ∑ _r : Unit, (oracleUnitary G ⊗ₖ (1 : Matrix Unit Unit ℂ))ᴴ *
      (oracleUnitary G ⊗ₖ (1 : Matrix Unit Unit ℂ)) = 1 := fun G ↦ by
    rw [Fintype.sum_unique, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      conjTranspose_oracleUnitary_mul_self, Matrix.one_mul, one_kronecker_one]
  refine tsum_ofReal_trace_conj_sub_le (fun _ : Unit ↦ oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ))
    (fun _ ↦ oracleUnitary H' ⊗ₖ (1 : Matrix Unit Unit ℂ)) (hK H) (hK H') _
    (fun _ ↦ sub_eq_sub_mul_setProj _ _ _ fun i j hj ↦ ?_) hσ
  simp only [kroneckerMap_apply, oracleUnitary_apply, hH j.1.1 hj]

/-- **The hybrid between two tables**, both ways: against tables that agree outside `C`, the
square roots of the laws differ by `∑ⱼ √(4 μⱼ)`, `μⱼ` the hit mass of `C` at the `j`-th query of
the run against `H`. -/
theorem sqrt_tabProb_le (C : Set D) {H H' : D → Y} (hH : ∀ z, z ∉ C → H z = H' z)
    (x : QComp (qromSpec D Y) (QReg.of Unit) (QReg.of Unit) Bool) :
    tabProb H' x ^ (2⁻¹ : ℝ) ≤ tabProb H x ^ (2⁻¹ : ℝ) + ∑' j, (4 *
      (additiveOracleRuntime H).queryWeight .instruments (hitW C) x rho0 j) ^ (2⁻¹ : ℝ) ∧
    tabProb H x ^ (2⁻¹ : ℝ) ≤ tabProb H' x ^ (2⁻¹ : ℝ) + ∑' j, (4 *
      (additiveOracleRuntime H).queryWeight .instruments (hitW C) x rho0 j) ^ (2⁻¹ : ℝ) := by
  have hk : ∀ w : ∀ i, Matrix ((qromSpec D Y).In i × (additiveOracleRuntime H).D)
      ((qromSpec D Y).In i × (additiveOracleRuntime H).D) ℂ → ℝ≥0∞,
      (∀ i σ, σ.PosSemidef → w i σ ≤ 4 * hitW C i σ) → ∀ j,
      ((additiveOracleRuntime H).queryWeight .instruments w x rho0 j) ^ (2⁻¹ : ℝ) ≤
        (4 * (additiveOracleRuntime H).queryWeight .instruments (hitW C) x rho0 j) ^ (2⁻¹ : ℝ) :=
    fun w hw j ↦ ENNReal.rpow_le_rpow (((additiveOracleRuntime H).queryWeight_mono
      LocalSig.Interp.instruments (w := w) (w' := fun i σ ↦ 4 * hitW C i σ) hw x
        rho0_posSemidef j).trans_eq ((additiveOracleRuntime H).queryWeight_const_mul
          LocalSig.Interp.instruments (w := hitW C) 4 x rho0 j)) (by norm_num)
  have h₁ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le LocalSig.Interp.instruments
    (SubState.basis ()) (branch_additiveOracleRuntime H) (branch_additiveOracleRuntime H') x
    (SubState.basis ()) (fun p ↦ p.2.2) (measurableSet_singleton true)
  have h₂ := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' LocalSig.Interp.instruments
    (SubState.basis ()) (branch_additiveOracleRuntime H) (branch_additiveOracleRuntime H') x
    (SubState.basis ()) (fun p ↦ p.2.2) (measurableSet_singleton true)
  exact ⟨h₂.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum
      (hk _ fun _ σ hσ ↦ krausWeight_oracle_le C hH σ hσ))),
    h₁.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum
      (hk _ fun _ σ hσ ↦ krausWeight_oracle_le C hH σ hσ)))⟩

omit [AddCommGroup Y] in
/-- Averaged over `θ`, the hit masses of the sets `C θ` weigh at most `c` times the trace when
every cell lies in `C θ` for weight at most `c`. -/
theorem sum_hitW_le {Θ : Type} [Fintype Θ] (C : Θ → Set D) (c : ℝ≥0∞)
    (hC : ∀ z, ∑ θ, (C θ).indicator (1 : D → ℝ≥0∞) z ≤ c) (i : (qromSpec D Y).Port)
    (σ : Matrix ((D × Y) × Unit) ((D × Y) × Unit) ℂ) (hσ : σ.PosSemidef) :
    ∑ θ, hitW (C θ) i σ ≤ c * ENNReal.ofReal σ.trace.re := by
  have hd : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 (hσ.diag_nonneg (i := a))).1
  have htr : ENNReal.ofReal σ.trace.re = ∑ a, ENNReal.ofReal (σ a a).re := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hd a]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  simp only [hitW, diagMass]
  rw [Finset.sum_comm, htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  calc ∑ θ, {p : (D × Y) × Unit | p.1.1 ∈ C θ}.indicator
        (fun a ↦ ENNReal.ofReal (σ a a).re) a
      = (∑ θ, (C θ).indicator (1 : D → ℝ≥0∞) a.1.1) * ENNReal.ofReal (σ a a).re := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun θ _ ↦ ?_
        by_cases h : a.1.1 ∈ C θ <;> simp [Set.indicator, h]
    _ ≤ c * ENNReal.ofReal (σ a a).re := mul_le_mul_of_nonneg_right (hC a.1.1) zero_le

/-- **The hybrid between tables, averaged.** Programs `x ψ` with at most `q` queries run against
`T₀ ψ` and against tables `T₁ θ ψ` that agree with `T₀ ψ` outside `C θ ψ`; if every cell lies in
`C θ ψ` with probability at most `κ` over `θ`, the averaged laws satisfy
`E P₁ ≤ (√E P₂ + q √(4 κ))²` and `E P₂ ≤ (√E P₁ + q √(4 κ))²`. -/
theorem uavg_hybrid_tables {Θ Ψ : Type} [Fintype Θ] [Nonempty Θ] [Fintype Ψ] [Nonempty Ψ]
    (T₀ : Ψ → D → Y) (T₁ : Θ → Ψ → D → Y) (C : Θ → Ψ → Set D)
    (hT : ∀ θ ψ z, z ∉ C θ ψ → T₀ ψ z = T₁ θ ψ z)
    (x : Ψ → QComp (qromSpec D Y) (QReg.of Unit) (QReg.of Unit) Bool) {q : ℕ}
    (hq : ∀ ψ, (x ψ).IsTotalQueryBound q) (κ : ℝ≥0∞)
    (hκ : ∀ ψ z, ∑ θ, (C θ ψ).indicator (1 : D → ℝ≥0∞) z ≤ κ * Fintype.card Θ) :
    (uavg fun p : Θ × Ψ ↦ tabProb (T₁ p.1 p.2) (x p.2)) ≤
        ((uavg fun ψ ↦ tabProb (T₀ ψ) (x ψ)) ^ (2⁻¹ : ℝ) + q * (4 * κ) ^ (2⁻¹ : ℝ)) ^ 2 ∧
      (uavg fun ψ ↦ tabProb (T₀ ψ) (x ψ)) ≤
        ((uavg fun p : Θ × Ψ ↦ tabProb (T₁ p.1 p.2) (x p.2)) ^ (2⁻¹ : ℝ) +
          q * (4 * κ) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set μ : Θ × Ψ → ℕ → ℝ≥0∞ := fun p j ↦
    (additiveOracleRuntime (T₀ p.2)).queryWeight .instruments (hitW (C p.1 p.2)) (x p.2) rho0 j
    with hμdef
  have hP₂ : (uavg fun p : Θ × Ψ ↦ tabProb (T₀ p.2) (x p.2)) =
      uavg fun ψ ↦ tabProb (T₀ ψ) (x ψ) := by
    rw [uavg_prod]
    exact uavg_const (α := Θ) (uavg fun ψ ↦ tabProb (T₀ ψ) (x ψ))
  have hlt : ∀ j, (uavg fun p ↦ μ p j) ≤ κ := fun j ↦ by
    refine uavg_le_of_sum_le' _ _ ?_
    rw [Fintype.sum_prod_type_right, Fintype.card_prod, Nat.cast_mul]
    have hψ : ∀ ψ, ∑ θ, μ (θ, ψ) j ≤ κ * Fintype.card Θ := fun ψ ↦ by
      have hsum := (additiveOracleRuntime (T₀ ψ)).tsum_queryWeight LocalSig.Interp.instruments
        (fun θ ↦ hitW (Y := Y) (C θ ψ)) (x ψ) rho0 j
      simp only [tsum_fintype] at hsum
      simp only [hμdef]
      rw [hsum]
      calc (additiveOracleRuntime (T₀ ψ)).queryWeight .instruments
            (fun i σ ↦ ∑ θ, hitW (C θ ψ) i σ) (x ψ) rho0 j
          ≤ (additiveOracleRuntime (T₀ ψ)).queryWeight .instruments
            (fun _ σ ↦ (κ * Fintype.card Θ) * ENNReal.ofReal σ.trace.re) (x ψ) rho0 j :=
            QuantumRuntime.queryWeight_mono _ _
              (fun i σ hσ ↦ sum_hitW_le (fun θ ↦ C θ ψ) _ (hκ ψ) i σ hσ) _ rho0_posSemidef j
        _ = (κ * Fintype.card Θ) * (additiveOracleRuntime (T₀ ψ)).queryWeight .instruments
            (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (x ψ) rho0 j :=
            QuantumRuntime.queryWeight_const_mul _ _ _ _ _ _
        _ ≤ (κ * Fintype.card Θ) * 1 := by
            gcongr
            exact ((additiveOracleRuntime (T₀ ψ)).queryWeight_le_ofReal_trace _
              (fun _ _ _ ↦ le_rfl) _ rho0_posSemidef j).trans ofReal_trace_rho0_le_one
        _ = κ * Fintype.card Θ := mul_one _
    calc ∑ ψ, ∑ θ, μ (θ, ψ) j ≤ ∑ _ψ : Ψ, κ * Fintype.card Θ := Finset.sum_le_sum fun ψ _ ↦ hψ ψ
      _ = κ * (Fintype.card Θ * Fintype.card Ψ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hzero : ∀ j ∉ Finset.range q, (4 * uavg fun p ↦ μ p j) ^ (2⁻¹ : ℝ) = 0 := fun j hj ↦ by
    have h0 : ∀ p, μ p j = 0 := fun p ↦
      (additiveOracleRuntime (T₀ p.2)).queryWeight_eq_zero_of_isTotalQueryBound _ (hq p.2)
        (by simpa using hj) _
    simp only [h0, uavg, Finset.sum_const_zero, mul_zero]
    exact ENNReal.zero_rpow_of_pos (by norm_num)
  have hS : ∑' j, (4 * uavg fun p ↦ μ p j) ^ (2⁻¹ : ℝ) ≤ q * (4 * κ) ^ (2⁻¹ : ℝ) := by
    rw [tsum_eq_sum hzero]
    calc ∑ j ∈ Finset.range q, (4 * uavg fun p ↦ μ p j) ^ (2⁻¹ : ℝ)
        ≤ ∑ _j ∈ Finset.range q, (4 * κ) ^ (2⁻¹ : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ ENNReal.rpow_le_rpow
            (mul_le_mul_of_nonneg_left (hlt j) zero_le)
            (by norm_num)
      _ = q * (4 * κ) ^ (2⁻¹ : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h₁ := uavg_le_of_hybrid (fun p : Θ × Ψ ↦ tabProb (T₁ p.1 p.2) (x p.2))
    (fun p ↦ tabProb (T₀ p.2) (x p.2)) μ fun p ↦
      (sqrt_tabProb_le (C p.1 p.2) (hT p.1 p.2) (x p.2)).1
  have h₂ := uavg_le_of_hybrid (fun p : Θ × Ψ ↦ tabProb (T₀ p.2) (x p.2))
    (fun p ↦ tabProb (T₁ p.1 p.2) (x p.2)) μ fun p ↦
      (sqrt_tabProb_le (C p.1 p.2) (hT p.1 p.2) (x p.2)).2
  rw [hP₂] at h₁ h₂
  exact ⟨h₁.trans (pow_le_pow_left₀ zero_le (add_le_add le_rfl hS) 2),
    h₂.trans (pow_le_pow_left₀ zero_le (add_le_add le_rfl hS) 2)⟩

end tables

/-! ## From the squared hybrid to the advantage -/

theorem rpow_two_inv_two {u : ℝ≥0∞} : (u ^ (2 : ℕ)) ^ (2⁻¹ : ℝ) = u := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem inv_two_rpow_two {u : ℝ≥0∞} : (u ^ (2⁻¹ : ℝ)) ^ (2 : ℕ) = u := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Both squared hybrids bound the difference**: `|a - b| ≤ 2 d`. -/
theorem abs_toReal_sub_le_of_hybrid {a b d : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) (hd : d ≠ ⊤)
    (h₁ : a ≤ (b ^ (2⁻¹ : ℝ) + d) ^ 2) (h₂ : b ≤ (a ^ (2⁻¹ : ℝ) + d) ^ 2) :
    |a.toReal - b.toReal| ≤ 2 * d.toReal := by
  have e₁ : a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + d :=
    (ENNReal.rpow_le_rpow h₁ (by norm_num)).trans_eq rpow_two_inv_two
  have e₂ : b ^ (2⁻¹ : ℝ) ≤ a ^ (2⁻¹ : ℝ) + d :=
    (ENNReal.rpow_le_rpow h₂ (by norm_num)).trans_eq rpow_two_inv_two
  have ha' : a ^ (2⁻¹ : ℝ) ≤ 1 := ENNReal.rpow_le_one ha (by norm_num)
  have hb' : b ^ (2⁻¹ : ℝ) ≤ 1 := ENNReal.rpow_le_one hb (by norm_num)
  have hat : a ^ (2⁻¹ : ℝ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha'
  have hbt : b ^ (2⁻¹ : ℝ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb'
  have hs : a.toReal = (a ^ (2⁻¹ : ℝ)).toReal ^ 2 := by
    rw [← ENNReal.toReal_pow, inv_two_rpow_two]
  have ht : b.toReal = (b ^ (2⁻¹ : ℝ)).toReal ^ 2 := by
    rw [← ENNReal.toReal_pow, inv_two_rpow_two]
  have es : (a ^ (2⁻¹ : ℝ)).toReal ≤ (b ^ (2⁻¹ : ℝ)).toReal + d.toReal := by
    rw [← ENNReal.toReal_add hbt hd]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hbt, hd⟩) e₁
  have et : (b ^ (2⁻¹ : ℝ)).toReal ≤ (a ^ (2⁻¹ : ℝ)).toReal + d.toReal := by
    rw [← ENNReal.toReal_add hat hd]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hat, hd⟩) e₂
  have s1 : (a ^ (2⁻¹ : ℝ)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha'
  have t1 : (b ^ (2⁻¹ : ℝ)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hb'
  set s := (a ^ (2⁻¹ : ℝ)).toReal
  set t := (b ^ (2⁻¹ : ℝ)).toReal
  set r := d.toReal
  have s0 : 0 ≤ s := ENNReal.toReal_nonneg
  have t0 : 0 ≤ t := ENNReal.toReal_nonneg
  have r0 : 0 ≤ r := ENNReal.toReal_nonneg
  have k₁ : (s - t) * (s + t) ≤ r * (s + t) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have k₂ : (t - s) * (s + t) ≤ r * (s + t) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have k₃ : r * (s + t) ≤ r * 2 := mul_le_mul_of_nonneg_left (by linarith) r0
  rw [hs, ht, abs_le]
  constructor <;> nlinarith

/-- The closed form of `2 d` for `d = q √(4 κ)`. -/
theorem two_mul_toReal_hyb (q : ℕ) {κ : ℝ≥0∞} :
    2 * ((q : ℝ≥0∞) * (4 * κ) ^ (2⁻¹ : ℝ)).toReal = 4 * q * Real.sqrt κ.toReal := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-! ## The games at a fixed table -/

section games

variable (W : OracleWorld)

/-- **A challenger answering by a fixed function**, without setup, outputting the bit. -/
noncomputable def fixExp {Dom Rng : Type} (g : Dom → Rng) :
    Experiment W (Dom →ₒ Rng) Unit Bool where
  State := Unit
  setup := pure ()
  pub _ := ()
  answer _ x := pure (g x)
  judge _ _ b := pure b

/-- Sequences of programs with equal runs have equal runs. -/
theorem run_iFreeM_bind_congr {spec : QuantumOracleSpec.{0, 0}} (Rt : QuantumRuntime spec)
    {Y Z : QReg → Type} {A : QReg} {x y : QuantumComp LocalSig.instruments.{0} spec Y A}
    {k₁ k₂ : ∀ u, Y u → QuantumComp LocalSig.instruments.{0} spec Z u}
    (h : Rt.run .instruments x = Rt.run .instruments y)
    (hk : ∀ u a, Rt.run .instruments (k₁ u a) = Rt.run .instruments (k₂ u a)) :
    Rt.run .instruments (IFreeM.bind x k₁) = Rt.run .instruments (IFreeM.bind y k₂) := by
  have e₁ := QuantumRuntime.run_bind Rt LocalSig.Interp.instruments x k₁
  have e₂ := QuantumRuntime.run_bind Rt LocalSig.Interp.instruments y k₂
  rw [h] at e₁
  exact e₁.trans ((congrArg _ (funext fun p ↦ hk p.1 p.2)).trans e₂.symm)

variable {W}

/-- A challenger's call tree runs at a fixed table as its sampler there. -/
theorem run₂_callTree_congr (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q}
    {ans₁ ans₂ : (q : Q) → OracleComp W.Oracles (R.Range q)}
    (h : ∀ q, simulateQ (W.eager tab) (ans₁ q) = simulateQ (W.eager tab) (ans₂ q))
    (q : Q) (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    (W.runtime tab).run₂ .instruments (callTree W ans₁ q E ℓ) =
      (W.runtime tab).run₂ .instruments (callTree W ans₂ q E ℓ) := by
  have h₁ := (classicalOn_act (R := W.runtime tab) (spec := W.spec)
    (B := QReg.of ((advSpec W.spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
      fun _ ↦ W.classicalOn_toQuantumAt tab _ (ans₁ q)
  have h₂ := (classicalOn_act (R := W.runtime tab) (spec := W.spec)
    (B := QReg.of ((advSpec W.spec R).Out (.call q) × E)) (SubInstrument.relabel ℓ)).bind
      fun _ ↦ W.classicalOn_toQuantumAt tab _ (ans₂ q)
  rw [h q] at h₁
  exact run₂_eq_of_classicalOn h₁ h₂

/-- The challenger's answer to a classical call runs at a fixed table as its sampler there. -/
theorem run_answerSub_call_congr (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q}
    {ans₁ ans₂ : (q : Q) → OracleComp W.Oracles (R.Range q)}
    (h : ∀ q, simulateQ (W.eager tab) (ans₁ q) = simulateQ (W.eager tab) (ans₂ q))
    (q : Q) (E : QReg) {A : QReg} (ℓ : A ≃ (advSpec W.spec R).In (.call q) × E) :
    (W.runtime tab).run .instruments (answerSub W ans₁ A (.query (.call q) E ℓ)) =
      (W.runtime tab).run .instruments (answerSub W ans₂ A (.query (.call q) E ℓ)) := by
  simp only [answerSub]
  exact run_iFreeM_bind_congr _ (run_eq_of_run₂_eq (run₂_callTree_congr tab h q E ℓ))
    fun _ _ ↦ rfl

/-- **A challenger's answers matter at a fixed table only through their samplers.** -/
theorem run_substitute_answerSub_congr (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q}
    {ans₁ ans₂ : (q : Q) → OracleComp W.Oracles (R.Range q)}
    (h : ∀ q, simulateQ (W.eager tab) (ans₁ q) = simulateQ (W.eager tab) (ans₂ q))
    {X : QReg → Type} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A) :
    (W.runtime tab).run .instruments (IFreeM.substitute (answerSub W ans₁) x) =
      (W.runtime tab).run .instruments (IFreeM.substitute (answerSub W ans₂) x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rw [IFreeM.substitute_liftBind, IFreeM.substitute_liftBind]
    refine run_iFreeM_bind_congr _ ?_ fun u a ↦ ?_
    · rcases c with o | ⟨p | q, E, ℓ⟩
      · rfl
      · rfl
      · exact run_answerSub_call_congr tab h q E ℓ
    · obtain ⟨b, e⟩ := a
      subst e
      exact ih b

theorem run₂_answered_congr (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q}
    {ans₁ ans₂ : (q : Q) → OracleComp W.Oracles (R.Range q)}
    (h : ∀ q, simulateQ (W.eager tab) (ans₁ q) = simulateQ (W.eager tab) (ans₂ q))
    {A B : QReg} {α : Type} (x : QComp (advSpec W.spec R) A B α) :
    (W.runtime tab).run₂ .instruments (answered W ans₁ x) =
      (W.runtime tab).run₂ .instruments (answered W ans₂ x) := by
  exact congrArg (fun d ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B α)
    (QuantumComp₂.leafEquiv B α).injective d)
      (run_substitute_answerSub_congr tab h (X := QuantumComp₂.Leaf B α) x)

/-- Under fair coins, the challenger's uniform sample weighs as the uniform average. -/
theorem tsum_sample_eq_uavg (hW : W.CoinsFair) (tab : W.Tab) {S : Type} [SampleableType S]
    [Fintype S] (G : S → ℝ≥0∞) :
    ∑' s : S, Pr{let z ← simulateQ (W.eager tab) (sample W S)}[z = s] * G s = uavg G := by
  rw [W.simulateQ_sample hW tab, tsum_fintype, uavg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [SampleableType.prEvent_uniformSample_eq_singleton]

theorem succAt_fixExp {Dom Rng : Type} (g : Dom → Rng) (tab : W.Tab)
    (B : Adversary W (Dom →ₒ Rng) Unit Bool) :
    (fixExp W g).succAt tab B = W.probAt tab ((answered W
      (fun x ↦ (pure (g x) : OracleComp W.Oracles Rng)) (withCallLog (B ()))).bind
        fun run ↦ QuantumComp₂.pure run.1) :=
  rfl

/-- **The real PRF game at a fixed table**: the average over the key of `fixExp` with the
answers of the keyed function at the table. -/
theorem succAt_prfReal (hW : W.CoinsFair) {Key Dom Rng : Type} [SampleableType Key]
    [Fintype Key] (F : Key → Dom → OracleComp W.Oracles Rng) (tab : W.Tab) (g : Key → Dom → Rng)
    (hg : ∀ K x, simulateQ (W.eager tab) (F K x) = pure (g K x))
    (B : Adversary W (Dom →ₒ Rng) Unit Bool) :
    (prfReal W F).succAt tab B = uavg fun K ↦ (fixExp W (g K)).succAt tab B := by
  refine (probAt_bind_classicalOn W tab (W.classicalOn_toQuantumAt tab _ _) _).trans
    ((tsum_sample_eq_uavg hW tab (S := Key) _).trans (congrArg uavg (funext fun K ↦ ?_)))
  rw [succAt_fixExp]
  refine probAt_eq_of_run₂ W tab ?_
  change (W.runtime tab).run₂ .instruments ((answered W (F K) (withCallLog (B ()))).bind
    fun run ↦ QuantumComp₂.pure run.1) = _
  rw [QuantumRuntime.run₂_bind, QuantumRuntime.run₂_bind,
    run₂_answered_congr tab fun x ↦ (hg K x).trans (simulateQ_pure _ _).symm]

/-- **The ideal PRF game at a fixed table**: the average over the function of `fixExp`. -/
theorem succAt_prfIdeal (hW : W.CoinsFair) {Dom U Rng : Type} [Fintype Dom] [DecidableEq Dom]
    [SampleableType U] [Fintype U] (post : Dom → U → Rng) (tab : W.Tab)
    (B : Adversary W (Dom →ₒ Rng) Unit Bool) :
    (prfIdeal W post).succAt tab B =
      uavg fun f : Dom → U ↦ (fixExp W fun x ↦ post x (f x)).succAt tab B := by
  exact (probAt_bind_classicalOn W tab (W.classicalOn_toQuantumAt tab _ _) _).trans
    (tsum_sample_eq_uavg hW tab (S := Dom → U) _)

/-- **The game of a fixed challenger makes the adversary's hash calls only.** -/
theorem isTotalQueryBound_fixExp_game {Dom Rng : Type} (g : Dom → Rng)
    (B : Adversary W (Dom →ₒ Rng) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    ((fixExp W g).game B).IsTotalQueryBound q := by
  have hA : IFreeM.IsChargeBound (answered W (fun x ↦ (pure (g x) : OracleComp W.Oracles Rng))
      (withCallLog (B ()))) (fun _ c ↦ QuantumComp.Cmd.queryCharge c) q := by
    refine IFreeM.IsChargeBound.substitute _ (fun A c ↦ ?_) (isChargeBound_withCallLog (hB ()))
    rcases c with o | ⟨p | x, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).2 ⟨le_rfl, fun _ ↦ trivial⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).2 ⟨le_rfl, fun _ ↦ trivial⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).2 ⟨le_rfl, fun _ ↦ trivial⟩
  have h0 : IFreeM.IsChargeBound ((pure () : OracleComp W.Oracles Unit).toQuantumAt
      (W.impl (QReg.of Unit))) (fun _ c ↦ QuantumComp.Cmd.queryCharge c) 0 :=
    IFreeM.isChargeBound_pure _ _
  have hk : ∀ run : Bool × QueryLog (Dom →ₒ Rng), IFreeM.IsChargeBound
      (QuantumComp₂.pure run.1 : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool)
      (fun _ c ↦ QuantumComp.Cmd.queryCharge c) 0 := fun _ ↦ IFreeM.isChargeBound_pure _ _
  have h := FreeM₂.isChargeBound_bind h0 fun _ ↦ FreeM₂.isChargeBound_bind hA hk
  rw [zero_add, add_zero] at h
  exact h

/-- The key-in-the-middle function at a fixed table. -/
theorem simulateQ_kimFn {Key Dom Rng : Type} (tab : W.Tab) (fmt : Dom → HashInput × HashInput)
    (keyBytes : Key → HashInput) (trunc : Dom → HashOutput → Rng) (K : Key) (x : Dom) :
    simulateQ (W.eager tab) (kimFn W fmt keyBytes trunc K x) =
      pure (trunc x (W.hashOf tab ((fmt x).1 ++ keyBytes K ++ (fmt x).2))) := by
  simp only [kimFn, simulateQ_map, W.simulateQ_hash, map_pure]

/-- The derived-key function at a fixed table. -/
theorem simulateQ_derivedKimFn {Seed Dom Rng : Type} (tab : W.Tab) (pre : HashInput)
    (seedBytes : Seed → HashInput) (keyBytes : HashOutput → HashInput)
    (fmt : Dom → HashInput × HashInput) (trunc : Dom → HashOutput → Rng) (S0 : Seed) (x : Dom) :
    simulateQ (W.eager tab) (derivedKimFn W pre seedBytes keyBytes fmt trunc S0 x) =
      pure (trunc x (W.hashOf tab ((fmt x).1 ++ keyBytes (W.hashOf tab (pre ++ seedBytes S0)) ++
        (fmt x).2))) := by
  simp only [derivedKimFn, simulateQ_bind, W.simulateQ_hash, pure_bind, simulateQ_kimFn]

end games

/-! ## Cells of the QROM world -/

section cells

/-- The cell of a byte string (`0` for strings too long to be hashed). -/
noncomputable def cellOf (l : HashInput) : HashDomain :=
  (encodeInput l).getD 0

theorem encodeInput_eq_cellOf {l : HashInput} (h : l.length ≤ maxLen) :
    encodeInput l = some (cellOf l) := by
  rw [cellOf, encodeInput_of_length_le h]
  rfl

theorem romWorld_hashOf (H : romWorld.Tab) {l : HashInput} (h : l.length ≤ maxLen) :
    romWorld.hashOf H l = H (cellOf l) := by
  change (encodeInput l).elim 0 H = H (cellOf l)
  rw [encodeInput_eq_cellOf h]
  rfl

theorem decodeInput_cellOf {l : HashInput} (h : l.length ≤ maxLen) : decodeInput (cellOf l) = l :=
  decodeInput_of_encodeInput_eq_some (encodeInput_eq_cellOf h)

theorem cellOf_inj {l l' : HashInput} (h : l.length ≤ maxLen) (h' : l'.length ≤ maxLen)
    (e : cellOf l = cellOf l') : l = l' := by
  rw [← decodeInput_cellOf h, e, decodeInput_cellOf h']

end cells

/-! ## The key-in-the-middle PRF -/

section kim

variable {Key Dom Rng : Type}

/-- The keyed input of the format `x` under the key `K`. -/
def kimInput (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput) (K : Key)
    (x : Dom) : HashInput :=
  (fmt x).1 ++ keyBytes K ++ (fmt x).2

/-- **Distinct keyed cells**: under every key, distinct formats hash distinct inputs. It implies
`KimFmtInjective` and is what the reprogramming of the keyed cells needs. -/
def KimCellInjective (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput) : Prop :=
  ∀ K, Function.Injective (kimInput fmt keyBytes K)

/-- With keys of one length, injective formats whose prefixes or total lengths differ have
distinct keyed cells. -/
theorem kimCellInjective_of {fmt : Dom → HashInput × HashInput} {keyBytes : Key → HashInput}
    (hfmt : Function.Injective fmt) {n : ℕ} (hn : ∀ K, (keyBytes K).length = n)
    (hlen : ∀ x y, (fmt x).1.length = (fmt y).1.length ∨
      (fmt x).1.length + (fmt x).2.length ≠ (fmt y).1.length + (fmt y).2.length) :
    KimCellInjective fmt keyBytes := by
  intro K x y h
  unfold kimInput at h
  rcases hlen x y with hl | hl
  · rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨ha, hb⟩ := List.append_inj h hl
    exact hfmt (Prod.ext ha (List.append_cancel_left hb))
  · exact absurd (by simpa [hn, Nat.add_comm, Nat.add_left_comm] using congrArg List.length h) hl

/-- **Keys of one length**: the keys making `l` a keyed input number at most the prefix
lengths. -/
theorem card_filter_kimInput_le [Fintype Key] [Fintype Dom] (fmt : Dom → HashInput × HashInput)
    (keyBytes : Key → HashInput) (hkey : Function.Injective keyBytes) {n : ℕ}
    (hn : ∀ K, (keyBytes K).length = n) (l : HashInput) :
    (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤
      (Finset.univ.image fun x ↦ (fmt x).1.length).card := by
  classical
  let f : Key → ℕ := fun K ↦
    @dite _ (∃ x, kimInput fmt keyBytes K x = l) (Classical.propDecidable _)
      (fun h ↦ (fmt h.choose).1.length) fun _ ↦ 0
  refine Finset.card_le_card_of_injOn f (fun K hK ↦ ?_) fun K hK K' hK' he ↦ ?_
  · have hK : ∃ x, kimInput fmt keyBytes K x = l := (Finset.mem_filter.1 hK).2
    simp only [f, dite_eq_left hK]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · have hK : ∃ x, kimInput fmt keyBytes K x = l := (Finset.mem_filter.1 hK).2
    have hK' : ∃ x, kimInput fmt keyBytes K' x = l := (Finset.mem_filter.1 hK').2
    simp only [f, dite_eq_left hK, dite_eq_left hK'] at he
    have key : ∀ (K : Key) (y : Dom), kimInput fmt keyBytes K y = l →
        keyBytes K = (l.drop (fmt y).1.length).take n := fun K y hy ↦ by
      rw [← hy, kimInput, List.append_assoc, List.drop_left, ← hn K, List.take_left]
    exact hkey ((key K _ hK.choose_spec).trans (he ▸ (key K' _ hK'.choose_spec).symm))

/-- The keyed cells of `K` as a lazy table without dependencies. -/
noncomputable def kimTable (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput)
    (hlen : KimLengthLe fmt keyBytes maxLen) (hinj : KimCellInjective fmt keyBytes) (K : Key) :
    LazyTable Dom HashDomain HashOutput where
  cell x _ := cellOf (kimInput fmt keyBytes K x)
  pre _ _ := False
  wf := ⟨fun a ↦ ⟨a, fun _ h ↦ h.elim⟩⟩
  dep _ _ _ _ := rfl
  inj _ _ _ h := hinj K (cellOf_inj (hlen _ K) (hlen _ K) h)

/-- Few keys make a cell keyed. -/
theorem sum_indicator_kim_le [Fintype Key] [Fintype Dom] (fmt : Dom → HashInput × HashInput)
    (keyBytes : Key → HashInput) (hlen : KimLengthLe fmt keyBytes maxLen) {N : ℕ}
    (hN : ∀ l : HashInput, (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤ N)
    (z : HashDomain) :
    ∑ K, (Set.range fun x ↦ cellOf (kimInput fmt keyBytes K x)).indicator
      (1 : HashDomain → ℝ≥0∞) z ≤ N := by
  classical
  calc ∑ K, (Set.range fun x ↦ cellOf (kimInput fmt keyBytes K x)).indicator
        (1 : HashDomain → ℝ≥0∞) z
      ≤ ∑ K, if ∃ x, kimInput fmt keyBytes K x = decodeInput z then (1 : ℝ≥0∞) else 0 :=
        Finset.sum_le_sum fun K _ ↦ by
          by_cases h : ∃ x, cellOf (kimInput fmt keyBytes K x) = z
          · obtain ⟨x, hx⟩ := h
            have hm : ∃ x, kimInput fmt keyBytes K x = decodeInput z :=
              ⟨x, by rw [← hx, decodeInput_cellOf (l := kimInput fmt keyBytes K x) (hlen x K)]⟩
            simp only [hm, ↓reduceIte]
            unfold Set.indicator
            split <;> simp
          · rw [Set.indicator_of_notMem (by simpa using h)]
            exact zero_le
    _ = ((Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = decodeInput z).card :
          ℝ≥0∞) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_one]
    _ ≤ N := Nat.cast_le.2 (hN _)

end kim

/-! ## The bounds -/

open Common (QueryCostAtMost)

section main

variable {Key Dom Rng : Type}

/-- **The advantage from the two squared hybrids**: averaged over the table, the signed
advantage is at most `2 d` in absolute value. -/
theorem abs_avg_prfAdv_le_of_hybrid [SampleableType Key] [Fintype Dom]
    (F : Key → Dom → OracleComp romWorld.Oracles Rng) (post : Dom → HashOutput → Rng)
    (B : Adversary romWorld (Dom →ₒ Rng) Unit Bool) {d : ℝ≥0∞} (hd : d ≠ ⊤)
    (h₁ : (uavg fun H : HashDomain → HashOutput ↦ (prfReal romWorld F).succAt H B) ≤
      ((uavg fun H : HashDomain → HashOutput ↦ (prfIdeal romWorld post).succAt H B) ^ (2⁻¹ : ℝ) +
        d) ^ 2)
    (h₂ : (uavg fun H : HashDomain → HashOutput ↦ (prfIdeal romWorld post).succAt H B) ≤
      ((uavg fun H : HashDomain → HashOutput ↦ (prfReal romWorld F).succAt H B) ^ (2⁻¹ : ℝ) +
        d) ^ 2) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * prfAdv romWorld F post H B| ≤ 2 * d.toReal := by
  have hr : ∀ H : HashDomain → HashOutput, (prfReal romWorld F).succAt H B ≤ 1 := fun _ ↦
    QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _
  have hi : ∀ H : HashDomain → HashOutput, (prfIdeal romWorld post).succAt H B ≤ 1 := fun _ ↦
    QuantumRuntime.outcomeLawWith_le_one _ _ _ _ _ _
  refine Eq.trans_le ?_ (abs_toReal_sub_le_of_hybrid (uavg_le_one hr) (uavg_le_one hi) hd h₁ h₂)
  rw [toReal_uavg fun H ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hr H),
    toReal_uavg fun H ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hi H), ← Finset.sum_sub_distrib]
  refine congrArg abs (Finset.sum_congr rfl fun H _ ↦ ?_)
  rw [← mul_sub]
  rfl

theorem natCast_div_ne_top {N : ℕ} [Fintype Key] [Nonempty Key] :
    (N : ℝ≥0∞) / Fintype.card Key ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem hyb_ne_top (q : ℕ) {κ : ℝ≥0∞} (hκ : κ ≠ ⊤) : (q : ℝ≥0∞) * (4 * κ) ^ (2⁻¹ : ℝ) ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (by norm_num) hκ))

/-- **KIM-PRF in the QROM** (D1): for any adversary with at most `q` hash calls, the signed
advantage averaged over the table is at most `4 q √(N / |Key|)` in absolute value, `N` bounding
the keys that make a given string a keyed input. -/
theorem abs_avg_kimPrfAdv_le [SampleableType Key] [Fintype Key] [Nonempty Key] [Fintype Dom]
    (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput)
    (trunc : Dom → HashOutput → Rng) (hlen : KimLengthLe fmt keyBytes maxLen)
    (hinj : KimCellInjective fmt keyBytes) {N : ℕ}
    (hN : ∀ l : HashInput,
      (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤ N)
    (B : Adversary romWorld (Dom →ₒ Rng) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * kimPrfAdv romWorld fmt keyBytes trunc H B| ≤
      4 * q * Real.sqrt (N / Fintype.card Key) := by
  classical
  set prog : (Dom → HashOutput) → QComp (qromSpec HashDomain HashOutput) (QReg.of Unit)
    (QReg.of Unit) Bool := fun v ↦ (fixExp romWorld fun x ↦ trunc x (v x)).game B with hprog
  set T : Key → LazyTable Dom HashDomain HashOutput := kimTable fmt keyBytes hlen hinj with hT
  set κ : ℝ≥0∞ := (N : ℝ≥0∞) / Fintype.card Key with hκ
  have hcK : (Fintype.card Key : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hreal : ∀ H : HashDomain → HashOutput,
      (prfReal romWorld (kimFn romWorld fmt keyBytes trunc)).succAt H B =
        uavg fun K ↦ tabProb H (prog ((T K).tab H)) := fun H ↦ by
    rw [succAt_prfReal romWorld_coinsFair _ H _
      fun K x ↦ simulateQ_kimFn (W := romWorld) H fmt keyBytes trunc K x]
    refine congrArg uavg (funext fun K ↦ ?_)
    have e : (fun x ↦ trunc x (romWorld.hashOf H ((fmt x).1 ++ keyBytes K ++ (fmt x).2))) =
        fun x ↦ trunc x ((T K).tab H x) := funext fun x ↦ by
      rw [romWorld_hashOf H (hlen x K), LazyTable.tab_eq]
      rfl
    exact congrArg (fun g : Dom → Rng ↦ tabProb H ((fixExp romWorld g).game B)) e
  have hideal : ∀ H : HashDomain → HashOutput, (prfIdeal romWorld trunc).succAt H B =
      uavg fun f ↦ tabProb H (prog f) := fun H ↦
    succAt_prfIdeal romWorld_coinsFair trunc H B
  have ha : (uavg fun H : HashDomain → HashOutput ↦
      (prfReal romWorld (kimFn romWorld fmt keyBytes trunc)).succAt H B) =
      uavg fun p : Key × ((Dom → HashOutput) × (HashDomain → HashOutput)) ↦
        tabProb ((T p.1).fill p.2.1 p.2.1 p.2.2) (prog p.2.1) := by
    simp only [hreal]
    rw [uavg_comm, uavg_prod]
    refine congrArg uavg (funext fun K ↦ ?_)
    exact (uavg_tab_eq_fill (T K) fun v H ↦ tabProb H (prog v)).trans (uavg_prod
      (fun p : (Dom → HashOutput) × (HashDomain → HashOutput) ↦
        tabProb ((T K).fill p.1 p.1 p.2) (prog p.1))).symm
  have hb : (uavg fun H : HashDomain → HashOutput ↦ (prfIdeal romWorld trunc).succAt H B) =
      uavg fun ψ : (Dom → HashOutput) × (HashDomain → HashOutput) ↦ tabProb ψ.2 (prog ψ.1) := by
    simp only [hideal]
    rw [uavg_comm]
    exact (uavg_prod (fun ψ : (Dom → HashOutput) × (HashDomain → HashOutput) ↦
      tabProb ψ.2 (prog ψ.1))).symm
  obtain ⟨h₁, h₂⟩ := uavg_hybrid_tables (Θ := Key)
    (Ψ := (Dom → HashOutput) × (HashDomain → HashOutput)) (fun ψ ↦ ψ.2)
    (fun K ψ ↦ (T K).fill ψ.1 ψ.1 ψ.2)
    (fun K _ ↦ Set.range fun x ↦ cellOf (kimInput fmt keyBytes K x))
    (fun K ψ z hz ↦ ((T K).fill_of_forall_ne fun s hs ↦ hz ⟨s, hs⟩).symm) (fun ψ ↦ prog ψ.1)
    (fun ψ ↦ isTotalQueryBound_fixExp_game _ B hB) κ
    (fun ψ z ↦ (sum_indicator_kim_le fmt keyBytes hlen hN z).trans
      (le_of_eq (ENNReal.div_mul_cancel hcK (ENNReal.natCast_ne_top _)).symm))
  have hd := hyb_ne_top q (natCast_div_ne_top (Key := Key) (N := N))
  refine (abs_avg_prfAdv_le_of_hybrid _ _ B hd (by rw [ha, hb]; exact h₁)
    (by rw [ha, hb]; exact h₂)).trans_eq ?_
  rw [two_mul_toReal_hyb, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- The cells of a derived key: the derivation cell, then the keyed cells of its value. -/
noncomputable def derivedTable {Seed : Type} (pre : HashInput) (seedBytes : Seed → HashInput)
    (fmt : Dom → HashInput × HashInput) (keyBytes : HashOutput → HashInput)
    (hlen : KimLengthLe fmt keyBytes maxLen) (hlen0 : ∀ S0, (pre ++ seedBytes S0).length ≤ maxLen)
    (hinj : KimCellInjective fmt keyBytes)
    (hsep : ∀ S0 S x, pre ++ seedBytes S0 ≠ kimInput fmt keyBytes S x) (S0 : Seed) :
    LazyTable (Option Dom) HashDomain HashOutput where
  cell o v := o.elim (cellOf (pre ++ seedBytes S0)) fun x ↦
    cellOf (kimInput fmt keyBytes (v none) x)
  pre a b := a = none ∧ b ≠ none
  wf := ⟨fun a ↦ ⟨a, fun b hb ↦ ⟨b, fun _ hc ↦ (hc.2 hb.1).elim⟩⟩⟩
  dep s v v' h := by
    cases s with
    | none => rfl
    | some x =>
      change cellOf (kimInput fmt keyBytes (v none) x) = cellOf (kimInput fmt keyBytes (v' none) x)
      rw [h none ⟨rfl, Option.some_ne_none x⟩]
  inj v a b h := by
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some y => exact (hsep S0 (v none) y (cellOf_inj (hlen0 S0) (hlen y _) h)).elim
    | some x =>
      cases b with
      | none => exact (hsep S0 (v none) x (cellOf_inj (hlen0 S0) (hlen x _) h.symm)).elim
      | some y => exact congrArg some (hinj (v none) (cellOf_inj (hlen x _) (hlen y _) h))

/-- **Derived-key KIM-PRF in the QROM** (D1, leanXMSS): the seed `S0` hidden behind
`S = H(pre ‖ S0)`; for any adversary with at most `q` hash calls, the signed advantage averaged
over the table is at most `4 q √(1 / |Seed| + N / |HashOutput|)` in absolute value. -/
theorem abs_avg_derivedKimPrfAdv_le {Seed : Type} [SampleableType Seed] [Fintype Seed]
    [Nonempty Seed] [Fintype Dom] (pre : HashInput) (seedBytes : Seed → HashInput)
    (keyBytes : HashOutput → HashInput) (fmt : Dom → HashInput × HashInput)
    (trunc : Dom → HashOutput → Rng) (hlen : KimLengthLe fmt keyBytes maxLen)
    (hlen0 : ∀ S0, (pre ++ seedBytes S0).length ≤ maxLen) (hinj : KimCellInjective fmt keyBytes)
    (hseed : Function.Injective seedBytes)
    (hsep : ∀ S0 S x, pre ++ seedBytes S0 ≠ kimInput fmt keyBytes S x) {N : ℕ}
    (hN : ∀ l : HashInput,
      (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤ N)
    (B : Adversary romWorld (Dom →ₒ Rng) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ *
        derivedKimPrfAdv romWorld pre seedBytes keyBytes fmt trunc H B| ≤
      4 * q * Real.sqrt ((Fintype.card Seed : ℝ)⁻¹ + N / Fintype.card HashOutput) := by
  classical
  set prog : (Dom → HashOutput) → QComp (qromSpec HashDomain HashOutput) (QReg.of Unit)
    (QReg.of Unit) Bool := fun v ↦ (fixExp romWorld fun x ↦ trunc x (v x)).game B with hprog
  set T : Seed → LazyTable (Option Dom) HashDomain HashOutput :=
    derivedTable pre seedBytes fmt keyBytes hlen hlen0 hinj hsep with hT
  set e : (Option Dom → HashOutput) ≃ HashOutput × (Dom → HashOutput) :=
    Equiv.piOptionEquivProd (β := fun _ ↦ HashOutput) with he
  set κ : ℝ≥0∞ := (Fintype.card Seed : ℝ≥0∞)⁻¹ + N / Fintype.card HashOutput with hκ
  have hcs : (Fintype.card Seed : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcy : (Fintype.card HashOutput : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hreal : ∀ H : HashDomain → HashOutput,
      (prfReal romWorld (derivedKimFn romWorld pre seedBytes keyBytes fmt trunc)).succAt H B =
        uavg fun S0 ↦ tabProb H (prog fun x ↦ (T S0).tab H (some x)) := fun H ↦ by
    rw [succAt_prfReal romWorld_coinsFair _ H _ fun S0 x ↦
      simulateQ_derivedKimFn (W := romWorld) H pre seedBytes keyBytes fmt trunc S0 x]
    refine congrArg uavg (funext fun S0 ↦ ?_)
    have h0 : (T S0).tab H none = H (cellOf (pre ++ seedBytes S0)) := (T S0).tab_eq H none
    have e' : (fun x ↦ trunc x (romWorld.hashOf H ((fmt x).1 ++
        keyBytes (romWorld.hashOf H (pre ++ seedBytes S0)) ++ (fmt x).2))) =
        fun x ↦ trunc x ((T S0).tab H (some x)) := funext fun x ↦ by
      rw [(T S0).tab_eq H (some x)]
      change _ = trunc x (H (cellOf (kimInput fmt keyBytes ((T S0).tab H none) x)))
      rw [h0, romWorld_hashOf H (hlen0 S0), romWorld_hashOf H (hlen x _)]
      rfl
    exact congrArg (fun g : Dom → Rng ↦ tabProb H ((fixExp romWorld g).game B)) e'
  have hideal : ∀ H : HashDomain → HashOutput, (prfIdeal romWorld trunc).succAt H B =
      uavg fun f ↦ tabProb H (prog f) := fun H ↦
    succAt_prfIdeal romWorld_coinsFair trunc H B
  have ha : (uavg fun H : HashDomain → HashOutput ↦
      (prfReal romWorld (derivedKimFn romWorld pre seedBytes keyBytes fmt trunc)).succAt H B) =
      uavg fun p : (Seed × HashOutput) × ((Dom → HashOutput) × (HashDomain → HashOutput)) ↦
        tabProb ((T p.1.1).fill (e.symm (p.1.2, p.2.1)) (e.symm (p.1.2, p.2.1)) p.2.2)
          (prog p.2.1) := by
    simp only [hreal]
    rw [uavg_comm, uavg_prod, uavg_prod]
    refine congrArg uavg (funext fun S0 ↦ ?_)
    refine (uavg_tab_eq_fill (T S0) fun v H ↦ tabProb H (prog fun x ↦ v (some x))).trans ?_
    refine (uavg_equiv e.symm (fun v ↦ uavg fun H ↦
      tabProb ((T S0).fill v v H) (prog fun x ↦ v (some x)))).symm.trans ?_
    rw [uavg_prod]
    refine congrArg uavg (funext fun S ↦ ?_)
    exact (uavg_prod (fun p : (Dom → HashOutput) × (HashDomain → HashOutput) ↦
      tabProb ((T S0).fill (e.symm (S, p.1)) (e.symm (S, p.1)) p.2) (prog p.1))).symm
  have hb : (uavg fun H : HashDomain → HashOutput ↦ (prfIdeal romWorld trunc).succAt H B) =
      uavg fun ψ : (Dom → HashOutput) × (HashDomain → HashOutput) ↦ tabProb ψ.2 (prog ψ.1) := by
    simp only [hideal]
    rw [uavg_comm]
    exact (uavg_prod (fun ψ : (Dom → HashOutput) × (HashDomain → HashOutput) ↦
      tabProb ψ.2 (prog ψ.1))).symm
  have hs1 : ∀ z, ∑ S0 : Seed, ({cellOf (pre ++ seedBytes S0)} : Set HashDomain).indicator
      (1 : HashDomain → ℝ≥0∞) z ≤ 1 := fun z ↦ by
    have hc : ∀ S0 ∈ (Finset.univ : Finset Seed),
        ({cellOf (pre ++ seedBytes S0)} : Set HashDomain).indicator (1 : HashDomain → ℝ≥0∞) z =
          if z = cellOf (pre ++ seedBytes S0) then 1 else 0 := fun S0 _ ↦ by
      by_cases h : z = cellOf (pre ++ seedBytes S0) <;> simp [Set.indicator, h]
    rw [Finset.sum_congr rfl hc, Finset.sum_boole]
    have hle : (Finset.univ.filter fun S0 : Seed ↦ z = cellOf (pre ++ seedBytes S0)).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb ↦ by
        have ha' : z = cellOf (pre ++ seedBytes a) := (Finset.mem_filter.1 ha).2
        have hb' : z = cellOf (pre ++ seedBytes b) := (Finset.mem_filter.1 hb).2
        exact hseed (List.append_cancel_left (cellOf_inj (hlen0 a) (hlen0 b) (ha'.symm.trans hb')))
    exact_mod_cast hle
  have hκ' : κ * Fintype.card (Seed × HashOutput) =
      Fintype.card HashOutput + Fintype.card Seed * N := by
    rw [hκ, Fintype.card_prod, Nat.cast_mul, add_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hcs (ENNReal.natCast_ne_top _), one_mul,
      mul_comm (Fintype.card Seed : ℝ≥0∞), ← mul_assoc,
      ENNReal.div_mul_cancel hcy (ENNReal.natCast_ne_top _), mul_comm (N : ℝ≥0∞)]
  obtain ⟨h₁, h₂⟩ := uavg_hybrid_tables (Θ := Seed × HashOutput)
    (Ψ := (Dom → HashOutput) × (HashDomain → HashOutput)) (fun ψ ↦ ψ.2)
    (fun θ ψ ↦ (T θ.1).fill (e.symm (θ.2, ψ.1)) (e.symm (θ.2, ψ.1)) ψ.2)
    (fun θ _ ↦ ({cellOf (pre ++ seedBytes θ.1)} : Set HashDomain) ∪
      Set.range fun x ↦ cellOf (kimInput fmt keyBytes θ.2 x))
    (fun θ ψ z hz ↦ ((T θ.1).fill_of_forall_ne fun s hs ↦ hz (by
      cases s with
      | none => exact Or.inl (Set.mem_singleton_iff.2 hs.symm)
      | some x => exact Or.inr ⟨x, hs⟩)).symm)
    (fun ψ ↦ prog ψ.1) (fun ψ ↦ isTotalQueryBound_fixExp_game _ B hB) κ (fun ψ z ↦ by
      calc ∑ θ : Seed × HashOutput, (({cellOf (pre ++ seedBytes θ.1)} : Set HashDomain) ∪
            Set.range fun x ↦ cellOf (kimInput fmt keyBytes θ.2 x)).indicator
              (1 : HashDomain → ℝ≥0∞) z
          ≤ ∑ θ : Seed × HashOutput,
              (({cellOf (pre ++ seedBytes θ.1)} : Set HashDomain).indicator
                (1 : HashDomain → ℝ≥0∞) z +
              (Set.range fun x ↦ cellOf (kimInput fmt keyBytes θ.2 x)).indicator
                (1 : HashDomain → ℝ≥0∞) z) := Finset.sum_le_sum fun θ _ ↦ by
            unfold Set.indicator
            split_ifs <;> simp_all
        _ ≤ Fintype.card HashOutput * 1 + Fintype.card Seed * N := by
            rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
            gcongr
            · exact hs1 z
            · exact sum_indicator_kim_le fmt keyBytes hlen hN z
        _ = κ * Fintype.card (Seed × HashOutput) := by rw [hκ', mul_one])
  have hκt : κ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hcs,
    natCast_div_ne_top (Key := HashOutput) (N := N)⟩
  refine (abs_avg_prfAdv_le_of_hybrid _ _ B (hyb_ne_top q hκt) (by rw [ha, hb]; exact h₁)
    (by rw [ha, hb]; exact h₂)).trans_eq ?_
  rw [two_mul_toReal_hyb, hκ, ENNReal.toReal_add (ENNReal.inv_ne_top.2 hcs)
    (natCast_div_ne_top (Key := HashOutput) (N := N)), ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

/-- **PRF_msg in the QROM** (D2): for injective keys of one length and injective suffixes, the
signed advantage of any adversary with at most `q` hash calls, averaged over the table, is at
most `4 q √(1 / |Key|)` in absolute value. -/
theorem abs_avg_prfMsgAdv_le [SampleableType Key] [Fintype Key] [Nonempty Key] [Fintype Dom]
    (bytes : Dom → HashInput) (keyBytes : Key → HashInput) (trunc : HashOutput → Rng)
    (hlen : KimLengthLe (fun x ↦ (([] : HashInput), bytes x)) keyBytes maxLen)
    (hbytes : Function.Injective bytes) (hkey : Function.Injective keyBytes) {n : ℕ}
    (hn : ∀ K, (keyBytes K).length = n) (B : Adversary romWorld (Dom →ₒ Rng) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * prfMsgAdv romWorld bytes keyBytes trunc H B| ≤
      4 * q * Real.sqrt (1 / Fintype.card Key) := by
  classical
  have hinj : KimCellInjective (fun x ↦ (([] : HashInput), bytes x)) keyBytes := fun K x y h ↦
    hbytes (List.append_cancel_left
      (show ([] ++ keyBytes K) ++ bytes x = ([] ++ keyBytes K) ++ bytes y from h))
  have hN : ∀ l : HashInput, (Finset.univ.filter fun K ↦
      ∃ x, kimInput (fun x ↦ (([] : HashInput), bytes x)) keyBytes K x = l).card ≤ 1 := fun l ↦
    (card_filter_kimInput_le _ keyBytes hkey hn l).trans (Finset.card_le_one.2 fun a ha b hb ↦ by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, List.length_nil] at ha hb
      obtain ⟨_, rfl⟩ := ha
      obtain ⟨_, rfl⟩ := hb
      rfl)
  have h := abs_avg_kimPrfAdv_le (fun x ↦ (([] : HashInput), bytes x)) keyBytes (fun _ ↦ trunc)
    hlen hinj hN B hB
  rw [Nat.cast_one] at h
  exact h

/-! ### Straight-line reductions -/

variable {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}

/-- **KIM-PRF against a straight-line reduction**: the adversary part's hash calls `n` and the
reduction's honest hash calls (`c₀`, `k` per classical call, `c₁`) are charged alike. -/
theorem abs_avg_kimPrfAdv_slRed_le [SampleableType Key] [Fintype Key] [Nonempty Key]
    [Fintype Dom] (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput)
    (trunc : Dom → HashOutput → Rng) (hlen : KimLengthLe fmt keyBytes maxLen)
    (hinj : KimCellInjective fmt keyBytes) {N : ℕ}
    (hN : ∀ l : HashInput,
      (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤ N)
    (pre : OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (Dom →ₒ Rng) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) Bool)
    {c₀ c₁ k n m : ℕ} (hpre : QueryCostAtMost pre (hcallCost romWorld (R' := Dom →ₒ Rng)) c₀)
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (hcallCost romWorld (R' := Dom →ₒ Rng)) k)
    (hpost : ∀ a f s, QueryCostAtMost (post a f s) (hcallCost romWorld (R' := Dom →ₒ Rng)) c₁)
    (hn : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge hashCharge) n)
    (hm : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge callCharge) m) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * kimPrfAdv romWorld fmt keyBytes trunc H
        (fun _ ↦ slRed romWorld pre adv st0 σ post)| ≤
      4 * ((c₀ + ((n + k * m) + c₁) : ℕ) : ℝ) * Real.sqrt (N / Fintype.card Key) :=
  abs_avg_kimPrfAdv_le fmt keyBytes trunc hlen hinj hN _ fun _ ↦
    isChargeBound_slRed_hash romWorld pre adv st0 σ post hpre hσ hpost hn hm

/-- **Derived-key KIM-PRF against a straight-line reduction.** -/
theorem abs_avg_derivedKimPrfAdv_slRed_le {Seed : Type} [SampleableType Seed] [Fintype Seed]
    [Nonempty Seed] [Fintype Dom] (pre₀ : HashInput) (seedBytes : Seed → HashInput)
    (keyBytes : HashOutput → HashInput) (fmt : Dom → HashInput × HashInput)
    (trunc : Dom → HashOutput → Rng) (hlen : KimLengthLe fmt keyBytes maxLen)
    (hlen0 : ∀ S0, (pre₀ ++ seedBytes S0).length ≤ maxLen) (hinj : KimCellInjective fmt keyBytes)
    (hseed : Function.Injective seedBytes)
    (hsep : ∀ S0 S x, pre₀ ++ seedBytes S0 ≠ kimInput fmt keyBytes S x) {N : ℕ}
    (hN : ∀ l : HashInput,
      (Finset.univ.filter fun K ↦ ∃ x, kimInput fmt keyBytes K x = l).card ≤ N)
    (pre : OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (Dom →ₒ Rng) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) Bool)
    {c₀ c₁ k n m : ℕ} (hpre : QueryCostAtMost pre (hcallCost romWorld (R' := Dom →ₒ Rng)) c₀)
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (hcallCost romWorld (R' := Dom →ₒ Rng)) k)
    (hpost : ∀ a f s, QueryCostAtMost (post a f s) (hcallCost romWorld (R' := Dom →ₒ Rng)) c₁)
    (hn : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge hashCharge) n)
    (hm : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge callCharge) m) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ *
        derivedKimPrfAdv romWorld pre₀ seedBytes keyBytes fmt trunc H
          (fun _ ↦ slRed romWorld pre adv st0 σ post)| ≤
      4 * ((c₀ + ((n + k * m) + c₁) : ℕ) : ℝ) *
        Real.sqrt ((Fintype.card Seed : ℝ)⁻¹ + N / Fintype.card HashOutput) :=
  abs_avg_derivedKimPrfAdv_le pre₀ seedBytes keyBytes fmt trunc hlen hlen0 hinj hseed hsep hN _
    fun _ ↦ isChargeBound_slRed_hash romWorld pre adv st0 σ post hpre hσ hpost hn hm

/-- **PRF_msg against a straight-line reduction.** -/
theorem abs_avg_prfMsgAdv_slRed_le [SampleableType Key] [Fintype Key] [Nonempty Key]
    [Fintype Dom] (bytes : Dom → HashInput) (keyBytes : Key → HashInput)
    (trunc : HashOutput → Rng)
    (hlen : KimLengthLe (fun x ↦ (([] : HashInput), bytes x)) keyBytes maxLen)
    (hbytes : Function.Injective bytes) (hkey : Function.Injective keyBytes) {nk : ℕ}
    (hnk : ∀ K, (keyBytes K).length = nk)
    (pre : OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (Dom →ₒ Rng) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + (Dom →ₒ Rng)) Bool)
    {c₀ c₁ k n m : ℕ} (hpre : QueryCostAtMost pre (hcallCost romWorld (R' := Dom →ₒ Rng)) c₀)
    (hσ : ∀ s q, QueryCostAtMost (σ s q) (hcallCost romWorld (R' := Dom →ₒ Rng)) k)
    (hpost : ∀ a f s, QueryCostAtMost (post a f s) (hcallCost romWorld (R' := Dom →ₒ Rng)) c₁)
    (hn : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge hashCharge) n)
    (hm : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge callCharge) m) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * prfMsgAdv romWorld bytes keyBytes trunc H
        (fun _ ↦ slRed romWorld pre adv st0 σ post)| ≤
      4 * ((c₀ + ((n + k * m) + c₁) : ℕ) : ℝ) * Real.sqrt (1 / Fintype.card Key) :=
  abs_avg_prfMsgAdv_le bytes keyBytes trunc hlen hbytes hkey hnk _ fun _ ↦
    isChargeBound_slRed_hash romWorld pre adv st0 σ post hpre hσ hpost hn hm

end main

end Quantum.StdModel.Qrom

end
