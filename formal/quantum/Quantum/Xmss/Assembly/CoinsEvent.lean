module

public import Quantum.Xmss.Assembly.Security

@[expose] public section

/-!
# Runtime 2 with coins against runtime 2 (Security's debt `coinsLazy`)

`runtime2CoinsR Lc` is `runtimeR` except at the read ports, which read the view `hwView W Lc`: a
read of a cell of the coin table `Lc` that is not hardwired returns the coin and leaves the
databases untouched, where `runtimeR` reads the compressed database. The two runtimes have the same
sponge, program and record ports.

* **No lazy-sampling equality.** After a coin read runtime 2 holds the read value in its database
  and answers later adversary queries of the cell with it, while runtime 2 with coins answers them
  independently of the coin; averaging over the coins does not remove the difference. So the two
  runtimes are compared by a hybrid, charged to the reads of non-hardwired coin cells.
* **The hybrid** (`sqrt_win_runtime2CoinsR_le`): the Kraus operators differ only at the read ports,
  by at most `4` times the mass of the states whose read cell is a coin cell that is not hardwired
  (`coinReadMass`, Kraus's `krausWeight_le_hidden` with the hidden sets the cells of `Lc`); the
  masses are those of the run against `runtimeR`. Zero mass gives `P_c ≤ P_R`
  (`win_runtime2CoinsR_le_of_zero`).
* **Security's form.** `uavg_p2CR_le`: `E P_c ≤ (√(E P_R) + ∑ⱼ √(4 E μⱼ))²` with `x2 = gameR A`
  and `μⱼ = coinReadMassR`; `coinsLazy_of_coinReadMassR_eq_zero`: `coinsLazy` when the canonical
  game never reads a non-hardwired coin cell; `coinsLazy_hwEmpty`: `coinsLazy` outright for the
  empty coin table, with `x2 = gameR A`. For a nonempty coin table the canonical game's reads (whose
  cells follow random read outcomes) hit a coin cell with small but positive mass, so `coinsLazy`
  needs the error term of `uavg_p2CR_le`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel

/-! ## The hybrid, for a general label and memory -/

section generic

/-- The Kraus weight of a difference vanishes at a port where the two families agree. -/
theorem krausWeight_sub_eq_zero {s : QuantumOracleSpec.{0, 0}} {D : QReg}
    {U W : ∀ i, s.Result i → Matrix (s.Out i × D) (s.In i × D) ℂ} {i : s.Port}
    (h : ∀ r, U i r = W i r) (σ : Matrix (s.In i × D) (s.In i × D) ℂ) :
    krausWeight (fun i r ↦ U i r - W i r) i σ = 0 := by
  rw [krausWeight]
  refine ENNReal.tsum_eq_zero.2 fun r ↦ ?_
  rw [MatrixMap.conj_apply, show U i r - W i r = 0 from sub_eq_zero.2 (h r)]
  have h0 : ∀ {a b : Type} [Fintype a] [Fintype b] (τ : Matrix a a ℂ),
      ((0 : Matrix b a ℂ) * τ * (0 : Matrix b a ℂ)ᴴ).trace.re ≤ 0 := fun _ ↦ by simp
  exact ENNReal.ofReal_eq_zero.2 (h0 (b := s.Out i × D) σ)

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

/-- **The coin-read mass**: at a read port, the mass of the states whose read cell is a cell of the
coin table `Lc` that is not hardwired; `0` at the sponge and program ports. -/
noncomputable def coinReadMass (Lc : Hw X Z) :
    ∀ i : (hwSpec X Z M).Port, Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞
  | .inl (.inl _) => fun _ ↦ 0
  | .inl (.inr c) =>
      hiddenMass {z | Lc.1 z ≠ none} {x | Lc.2.1 x ≠ none} {x | Lc.2.2 x ≠ none} (.inl (.inr c))
  | .inr _ => fun _ ↦ 0

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The empty coin table has no coin-read mass. -/
theorem coinReadMass_hwEmpty (i : (hwSpec X Z M).Port)
    (σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ) :
    coinReadMass (hwEmpty X Z) i σ = 0 := by
  rcases i with (i | c) | c
  · rfl
  · cases c <;> simp [coinReadMass, hiddenMass, hwEmpty, Database.empty, diagMass]
  · rfl

variable [Nonempty X] [Nonempty Z]

/-- **Runtime 2 against runtime 2 with coins, per call**: at most `4` times the coin-read mass. -/
theorem krausWeight_coins_le (Lc : Hw X Z) (m₀ : M) (i : (hwSpec X Z M).Port)
    {σ : Matrix ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦ kraus2 X Z m₀ i r - krausCoins X Z Lc m₀ i r) i σ ≤
      4 * coinReadMass Lc i σ := by
  rcases i with (i | c) | c
  · exact (krausWeight_sub_eq_zero (U := kraus2 X Z m₀) (W := krausCoins X Z Lc m₀)
      (fun _ ↦ rfl) σ).trans_le zero_le
  · exact krausWeight_le_hidden (M := M) Lc m₀ ⟨fun _ h ↦ h, fun _ h ↦ h, fun _ h ↦ h⟩
      (.inl (.inr c)) hσ
  · exact (krausWeight_sub_eq_zero (U := kraus2 X Z m₀) (W := krausCoins X Z Lc m₀)
      (fun _ ↦ rfl) σ).trans_le zero_le

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ] {t : QuantumOracleSpec.{0, 0}}

/-- **Runtime 2 with coins against runtime 2, both extended by the same steps.** If the coin-read
mass (extended by `0`) of the `j`-th call of the run against extended runtime 2 is at most `μ j`,
then `√P_c ≤ √P₂ + ∑ⱼ √(4 μ j)`. -/
theorem sqrt_win_runtime2Coins_extend_le (Lc : Hw X Z) (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    {K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ}
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r))
    (x : QuantumComp Λ ((hwSpec X Z M).sum t) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hμ : ∀ j, ((runtime2 X Z m₀).extend step').queryWeight I (extWeight (coinReadMass Lc)) x
      (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j ≤ μ j) :
    ((runtime2Coins X Z Lc m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((runtime2 X Z m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_evalDistMap_extend_le I (initHw X Z m₀) (runtime2_branch m₀)
    (runtime2Coins_branch Lc m₀) step' hK (fun i σ ↦ 4 * coinReadMass Lc i σ)
    (fun i _ hσ ↦ krausWeight_coins_le Lc m₀ i hσ) x ρ f hE).trans (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine (le_of_eq ((congrArg (fun w ↦ ((runtime2 X Z m₀).extend step').queryWeight I w x
    (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j) (extWeight_const_mul 4 _)).trans
    (((runtime2 X Z m₀).extend step').queryWeight_const_mul I 4 x _ j))).trans ?_
  gcongr
  exact hμ j

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

/-- **Runtime 2 with coins against `runtimeR`, both with record ports.** If the coin-read mass of
the `j`-th call of the run against `runtimeR` is at most `μ j`, then `√P_c ≤ √P_R + ∑ⱼ √(4 μ j)`. -/
theorem sqrt_win_runtime2CoinsR_le (Lc : Hw X Z) (m₀ : Finset S × M')
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hμ : ∀ j, (runtimeR m₀).queryWeight I (extWeight (coinReadMass Lc)) x
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j ≤ μ j) :
    (runtime2CoinsR X Z Lc m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      (runtimeR m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) :=
  sqrt_win_runtime2Coins_extend_le I Lc m₀ (t := recSpec S M') recStep
    (fun T r ↦ recStep_branch T r) x ρ f hE hμ

/-- **No coin read, no difference**: with zero coin-read mass at every call, runtime 2 with coins
wins at most as often as `runtimeR`. -/
theorem win_runtime2CoinsR_le_of_zero (Lc : Hw X Z) (m₀ : Finset S × M')
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E)
    (h0 : ∀ j, (runtimeR m₀).queryWeight I (extWeight (coinReadMass Lc)) x
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j = 0) :
    (runtime2CoinsR X Z Lc m₀).evalDistMap I x ρ f E ≤ (runtimeR m₀).evalDistMap I x ρ f E := by
  have h := sqrt_win_runtime2CoinsR_le I Lc m₀ x ρ f hE (μ := fun _ ↦ 0) fun j ↦ (h0 j).le
  simp only [mul_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), tsum_zero,
    add_zero] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2⁻¹)).1 h

/-- The empty coin table has zero coin-read mass at every call. -/
theorem queryWeight_coinReadMass_hwEmpty (m₀ : Finset S × M')
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (j : ℕ) :
    (runtimeR m₀).queryWeight I (extWeight (coinReadMass (hwEmpty X Z))) x
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j = 0 := by
  have hz : ∀ i σ, extWeight (t := recSpec S M') (coinReadMass (M := Finset S × M')
      (hwEmpty X Z)) i σ = 0 * extWeight (t := recSpec S M') (coinReadMass (hwEmpty X Z)) i σ :=
    fun i σ ↦ by
      rw [zero_mul]
      rcases i with i | i
      · exact coinReadMass_hwEmpty i σ
      · rfl
  exact ((runtimeR (X := X) (Z := Z) m₀).queryWeight_congr I (fun i σ _ ↦ hz i σ) x
    (ρ.prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef j).trans
    (((runtimeR (X := X) (Z := Z) m₀).queryWeight_const_mul I 0 x _ j).trans (zero_mul _))

end generic

/-! ## Security's debt `coinsLazy` -/

section security

/-- The coin-read mass of the `j`-th call of the canonical game against `runtimeR`. -/
noncomputable def coinReadMassR (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z)
    (L : HonestTable) (j : ℕ) : ℝ≥0∞ :=
  (runtimeR m0R).queryWeight .instruments (extWeight (coinReadMass (M := Mem) (Lc L)))
    (gameR A L) initR j

/-- **Runtime 2 with coins against `runtimeR` on the canonical game**, per table. -/
theorem sqrt_p2CR_le (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z) (L : HonestTable) :
    p2CR A Lc L ^ (2⁻¹ : ℝ) ≤
      p2R (gameR A) L ^ (2⁻¹ : ℝ) + ∑' j, (4 * coinReadMassR A Lc L j) ^ (2⁻¹ : ℝ) :=
  sqrt_win_runtime2CoinsR_le .instruments (Lc L) m0R (gameR A L) (SubState.basis ()) winObs
    (measurableSet_singleton true) fun _ ↦ le_rfl

/-- **`coinsLazy` with its error term**, averaged over the table: `x2 = gameR A`. -/
theorem uavg_p2CR_le (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z) :
    uavg (p2CR A Lc) ≤ (uavg (p2R (gameR A)) ^ (2⁻¹ : ℝ) +
      ∑' j, (4 * uavg (fun L ↦ coinReadMassR A Lc L j)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  uavg_le_of_hybrid _ _ _ (sqrt_p2CR_le A Lc)

/-- **`coinsLazy`** with `x2 = gameR A`, when the canonical game never reads a coin cell that is not
hardwired. -/
theorem coinsLazy_of_coinReadMassR_eq_zero (A : Adversary (X × Z)) (Lc : HonestTable → Hw X Z)
    (h0 : ∀ L j, coinReadMassR A Lc L j = 0) : uavg (p2CR A Lc) ≤ uavg (p2R (gameR A)) :=
  uavg_mono fun L ↦ win_runtime2CoinsR_le_of_zero .instruments (Lc L) m0R (gameR A L)
    (SubState.basis ()) winObs (measurableSet_singleton true) (h0 L)

/-- **`coinsLazy` for the empty coin table**, with `x2 = gameR A`. -/
theorem coinsLazy_hwEmpty (A : Adversary (X × Z)) :
    uavg (p2CR A fun _ ↦ hwEmpty X Z) ≤ uavg (p2R (gameR A)) :=
  coinsLazy_of_coinReadMassR_eq_zero A _ fun L j ↦
    queryWeight_coinReadMass_hwEmpty .instruments m0R (gameR A L) (SubState.basis ()) j

end security

end Quantum.Xmss.Assembly

end
