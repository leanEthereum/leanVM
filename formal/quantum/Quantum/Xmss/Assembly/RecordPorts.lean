module

public import Quantum.Xmss.Assembly.Template
public import Quantum.Xmss.Hybrid.Coins
public import Quantum.Xmss.Hybrid.Disclose
public import Quantum.Sponge.Oracle.Hardwired

@[expose] public section

/-!
# Runtimes extended by record ports

`Template`'s results are for `runtimeR m₀`, runtime 2 extended by the record ports (`recStep`),
which only grow the memory label. This file restates the hybrid, the mass bounds and the event
bound for runtimes extended by further ports `t` (`QuantumRuntime.extend`), and instantiates them at
the record ports.

* **Kraus operators of an extension** (`sumKraus`, `extend_branch_eq_conj`): the extension of a
  runtime with Kraus operators `U` by steps with Kraus operators `K`. Two runtimes extended by the
  same steps have Kraus differences `0` on the added ports (`krausWeight_sumKraus_sub_inr`), so a
  bound `w` on the Kraus weights of the differences extends by `0` (`extWeight`,
  `krausWeight_sumKraus_sub_le`), and the square-root hybrid holds for the extended runtimes
  (`rpow_inv_two_evalDistMap_extend_le`).
* **The hybrids** (Kraus, Coins): `krausWeight_le_hidden_extend`, `sqrt_win_runtime1_extend_le`,
  `krausWeight_le_coinMass_extend`, `sqrt_win_runtime1_extend_le_coins`,
  `uavg_win_runtime1_extend_le_coins`; at the record ports `sqrt_win_runtime1R_le`,
  `sqrt_win_runtime1R_le_coins`, `uavg_win_runtime1R_le_coins` (`runtime1R`, `runtime2CoinsR`).
* **The mass bounds** (Disclose): the hidden mass extended by `0` is the diagonal mass of
  `extHidSet` (empty on the added ports), so `sum_queryWeight_view_le` gives
  `sum_queryWeight_hiddenMass_extend_le` and its instances (`…_hiddenK_digest_extend_le`,
  `…_hiddenK'_extend_le`, `…_hiddenH_extend_le`, `…_hiddenKNext_extend_le`), with `ViewByOn` for
  any set of ports containing the sponge and read ports (`viewByOn_gameT`'s `isLeft` included);
  `sum_queryWeight_hiddenMass_runtimeR_le` at the record ports.
* **The event bound**: the added ports are classical calls (`extCls`) with costs `dT`, keeping the
  grade bound (`rpow_inv_two_eventWeight_extend_le`, `eventWeight_extend_le`, for the hardwired
  runtime written as `QuantumRuntime.mk` with the initial state and steps of
  `spongeHardwiredRuntime`, so that runtime 2 is an instance without unfolding). A record port
  keeps the databases (`eq_of_recKraus_ne_zero`, `querySupportedOn_recStep`); for a bad set that
  does not read the memory label (`LabelFree`) its Kraus operators commute with the event
  projector (`one_kronecker_hwProjector_mul_comm`), so its cost is `0`
  (`tsum_potential_le_of_mem_iff`, `tsum_potential_recStep_le`, `eventWeight_runtimeR_le`).
-/

open Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v w

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Extensions by further ports -/

section ext

variable {s t : QuantumOracleSpec.{0, 0}} {D : QReg}

/-- Weights on the ports of `s.sum t`: `w` on those of `s`, `w'` on those of `t`. -/
def sumWeight (w : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞)
    (w' : ∀ j : t.Port, Matrix (t.In j × D) (t.In j × D) ℂ → ℝ≥0∞) :
    ∀ i : (s.sum t).Port, Matrix ((s.sum t).In i × D) ((s.sum t).In i × D) ℂ → ℝ≥0∞
  | .inl i => w i
  | .inr j => w' j

/-- Weights extended by `0` on the ports of `t`. -/
abbrev extWeight (w : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞) :
    ∀ i : (s.sum t).Port, Matrix ((s.sum t).In i × D) ((s.sum t).In i × D) ℂ → ℝ≥0∞ :=
  sumWeight w fun _ _ ↦ 0

/-- Data on the inputs of the ports of `s.sum t`: `f` on those of `s`, `g` on those of `t`. -/
def sumPort {β : Type*} (f : ∀ i : s.Port, s.In i × D → β) (g : ∀ j : t.Port, t.In j × D → β) :
    ∀ i : (s.sum t).Port, (s.sum t).In i × D → β
  | .inl i => f i
  | .inr j => g j

/-- The Kraus operators of an extension: `U` on the ports of `s`, `K` on those of `t`. -/
def sumKraus (U : ∀ i, s.Result i → Matrix (s.Out i × D) (s.In i × D) ℂ)
    (K : ∀ j, t.Result j → Matrix (t.Out j × D) (t.In j × D) ℂ) :
    ∀ i, (s.sum t).Result i → Matrix ((s.sum t).Out i × D) ((s.sum t).In i × D) ℂ
  | .inl i => U i
  | .inr j => K j

theorem extWeight_const_mul (c : ℝ≥0∞)
    (w : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞) :
    extWeight (t := t) (fun i σ ↦ c * w i σ) = fun i σ ↦ c * extWeight w i σ := by
  funext i σ
  rcases i with i | j
  · rfl
  · exact (mul_zero c).symm

theorem extWeight_add (w₁ w₂ : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞) :
    extWeight (t := t) (fun i σ ↦ w₁ i σ + w₂ i σ) =
      fun i σ ↦ extWeight w₁ i σ + extWeight w₂ i σ := by
  funext i σ
  rcases i with i | j
  · rfl
  · exact (add_zero 0).symm

/-- **The Kraus operators of an extended runtime.** -/
theorem extend_branch_eq_conj (R : QuantumRuntime s)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × R.D) (t.Out j × R.D) (t.Result j))
    {U : ∀ i, s.Result i → Matrix (s.Out i × R.D) (s.In i × R.D) ℂ}
    {K : ∀ j, t.Result j → Matrix (t.Out j × R.D) (t.In j × R.D) ℂ}
    (hU : ∀ i r, (R.step i).branch r = MatrixMap.conj (U i r))
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r)) :
    ∀ i r, ((R.extend step').step i).branch r = MatrixMap.conj (sumKraus U K i r)
  | .inl i, r => hU i r
  | .inr j, r => hK j r

/-- Two runtimes extended by the same steps differ by `0` on the added ports. -/
theorem krausWeight_sumKraus_sub_inr {U W : ∀ i, s.Result i → Matrix (s.Out i × D) (s.In i × D) ℂ}
    (K : ∀ j, t.Result j → Matrix (t.Out j × D) (t.In j × D) ℂ) (j : t.Port)
    (σ : Matrix ((s.sum t).In (.inr j) × D) ((s.sum t).In (.inr j) × D) ℂ) :
    krausWeight (fun i r ↦ sumKraus U K i r - sumKraus W K i r) (.inr j) σ = 0 := by
  rw [krausWeight]
  refine ENNReal.tsum_eq_zero.2 fun r ↦ ?_
  rw [MatrixMap.conj_apply, show sumKraus U K (.inr j) r - sumKraus W K (.inr j) r = 0 from
    sub_self (K j r)]
  have h0 : ∀ {a b : Type} [Fintype a] [Fintype b] (τ : Matrix a a ℂ),
      ((0 : Matrix b a ℂ) * τ * (0 : Matrix b a ℂ)ᴴ).trace.re ≤ 0 := fun _ ↦ by simp
  exact ENNReal.ofReal_eq_zero.2 (h0 (b := t.Out j × D) σ)

/-- A bound on the Kraus weights of the differences extends by `0` to the added ports. -/
theorem krausWeight_sumKraus_sub_le {U W : ∀ i, s.Result i → Matrix (s.Out i × D) (s.In i × D) ℂ}
    (K : ∀ j, t.Result j → Matrix (t.Out j × D) (t.In j × D) ℂ)
    {w : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞}
    (hw : ∀ i σ, σ.PosSemidef → krausWeight (fun i r ↦ U i r - W i r) i σ ≤ w i σ)
    (i : (s.sum t).Port) (σ : Matrix ((s.sum t).In i × D) ((s.sum t).In i × D) ℂ)
    (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦ sumKraus U K i r - sumKraus W K i r) i σ ≤ extWeight w i σ := by
  rcases i with i | j
  · exact hw i σ hσ
  · rw [krausWeight_sumKraus_sub_inr]
    exact zero_le

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **The square-root hybrid for extended runtimes.** Two runtimes on one register and initial
state with Kraus operators `U` and `W`, extended by the same steps, satisfy the square-root hybrid
with any bound `w` on the Kraus weights of `U - W`, extended by `0` on the added ports. -/
theorem rpow_inv_two_evalDistMap_extend_le (σ₀ : SubState D)
    {s₀ s₁ : ∀ i, SubInstrument (s.In i × D) (s.Out i × D) (s.Result i)}
    {U W : ∀ i, s.Result i → Matrix (s.Out i × D) (s.In i × D) ℂ}
    (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
    (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
    (step' : ∀ j : t.Port, SubInstrument (t.In j × D) (t.Out j × D) (t.Result j))
    {K : ∀ j, t.Result j → Matrix (t.Out j × D) (t.In j × D) ℂ}
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r))
    (w : ∀ i : s.Port, Matrix (s.In i × D) (s.In i × D) ℂ → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → krausWeight (fun i r ↦ U i r - W i r) i σ ≤ w i σ)
    (x : QuantumComp Λ (s.sum t) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ) {E : Set γ}
    (hE : MeasurableSet E) :
    ((QuantumRuntime.mk D σ₀ s₁).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((QuantumRuntime.mk D σ₀ s₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' j, ((QuantumRuntime.mk D σ₀ s₀).extend step').queryWeight I (extWeight w) x
          (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_outcomeLawWith_le' I σ₀
    (extend_branch_eq_conj (QuantumRuntime.mk D σ₀ s₀) step' hU hK)
    (extend_branch_eq_conj (QuantumRuntime.mk D σ₀ s₁) step' hW hK) x ρ f hE).trans
    (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  exact ((QuantumRuntime.mk D σ₀ s₀).extend step').queryWeight_mono I
    (fun i σ hσ ↦ krausWeight_sumKraus_sub_le K hw i σ hσ) x (ρ.prod σ₀).posSemidef j

end ext

/-! ## The hybrids with extended runtimes -/

section hybrid

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] [Nonempty X]
  [Nonempty Z] {t : QuantumOracleSpec.{0, 0}} {Hh : Set Z} {Hk Hk' : Set X}

/-- **Kraus's per-call bound, extended**: at most `4` times the hidden mass on the ports of
runtime 2, `0` on the added ports. -/
theorem krausWeight_le_hidden_extend (L : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ)
    (i : ((hwSpec X Z M).sum t).Port)
    {σ : Matrix (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M))
      (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦ sumKraus (kraus2 X Z m₀) K i r - sumKraus (kraus1 X Z L m₀) K i r)
      i σ ≤ 4 * extWeight (hiddenMass Hh Hk Hk') i σ := by
  rcases i with i | j
  · exact krausWeight_le_hidden L m₀ hL i hσ
  · rw [krausWeight_sumKraus_sub_inr]
    exact zero_le

/-- **Coins' per-call bound, extended**: at most `4` times the coin mass on the ports of runtime
2, `0` on the added ports. -/
theorem krausWeight_le_coinMass_extend (L Lc : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (hc : SubTable Lc L)
    (K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ)
    (i : ((hwSpec X Z M).sum t).Port)
    {σ : Matrix (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M))
      (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M)) ℂ} (hσ : σ.PosSemidef) :
    krausWeight (fun i r ↦ sumKraus (krausCoins X Z Lc m₀) K i r -
      sumKraus (kraus1 X Z L m₀) K i r) i σ ≤ 4 * extWeight (coinMass Hh Hk Hk' Lc) i σ := by
  rcases i with i | j
  · exact krausWeight_le_coinMass L Lc m₀ hL hc i hσ
  · rw [krausWeight_sumKraus_sub_inr]
    exact zero_le

variable {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xf : QReg → Type w} {A : QReg} {γ : Type*}
  [MeasurableSpace γ]

/-- **Runtime 1 against runtime 2, both extended by the same steps.** If the hidden mass (extended
by `0`) of the `j`-th call of the run against extended runtime 2 is at most `μ j`, then
`√P₁ ≤ √P₂ + ∑ⱼ √(4 μ j)`. -/
theorem sqrt_win_runtime1_extend_le (L : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    {K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ}
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r))
    (x : QuantumComp Λ ((hwSpec X Z M).sum t) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hHidden : ∀ j, ((runtime2 X Z m₀).extend step').queryWeight I
      (extWeight (hiddenMass Hh Hk Hk')) x (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j ≤ μ j) :
    ((runtime1 X Z L m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((runtime2 X Z m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_evalDistMap_extend_le I (initHw X Z m₀) (runtime2_branch m₀)
    (runtime1_branch L m₀) step' hK (fun i σ ↦ 4 * hiddenMass Hh Hk Hk' i σ)
    (fun i _ hσ ↦ krausWeight_le_hidden L m₀ hL i hσ) x ρ f hE).trans (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine (le_of_eq ((congrArg (fun w ↦ ((runtime2 X Z m₀).extend step').queryWeight I w x
    (ρ.matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j) (extWeight_const_mul 4 _)).trans
    (((runtime2 X Z m₀).extend step').queryWeight_const_mul I 4 x _ j))).trans ?_
  gcongr
  exact hHidden j

/-- **Runtime 1 against runtime 2 with coins, both extended by the same steps.** -/
theorem sqrt_win_runtime1_extend_le_coins (L Lc : Hw X Z) (m₀ : M) (hL : Covers L Hh Hk Hk')
    (hc : SubTable Lc L)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    {K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ}
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r))
    (x : QuantumComp Λ ((hwSpec X Z M).sum t) Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hMass : ∀ j, ((runtime2Coins X Z Lc m₀).extend step').queryWeight I
      (extWeight (coinMass Hh Hk Hk' Lc)) x
      (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j ≤ μ j) :
    ((runtime1 X Z L m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      ((runtime2Coins X Z Lc m₀).extend step').evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_evalDistMap_extend_le I (initHw X Z m₀) (runtime2Coins_branch Lc m₀)
    (runtime1_branch L m₀) step' hK (fun i σ ↦ 4 * coinMass Hh Hk Hk' Lc i σ)
    (fun i _ hσ ↦ krausWeight_le_coinMass L Lc m₀ hL hc i hσ) x ρ f hE).trans
    (add_le_add le_rfl ?_)
  refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine (le_of_eq ((congrArg (fun w ↦ ((runtime2Coins X Z Lc m₀).extend step').queryWeight I w x
    (ρ.matrix ⊗ₖ (runtime2Coins X Z Lc m₀).init.matrix) j) (extWeight_const_mul 4 _)).trans
    (((runtime2Coins X Z Lc m₀).extend step').queryWeight_const_mul I 4 x _ j))).trans ?_
  gcongr
  exact hMass j

/-- **Runtime 1 against runtime 2 with coins, extended, averaged over the table, with the coin
cells split off** (`uavg_win_runtime1_le_coins` for the extended runtimes). -/
theorem uavg_win_runtime1_extend_le_coins {Θ : Type*} [Fintype Θ] (L Lc : Θ → Hw X Z)
    (Hh₀ Ch : Θ → Set Z) (Hk₀ Hk'₀ Ck Ck' : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ))
    (hc : ∀ θ, SubTable (Lc θ) (L θ)) (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    {K : ∀ j, t.Result j →
      Matrix (t.Out j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ}
    (hK : ∀ j r, (step' j).branch r = MatrixMap.conj (K j r))
    (x : Θ → QuantumComp Λ ((hwSpec X Z M).sum t) Xf A) (ρ : Θ → SubState A)
    (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (μ : Θ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞)
    (hμ : ∀ θ j, ((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight I
      (extWeight (hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j)
    (hε : ∀ j, uavg (fun θ ↦ ((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight I
      (extWeight (hiddenMass (Ch θ) (Ck θ) (Ck' θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j) ≤ ε j) :
    uavg (fun θ ↦ ((runtime1 X Z (L θ) m₀).extend step').evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ ((runtime2Coins X Z (Lc θ) m₀).extend step').evalDistMap I (x θ) (ρ θ)
          (f θ) E) ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * (uavg (fun θ ↦ μ θ j) + ε j)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set ν : Θ → ℕ → ℝ≥0∞ := fun θ j ↦ ((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight I
    (extWeight (hiddenMass (Ch θ) (Ck θ) (Ck' θ))) (x θ)
    ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j
  have hMass : ∀ θ j, ((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight I
      (extWeight (coinMass (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ) (Lc θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j + ν θ j :=
    fun θ j ↦ by
      refine (((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight_mono I
        (w' := extWeight fun i σ ↦ hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ) i σ +
          hiddenMass (Ch θ) (Ck θ) (Ck' θ) i σ)
        (fun i σ _ ↦ ?_) (x θ) ((ρ θ).prod (runtime2Coins X Z (Lc θ) m₀).init).posSemidef
        j).trans (((congrArg (fun w ↦ ((runtime2Coins X Z (Lc θ) m₀).extend step').queryWeight
          I w (x θ) ((ρ θ).matrix ⊗ₖ (runtime2Coins X Z (Lc θ) m₀).init.matrix) j)
          (extWeight_add _ _)).trans (QuantumRuntime.queryWeight_add
            ((runtime2Coins X Z (Lc θ) m₀).extend step') I _ _ (x θ) _ j)).trans_le
          (add_le_add (hμ θ j) le_rfl))
      rcases i with i | j
      · exact (coinMass_le_hiddenMass _ _ _ _ i σ).trans (hiddenMass_union_le _ _ _ _ _ _ i σ)
      · exact le_rfl
  refine (uavg_le_of_hybrid _ _ (fun θ j ↦ μ θ j + ν θ j) fun θ ↦
    sqrt_win_runtime1_extend_le_coins I (L θ) (Lc θ) m₀ (hL θ) (hc θ) step' hK (x θ) (ρ θ) (f θ)
      hE (hMass θ)).trans ?_
  gcongr with j
  rw [uavg_add]
  exact add_le_add le_rfl (hε j)

/-! ### At the record ports -/

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

variable (X Z) in
/-- **Runtime 1 with record ports.** -/
@[reducible]
noncomputable def runtime1R (L : Hw X Z) (m₀ : Finset S × M') :
    QuantumRuntime (recHwSpec X Z S M') :=
  (runtime1 X Z L m₀).extend (t := recSpec S M') recStep

variable (X Z) in
/-- **Runtime 2 with coins and record ports.** -/
@[reducible]
noncomputable def runtime2CoinsR (Lc : Hw X Z) (m₀ : Finset S × M') :
    QuantumRuntime (recHwSpec X Z S M') :=
  (runtime2Coins X Z Lc m₀).extend (t := recSpec S M') recStep

/-- **Runtime 1 against `runtimeR`** (Kraus's hybrid with record ports, which cost `0`). -/
theorem sqrt_win_runtime1R_le (L : Hw X Z) (m₀ : Finset S × M') (hL : Covers L Hh Hk Hk')
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hHidden : ∀ j, (runtimeR m₀).queryWeight I (extWeight (hiddenMass Hh Hk Hk')) x
      (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) j ≤ μ j) :
    (runtime1R X Z L m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      (runtimeR m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) :=
  sqrt_win_runtime1_extend_le I L m₀ hL (t := recSpec S M') recStep
    (fun T r ↦ recStep_branch T r) x ρ f hE hHidden

/-- **Runtime 1 against runtime 2 with coins, both with record ports.** -/
theorem sqrt_win_runtime1R_le_coins (L Lc : Hw X Z) (m₀ : Finset S × M')
    (hL : Covers L Hh Hk Hk') (hc : SubTable Lc L)
    (x : QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : SubState A) (f : (Σ u, Xf u) → γ)
    {E : Set γ} (hE : MeasurableSet E) {μ : ℕ → ℝ≥0∞}
    (hMass : ∀ j, (runtime2CoinsR X Z Lc m₀).queryWeight I (extWeight (coinMass Hh Hk Hk' Lc)) x
      (ρ.matrix ⊗ₖ (runtime2CoinsR X Z Lc m₀).init.matrix) j ≤ μ j) :
    (runtime1R X Z L m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) ≤
      (runtime2CoinsR X Z Lc m₀).evalDistMap I x ρ f E ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * μ j) ^ (2⁻¹ : ℝ) :=
  sqrt_win_runtime1_extend_le_coins I L Lc m₀ hL hc (t := recSpec S M') recStep
    (fun T r ↦ recStep_branch T r) x ρ f hE hMass

/-- **The averaged coin hybrid with record ports.** -/
theorem uavg_win_runtime1R_le_coins {Θ : Type*} [Fintype Θ] (L Lc : Θ → Hw X Z)
    (Hh₀ Ch : Θ → Set Z) (Hk₀ Hk'₀ Ck Ck' : Θ → Set X)
    (hL : ∀ θ, Covers (L θ) (Hh₀ θ ∪ Ch θ) (Hk₀ θ ∪ Ck θ) (Hk'₀ θ ∪ Ck' θ))
    (hc : ∀ θ, SubTable (Lc θ) (L θ)) (m₀ : Finset S × M')
    (x : Θ → QuantumComp Λ (recHwSpec X Z S M') Xf A) (ρ : Θ → SubState A)
    (f : Θ → (Σ u, Xf u) → γ) {E : Set γ} (hE : MeasurableSet E) (μ : Θ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞)
    (hμ : ∀ θ j, (runtime2CoinsR X Z (Lc θ) m₀).queryWeight I
      (extWeight (hiddenMass (Hh₀ θ) (Hk₀ θ) (Hk'₀ θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2CoinsR X Z (Lc θ) m₀).init.matrix) j ≤ μ θ j)
    (hε : ∀ j, uavg (fun θ ↦ (runtime2CoinsR X Z (Lc θ) m₀).queryWeight I
      (extWeight (hiddenMass (Ch θ) (Ck θ) (Ck' θ))) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2CoinsR X Z (Lc θ) m₀).init.matrix) j) ≤ ε j) :
    uavg (fun θ ↦ (runtime1R X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ≤
      (uavg (fun θ ↦ (runtime2CoinsR X Z (Lc θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) E) ^
          (2⁻¹ : ℝ) +
        ∑' j, (4 * (uavg (fun θ ↦ μ θ j) + ε j)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  uavg_win_runtime1_extend_le_coins I L Lc Hh₀ Ch Hk₀ Hk'₀ Ck Ck' hL hc m₀ (t := recSpec S M')
    recStep (fun T r ↦ recStep_branch T r) x ρ f hE μ ε hμ hε

end hybrid

/-! ## The mass bounds for extended runtime 2 -/

section disclose

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] {t : QuantumOracleSpec.{0, 0}}

/-- The hidden sets of the inputs (`hidSet`), empty on the added ports. -/
def extHidSet (Hh : Set Z) (Hk Hk' : Set X) :
    ∀ i : ((hwSpec X Z M).sum t).Port,
      Set (((hwSpec X Z M).sum t).In i × QReg.of (HwReg X Z M))
  | .inl i => hidSet Hh Hk Hk' i
  | .inr _ => ∅

theorem extWeight_hiddenMass_eq (Hh : Set Z) (Hk Hk' : Set X) :
    extWeight (t := t) (hiddenMass (M := M) Hh Hk Hk') =
      fun i ↦ diagMass (extHidSet Hh Hk Hk' i) := by
  funext i σ
  rcases i with i | j
  · exact congrFun (congrFun (hiddenMass_eq_diagMass Hh Hk Hk') i) σ
  · exact (Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _).symm

variable [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **`sum_queryWeight_hiddenMass_le` for runtime 2 extended by further ports**, with the hidden
mass extended by `0`, under `ViewByOn` for any set of ports `P` containing the sponge and read
ports. -/
theorem sum_queryWeight_hiddenMass_extend_le {D : S → Type} [∀ s, Fintype (D s)]
    [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (lab : HwReg X Z M → Finset S)
    (x : ((s : S) → D s) → QuantumComp Λ ((hwSpec X Z M).sum t) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ) (P : ((hwSpec X Z M).sum t).Port → Prop)
    (hP : ∀ i, P (.inl (.inl i)))
    (hview : ViewByOn ((runtime2 X Z m₀).extend step') I P lab x ρ j)
    (Hh : ((s : S) → D s) → Set Z) (Hk Hk' : ((s : S) → D s) → Set X)
    (sh : Z → HwReg X Z M → Finset S) (sk sk' : X → HwReg X Z M → Finset S)
    (Fh : Z → HwReg X Z M → (s : S) → ((s : S) → D s) → Finset (D s))
    (Fk Fk' : X → HwReg X Z M → (s : S) → ((s : S) → D s) → Finset (D s))
    (hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v)
    (hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v)
    (hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v)
    (hh : ∀ v z r, z ∈ Hh v → r.2.1.1 z = none → ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none →
      ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v)
    (hk' : ∀ v y r, y ∈ Hk' v → r.2.1.2.2 y = none →
      ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v)
    (κ : ℝ≥0∞)
    (hκh : ∀ z r v, ∑ s ∈ sh z r,
      ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk : ∀ y r v, ∑ s ∈ sk y r,
      ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk' : ∀ y r v, ∑ s ∈ sk' y r,
      ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, ((runtime2 X Z m₀).extend step').queryWeight I
        (extWeight (hiddenMass (Hh v) (Hk v) (Hk' v))) (x v) (ρ v) j ≤
      κ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  have hw : ∀ v, ((runtime2 X Z m₀).extend step').queryWeight I
      (extWeight (hiddenMass (Hh v) (Hk v) (Hk' v))) (x v) (ρ v) j =
        ((runtime2 X Z m₀).extend step').queryWeight I
          (fun i ↦ diagMass (extHidSet (Hh v) (Hk v) (Hk' v) i)) (x v) (ρ v) j := fun v ↦
    congrArg (fun w ↦ ((runtime2 X Z m₀).extend step').queryWeight I w (x v) (ρ v) j)
      (extWeight_hiddenMass_eq _ _ _)
  rw [Finset.sum_congr rfl fun v _ ↦ hw v]
  refine sum_queryWeight_view_le ((runtime2 X Z m₀).extend step') I lab x ρ hρ j P hview
    (fun v ↦ extHidSet (Hh v) (Hk v) (Hk' v)) (fun v i hi ↦ ?_)
    (sumPort (liftCells sh sk sk' ∅) fun _ _ ↦ ∅)
    (sumPort (liftCells Fh Fk Fk' fun _ _ ↦ ∅) fun _ _ _ _ ↦ ∅) (fun i p s v d ↦ ?_)
    (fun v i p hp ↦ ?_) κ (fun i p v ↦ ?_)
  · rcases i with (i | c) | j
    · exact absurd (hP i) hi
    · rfl
    · rfl
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | j
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · exact hFh _ _ s v d
    · exact hFk _ _ s v d
    · exact hFk' _ _ s v d
    · rfl
    · rfl
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | j
    · exact hh v _ _ hp.1 hp.2
    · exact hk v _ _ hp.1 hp.2
    · exact hk' v _ _ hp.1 hp.2
    · exact hh v _ _ hp.1 hp.2
    · exact hk v _ _ hp.1 hp.2
    · exact hk' v _ _ hp.1 hp.2
    · exact hp.elim
    · exact hp.elim
  · rcases i with (((_ | _ | _) | (⟨z, upd⟩ | ⟨y, upd⟩ | ⟨y, upd⟩)) | c) | j
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · exact hκh _ _ v
    · exact hκk _ _ v
    · exact hκk' _ _ v
    · simp [sumPort, liftCells]
    · simp [sumPort]

/-- **Hidden `k`-cells naming one 128-bit value, extended**: `2^-128` per call on average. -/
theorem sum_queryWeight_hiddenK_digest_extend_le (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (lab : HwReg X Z M → Finset S)
    (x : (S → HashSig.Digest) → QuantumComp Λ ((hwSpec X Z M).sum t) Ω A)
    (ρ : (S → HashSig.Digest) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ) (P : ((hwSpec X Z M).sum t).Port → Prop)
    (hP : ∀ i, P (.inl (.inl i)))
    (hview : ViewByOn (D := fun _ : S ↦ HashSig.Digest) ((runtime2 X Z m₀).extend step') I P lab
      x ρ j)
    (Hk : (S → HashSig.Digest) → Set X) (src : X → HwReg X Z M → S)
    (val : X → HwReg X Z M → HashSig.Digest)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none → src y r ∉ lab r ∧ v (src y r) = val y r) :
    ∑ v, ((runtime2 X Z m₀).extend step').queryWeight I (extWeight (hiddenMass ∅ (Hk v) ∅))
        (x v) (ρ v) j ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  have hcard : (Fintype.card HashSig.Digest : ℝ≥0∞) = 2 ^ 128 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    norm_num [HashSig.digestBits]
  refine sum_queryWeight_hiddenMass_extend_le (D := fun _ : S ↦ HashSig.Digest) I m₀ step' lab x
    ρ hρ j P hP hview (fun _ ↦ ∅) Hk (fun _ ↦ ∅) (fun _ _ ↦ ∅) (fun y r ↦ {src y r})
    (fun _ _ ↦ ∅) (fun _ _ _ _ ↦ ∅) (fun y r _ _ ↦ {val y r}) (fun _ _ _ _ ↦ ∅)
    (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ hz ↦ hz.elim)
    (fun v y r hy hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) _ (fun _ _ _ ↦ by simp) (fun y r v ↦ ?_)
    (fun _ _ _ ↦ by simp)
  · obtain ⟨h1, h2⟩ := hk v y r hy hW
    exact ⟨src y r, Finset.mem_singleton_self _, h1, by simp [h2]⟩
  · simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul]
    show (Fintype.card HashSig.Digest : ℝ≥0∞)⁻¹ ≤ _
    rw [hcard]

/-- **The `k'`-cells of hidden paths, extended**: `|S| G / |Z|` per call on average. -/
theorem sum_queryWeight_hiddenK'_extend_le (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (π : Equiv.Perm (X × Z)) {G : ℕ} (hπ : PermGood π G) (lab : HwReg X Z M → Finset S)
    (x : (S → Z) → QuantumComp Λ ((hwSpec X Z M).sum t) Ω A)
    (ρ : (S → Z) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ) (P : ((hwSpec X Z M).sum t).Port → Prop)
    (hP : ∀ i, P (.inl (.inl i)))
    (hview : ViewByOn (D := fun _ : S ↦ Z) ((runtime2 X Z m₀).extend step') I P lab x ρ j)
    (Hk' : (S → Z) → Set X) (y : S → (S → Z) → X) (c : S → (S → Z) → Z)
    (hy : ∀ s v d, y s (Function.update v s d) = y s v)
    (hc : ∀ s v d, c s (Function.update v s d) = c s v)
    (hk' : ∀ v x' r, x' ∈ Hk' v → r.2.1.2.2 x' = none →
      ∃ s, s ∉ lab r ∧ (π (y s v, c s v + v s)).1 = x') :
    ∑ v, ((runtime2 X Z m₀).extend step').queryWeight I (extWeight (hiddenMass ∅ ∅ (Hk' v)))
        (x v) (ρ v) j ≤
      (Fintype.card S * G * (Fintype.card Z : ℝ≥0∞)⁻¹) *
        ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_extend_le (D := fun _ : S ↦ Z) I m₀ step' lab x ρ hρ j P hP
    hview (fun _ ↦ ∅) (fun _ ↦ ∅) Hk' (fun _ _ ↦ ∅) (fun _ _ ↦ ∅) (fun _ _ ↦ Finset.univ)
    (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ ↦ ∅)
    (fun x' _ s v ↦ Finset.univ.filter fun a : Z ↦ (π (y s v, c s v + a)).1 = x')
    (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun x' r s v d ↦ by simp only [hy, hc])
    (fun _ _ _ hz ↦ hz.elim) (fun _ _ _ hy ↦ hy.elim) (fun v x' r hx hW ↦ ?_) _
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun x' r v ↦ ?_)
  · obtain ⟨s, hs, he⟩ := hk' v x' r hx hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [he]⟩
  · calc ∑ s ∈ (Finset.univ : Finset S), ((Finset.univ.filter fun a : Z ↦
            (π (y s v, c s v + a)).1 = x').card : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹
        ≤ ∑ _s ∈ (Finset.univ : Finset S), (G : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_le_sum fun s _ ↦ ?_
          rw [card_filter_rate_eq]
          gcongr
          exact_mod_cast hπ.rate _ _
      _ = Fintype.card S * G * (Fintype.card Z : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- **The `h`-cells of hidden paths, extended**: `|S| / |Z|` per call on average. -/
theorem sum_queryWeight_hiddenH_extend_le (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (lab : HwReg X Z M → Finset S)
    (x : (S → Z) → QuantumComp Λ ((hwSpec X Z M).sum t) Ω A)
    (ρ : (S → Z) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ) (P : ((hwSpec X Z M).sum t).Port → Prop)
    (hP : ∀ i, P (.inl (.inl i)))
    (hview : ViewByOn (D := fun _ : S ↦ Z) ((runtime2 X Z m₀).extend step') I P lab x ρ j)
    (Hh : (S → Z) → Set Z) (w : S → (S → Z) → Z)
    (hw : ∀ s v d, w s (Function.update v s d) = w s v)
    (hh : ∀ v z r, z ∈ Hh v → r.2.1.1 z = none → ∃ s, s ∉ lab r ∧ w s v + v s = z) :
    ∑ v, ((runtime2 X Z m₀).extend step').queryWeight I (extWeight (hiddenMass (Hh v) ∅ ∅))
        (x v) (ρ v) j ≤
      (Fintype.card S * (Fintype.card Z : ℝ≥0∞)⁻¹) * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_extend_le (D := fun _ : S ↦ Z) I m₀ step' lab x ρ hρ j P hP
    hview Hh (fun _ ↦ ∅) (fun _ ↦ ∅) (fun _ _ ↦ Finset.univ) (fun _ _ ↦ ∅) (fun _ _ ↦ ∅)
    (fun z _ s v ↦ {z - w s v}) (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ ↦ ∅)
    (fun z r s v d ↦ by simp only [hw]) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl)
    (fun v z r hz hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) (fun _ _ _ hy ↦ hy.elim) _
    (fun z r v ↦ ?_) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
  · obtain ⟨s, hs, he⟩ := hh v z r hz hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [← he]⟩
  · simp [Finset.card_univ]

/-- **The `k`-cells of later blocks of hidden paths, extended**: `|S| / |X|` per call on
average. -/
theorem sum_queryWeight_hiddenKNext_extend_le (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (lab : HwReg X Z M → Finset S)
    (x : (S → X) → QuantumComp Λ ((hwSpec X Z M).sum t) Ω A)
    (ρ : (S → X) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ) (P : ((hwSpec X Z M).sum t).Port → Prop)
    (hP : ∀ i, P (.inl (.inl i)))
    (hview : ViewByOn (D := fun _ : S ↦ X) ((runtime2 X Z m₀).extend step') I P lab x ρ j)
    (Hk : (S → X) → Set X) (u : S → (S → X) → X)
    (hu : ∀ s v d, u s (Function.update v s d) = u s v)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none → ∃ s, s ∉ lab r ∧ u s v + v s = y) :
    ∑ v, ((runtime2 X Z m₀).extend step').queryWeight I (extWeight (hiddenMass ∅ (Hk v) ∅))
        (x v) (ρ v) j ≤
      (Fintype.card S * (Fintype.card X : ℝ≥0∞)⁻¹) * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_extend_le (D := fun _ : S ↦ X) I m₀ step' lab x ρ hρ j P hP
    hview (fun _ ↦ ∅) Hk (fun _ ↦ ∅) (fun _ _ ↦ ∅) (fun _ _ ↦ Finset.univ) (fun _ _ ↦ ∅)
    (fun _ _ _ _ ↦ ∅) (fun y _ s v ↦ {y - u s v}) (fun _ _ _ _ ↦ ∅)
    (fun _ _ _ _ _ ↦ rfl) (fun y r s v d ↦ by simp only [hu]) (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ hz ↦ hz.elim) (fun v y r hy hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) _
    (fun _ _ _ ↦ by simp) (fun y r v ↦ ?_) (fun _ _ _ ↦ by simp)
  · obtain ⟨s, hs, he⟩ := hk v y r hy hW
    exact ⟨s, Finset.mem_univ _, hs, by simp [← he]⟩
  · simp [Finset.card_univ]

/-- **`sum_queryWeight_hiddenMass_le` for `runtimeR`**, under `viewByOn_gameT`'s `ViewByOn` (the
ports of runtime 2), with the hidden mass `0` on the record ports. The instances above apply to
`runtimeR m₀` likewise, with `step' := recStep`. -/
theorem sum_queryWeight_hiddenMass_runtimeR_le {V : Type} [Fintype V] [DecidableEq V]
    {D : S → Type} [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)]
    (m₀ : Finset V × M) (lab : HwReg X Z (Finset V × M) → Finset S)
    (x : ((s : S) → D s) → QuantumComp Λ (recHwSpec X Z V M) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z (Finset V × M)))
      (A × QReg.of (HwReg X Z (Finset V × M))) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (runtimeR m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hh : ((s : S) → D s) → Set Z) (Hk Hk' : ((s : S) → D s) → Set X)
    (sh : Z → HwReg X Z (Finset V × M) → Finset S)
    (sk sk' : X → HwReg X Z (Finset V × M) → Finset S)
    (Fh : Z → HwReg X Z (Finset V × M) → (s : S) → ((s : S) → D s) → Finset (D s))
    (Fk Fk' : X → HwReg X Z (Finset V × M) → (s : S) → ((s : S) → D s) → Finset (D s))
    (hFh : ∀ z r s v d, Fh z r s (Function.update v s d) = Fh z r s v)
    (hFk : ∀ y r s v d, Fk y r s (Function.update v s d) = Fk y r s v)
    (hFk' : ∀ y r s v d, Fk' y r s (Function.update v s d) = Fk' y r s v)
    (hh : ∀ v z r, z ∈ Hh v → r.2.1.1 z = none → ∃ s ∈ sh z r, s ∉ lab r ∧ v s ∈ Fh z r s v)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none →
      ∃ s ∈ sk y r, s ∉ lab r ∧ v s ∈ Fk y r s v)
    (hk' : ∀ v y r, y ∈ Hk' v → r.2.1.2.2 y = none →
      ∃ s ∈ sk' y r, s ∉ lab r ∧ v s ∈ Fk' y r s v)
    (κ : ℝ≥0∞)
    (hκh : ∀ z r v, ∑ s ∈ sh z r,
      ((Fh z r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk : ∀ y r v, ∑ s ∈ sk y r,
      ((Fk y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ)
    (hκk' : ∀ y r v, ∑ s ∈ sk' y r,
      ((Fk' y r s v).card : ℝ≥0∞) * (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, (runtimeR m₀).queryWeight I (extWeight (hiddenMass (Hh v) (Hk v) (Hk' v))) (x v) (ρ v)
        j ≤
      κ * ∑ v, ENNReal.ofReal (ρ v).trace.re :=
  sum_queryWeight_hiddenMass_extend_le I m₀ (t := recSpec V M) recStep lab x ρ hρ j _
    (fun _ ↦ rfl) hview Hh Hk Hk' sh sk sk' Fh Fk Fk' hFh hFk hFk' hh hk hk' κ hκh hκk hκk'

end disclose

/-! ## The event bound with extended runtimes -/

section event

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

variable (X Z M) in
/-- The classical ports of the extended hardwired runtime: those of `hwCls` and every added port. -/
def extCls (t : QuantumOracleSpec.{0, 0}) : ((hwSpec X Z M).sum t).Port → Bool
  | .inl i => hwCls i
  | .inr _ => true

/-- An operator whose nonzero entries keep membership in `B` commutes with the event projector. -/
theorem one_kronecker_hwProjector_mul_comm (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (K : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hK : ∀ a a', K a' a ≠ 0 → (a'.2 ∈ B ↔ a.2 ∈ B)) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) * K =
      K * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) := by
  rw [hwProjector, one_kronecker_labelProjector, labelProjector]
  ext a' a
  rw [diagonal_mul, mul_diagonal]
  by_cases h : K a' a = 0
  · simp [h]
  · have hm := hK a a' h
    by_cases ha : a.2 ∈ B <;> simp [ha, hm]

/-- **A classical step keeping membership in `B` costs `0`.** -/
theorem tsum_potential_le_of_mem_iff (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] {ι : Type}
    [Fintype ι] (K : ι → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hK : ∑ r, (K r)ᴴ * K r = 1) (hB : ∀ r a a', K r a' a ≠ 0 → (a'.2 ∈ B ↔ a.2 ∈ B))
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (hσ : σ.PosSemidef) :
    ∑' r, potential (hwProjector B) (MatrixMap.conj (K r) σ) ≤
      potential (hwProjector B) σ + 0 := by
  refine (potential_kraus_le B K hK 0 (by simp) (by simp) σ hσ).trans_eq ?_
  congr 1
  have hc : ∀ r, (K r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) * K r =
      (K r)ᴴ * K r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) := fun r ↦ by
    rw [Matrix.mul_assoc, one_kronecker_hwProjector_mul_comm B (K r) (hB r), Matrix.mul_assoc]
  have hsum : ∑ r, (K r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) * K r =
      (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B := by
    rw [Finset.sum_congr rfl fun r _ ↦ hc r, ← Finset.sum_mul, hK, Matrix.one_mul]
  simp only [flipCost, hsum, sub_self]
  simp [ENNReal.zero_rpow_of_pos]

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']

omit [Fintype S] [Fintype M'] in
/-- A record port of `T` moves the register `s` to `(s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))`. -/
theorem eq_of_recKraus_ne_zero {T : Finset S} {m : Finset S × M'} {u u' : Unit}
    {s s' : HwReg X Z (Finset S × M')} (h : recKraus T m (u', s') (u, s) ≠ 0) :
    s' = (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) := by
  have h₂ := (one_kronecker_ne_zero h).2
  have h₁ := clsKraus_ne_zero h₂
  refine Prod.ext ?_ (recKraus_ne_zero h)
  by_contra hne
  exact h₁ (Matrix.one_apply_ne hne)

/-- A record port keeps the databases, hence the grade. -/
theorem querySupportedOn_recStep (T : Finset S) (r : Finset S × M') (n : ℕ)
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.1)
      (Set.Iic n) σ) :
    QuerySupportedOn (fun q : Unit × HwReg X Z (Finset S × M') ↦ dbGrade q.2.1)
      (Set.Iic (n + 1)) ((recStep (X := X) (Z := Z) T).branch r σ) := by
  rw [recStep_branch]
  refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
  rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
  exact Set.mem_Iic.mpr ((Set.mem_Iic.mp hq).trans (Nat.le_succ n))

variable (X Z S M') in
/-- **A bad set that does not read the memory label**: membership does not depend on the
recorded coordinates. -/
def LabelFree (B : Set (HwReg X Z (Finset S × M'))) : Prop :=
  ∀ (D : DbReg X Z) (W : Hw X Z) (T T' : Finset S) (m : M'),
    (D, W, (T, m)) ∈ B ↔ (D, W, (T', m)) ∈ B

/-- **A record port costs `0`** for a bad set that does not read the memory label. -/
theorem tsum_potential_recStep_le (B : Set (HwReg X Z (Finset S × M'))) [DecidablePred (· ∈ B)]
    (hB : LabelFree X Z S M' B) (T : Finset S)
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ)
    (hσ : σ.PosSemidef) :
    ∑' r, potential (hwProjector B) ((recStep (X := X) (Z := Z) T).branch r σ) ≤
      potential (hwProjector B) σ + 0 := by
  simp only [recStep_branch]
  refine tsum_potential_le_of_mem_iff B (recKraus T) (sum_recKraus T) (fun r a a' h ↦ ?_) σ hσ
  rw [eq_of_recKraus_ne_zero (u := a.1) (u' := a'.1) (s := a.2) (s' := a'.2) h]
  exact hB a.2.1 a.2.2.1 (a.2.2.2.1 ∪ T) a.2.2.2.1 a.2.2.2.2

variable [AddCommGroup X] [AddCommGroup Z] {L : LocalSig.{u, v}} {Wf : QReg → Type w}
  {A : QReg}

/-- **The graded event bound for the hardwired runtime extended by further ports**, which are
classical calls (`extCls`) keeping the grade bound (`hgT`) with costs `dT` (`hdT`):
`√w ≤ ∑_{n < q} √(6 ε n) + √(∑ d)`, the classical calls (`K`) including the added ones. The
hardwired runtime is written with its register, initial state `σ₀` and steps `s₀` (those of
`spongeHardwiredRuntime X Z W₀ m₀`), so that runtime 2 is an instance. -/
theorem rpow_inv_two_eventWeight_extend_le (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (hup : ∀ W m, UpClosed (slice B W m)) (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ B) {q K : ℕ}
    (ε : ℕ → ℝ≥0∞) (hεtop : ∀ n < q, ε n ≠ ⊤)
    (hε : ∀ n < q, ∀ W m, FreshBound (slice B W m) (n + K + 1) (ε n))
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector B) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector B) σ + dP c σ)
    (σ₀ : SubState (QReg.of (HwReg X Z M)))
    (s₀ : ∀ i, SubInstrument ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M)) ((hwSpec X Z M).Result i))
    (hσ₀ : σ₀ = (spongeHardwiredRuntime X Z W₀ m₀).init)
    (hs₀ : s₀ = (spongeHardwiredRuntime X Z W₀ m₀).step) {t : QuantumOracleSpec.{0, 0}}
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (dT : ∀ j : t.Port,
      Matrix (t.In j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    (hgT : ∀ j r n (σ : Matrix (t.In j × QReg.of (HwReg X Z M))
        (t.In j × QReg.of (HwReg X Z M)) ℂ),
      QuerySupportedOn (fun q : t.In j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1) (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1)
        (Set.Iic (n + 1)) ((step' j).branch r σ))
    (hdT : ∀ j σ, σ.PosSemidef → ∑' r, potential (hwProjector B) ((step' j).branch r σ) ≤
      potential (hwProjector B) σ + dT j σ)
    (I : L.Interp) (x : QuantumComp L ((hwSpec X Z M).sum t) Wf A)
    (hxq : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z M t i then 0 else 1) q)
    (hxK : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z M t i then 1 else 0) K)
    (ρ : SubState A) :
    ((QuantumRuntime.mk _ σ₀ s₀).extend step').eventWeight I (hwProjector B) x
        (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) ≤
      ∑ n ∈ Finset.range q, (6 * ε n) ^ (2⁻¹ : ℝ) +
        ((QuantumRuntime.mk _ σ₀ s₀).extend step').totalWeight I
          (sumWeight (hwCost dR dP) dT) x (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) := by
  subst hσ₀ hs₀
  have hρ0 : (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).posSemidef
  have htr : ENNReal.ofReal
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).trace_re_le_one
  have hz : hwProjector B * (SubState.basis (((Database.empty, Database.empty, Database.empty),
      W₀, m₀) : HwReg X Z M)).matrix = 0 := by
    rw [hwProjector, labelProjector, SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases h : ((Database.empty, Database.empty, Database.empty), W₀, m₀) = a ∧
        ((Database.empty, Database.empty, Database.empty), W₀, m₀) = b
    · rcases h with ⟨rfl, rfl⟩
      simp [hempty]
    · simp [h]
  have hzero : potential (hwProjector B)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) = 0 := by
    rw [potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply,
      ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, ENNReal.ofReal_zero]
  have hgrade : QuerySupportedOn (fun m : A × HwReg X Z M ↦ dbGrade m.2.1) (Set.Iic 0)
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) := by
    intro m m' hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  have h := rpow_inv_two_eventWeight_le_mixed ((spongeHardwiredRuntime X Z W₀ m₀).extend step') I
    (hwProjector B) (extCls X Z M t) (fun s : HwReg X Z M ↦ dbGrade s.1)
    (fun i r n σ hσ ↦ by
      rcases i with i | j
      · exact querySupportedOn_spongeHardwiredRuntime_step W₀ m₀ i r n σ hσ
      · exact hgT j r n σ hσ)
    (fun n ↦ 6 * ε n) (sumWeight (hwCost dR dP) dT) q K (fun n hn i hi σ hσ hσg ↦ ?_)
    (fun i hi σ hσ ↦ ?_) x hxq hxK hρ0 hgrade
  · refine h.trans (add_le_add (Finset.sum_le_sum fun n _ ↦ ?_)
      (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) ((congrArg (· + _) hzero).trans (zero_add _)))))
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc 6 * ε n * ENNReal.ofReal
          (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 6 * ε n * 1 := by
          gcongr
      _ = 6 * ε n := mul_one _
  · rcases i with ((p | c) | c) | j
    · have hs : ∑' r : Unit, potential (hwProjector B)
          ((((spongeHardwiredRuntime X Z W₀ m₀).extend step').step (.inl (.inl (.inl p)))).branch
            r σ) =
          potential (hwProjector B) (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) := by
        rw [tsum_fintype, Fintype.sum_unique]
        exact congrArg (potential (hwProjector B))
          (LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge W₀ m₀ p default) σ)
      exact (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le
        (rpow_inv_two_potential_spongeHardwired_le B hup (hεtop n hn) (hε n hn) W₀ m₀ p hσ hσg)
    · exact absurd hi (by simp [extCls, hwCls])
    · exact absurd hi (by simp [extCls, hwCls])
    · exact absurd hi (by simp [extCls])
  · rcases i with ((p | c) | c) | j
    · exact absurd hi (by simp [extCls, hwCls])
    · have hs : ∑' r : c.Result, potential (hwProjector B)
          ((((spongeHardwiredRuntime X Z W₀ m₀).extend step').step (.inl (.inl (.inr c)))).branch
            r σ) =
          ∑' r : c.Result, potential (hwProjector B) (MatrixMap.conj (hwReadKraus c r) σ) :=
        tsum_congr fun r ↦ congrArg (potential (hwProjector B))
          (LinearMap.congr_fun (spongeHardwiredRuntime_step_read W₀ m₀ c r) σ)
      exact hs.trans_le (hdR c σ hσ)
    · have hs : ∑' r : c.Result, potential (hwProjector B)
          ((((spongeHardwiredRuntime X Z W₀ m₀).extend step').step (.inl (.inr c))).branch
            r σ) =
          ∑' r : c.Result, potential (hwProjector B) (MatrixMap.conj (hwProgKraus c r) σ) :=
        tsum_congr fun r ↦ congrArg (potential (hwProjector B))
          (LinearMap.congr_fun (spongeHardwiredRuntime_step_prog W₀ m₀ c r) σ)
      exact hs.trans_le (hdP c σ hσ)
    · exact hdT j σ hσ

/-- **The graded event bound for the extended hardwired runtime**, squared. -/
theorem eventWeight_extend_le (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (hup : ∀ W m, UpClosed (slice B W m)) (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ B) {q K : ℕ}
    (ε : ℕ → ℝ≥0∞) (hεtop : ∀ n < q, ε n ≠ ⊤)
    (hε : ∀ n < q, ∀ W m, FreshBound (slice B W m) (n + K + 1) (ε n))
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector B) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector B) σ + dP c σ)
    (σ₀ : SubState (QReg.of (HwReg X Z M)))
    (s₀ : ∀ i, SubInstrument ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M)) ((hwSpec X Z M).Result i))
    (hσ₀ : σ₀ = (spongeHardwiredRuntime X Z W₀ m₀).init)
    (hs₀ : s₀ = (spongeHardwiredRuntime X Z W₀ m₀).step) {t : QuantumOracleSpec.{0, 0}}
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (dT : ∀ j : t.Port,
      Matrix (t.In j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    (hgT : ∀ j r n (σ : Matrix (t.In j × QReg.of (HwReg X Z M))
        (t.In j × QReg.of (HwReg X Z M)) ℂ),
      QuerySupportedOn (fun q : t.In j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1) (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1)
        (Set.Iic (n + 1)) ((step' j).branch r σ))
    (hdT : ∀ j σ, σ.PosSemidef → ∑' r, potential (hwProjector B) ((step' j).branch r σ) ≤
      potential (hwProjector B) σ + dT j σ)
    (I : L.Interp) (x : QuantumComp L ((hwSpec X Z M).sum t) Wf A)
    (hxq : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z M t i then 0 else 1) q)
    (hxK : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z M t i then 1 else 0) K)
    (ρ : SubState A) :
    ((QuantumRuntime.mk _ σ₀ s₀).extend step').eventWeight I (hwProjector B) x
        (ρ.matrix ⊗ₖ σ₀.matrix) ≤
      (∑ n ∈ Finset.range q, (6 * ε n) ^ (2⁻¹ : ℝ) +
        ((QuantumRuntime.mk _ σ₀ s₀).extend step').totalWeight I
          (sumWeight (hwCost dR dP) dT) x (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ENNReal.rpow_le_rpow (rpow_inv_two_eventWeight_extend_le B hup W₀ m₀ hempty ε hεtop
    hε dR dP hdR hdP σ₀ s₀ hσ₀ hs₀ step' dT hgT hdT I x hxq hxK ρ) (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

variable [Nonempty X] [Nonempty Z]

/-- **The graded event bound for `runtimeR`.** The record ports are classical calls of cost `0`
for a bad set that does not read the memory label (`LabelFree`); `K` counts them with the read
and program calls. -/
theorem eventWeight_runtimeR_le (B : Set (HwReg X Z (Finset S × M'))) [DecidablePred (· ∈ B)]
    (hB : LabelFree X Z S M' B) (hup : ∀ W m, UpClosed (slice B W m)) (m₀ : Finset S × M')
    (hempty : ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) ∉ B)
    {q K : ℕ} (ε : ℕ → ℝ≥0∞) (hεtop : ∀ n < q, ε n ≠ ⊤)
    (hε : ∀ n < q, ∀ W m, FreshBound (slice B W m) (n + K + 1) (ε n))
    (dR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector B) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector B)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector B) σ + dP c σ)
    (I : L.Interp) (x : QuantumComp L (recHwSpec X Z S M') Wf A)
    (hxq : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hxK : IPFunctor.IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (ρ : SubState A) :
    (runtimeR m₀).eventWeight I (hwProjector B) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      (∑ n ∈ Finset.range q, (6 * ε n) ^ (2⁻¹ : ℝ) +
        (runtimeR m₀).totalWeight I (extWeight (hwCost dR dP)) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 :=
  eventWeight_extend_le B hup (hwEmpty X Z) m₀ hempty ε hεtop hε dR dP hdR hdP (initHw X Z m₀)
    (spongeHardwiredRuntime X Z (hwEmpty X Z) m₀).step rfl rfl (t := recSpec S M') recStep
    (fun _ _ ↦ 0) (fun T r n σ hσ ↦ querySupportedOn_recStep T r n σ hσ)
    (fun T σ hσ ↦ tsum_potential_recStep_le B hB T σ hσ) I x hxq hxK ρ

end event

end Quantum.Xmss.Assembly

end
