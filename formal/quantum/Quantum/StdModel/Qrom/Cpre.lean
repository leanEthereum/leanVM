module

public import Quantum.StdModel.Qrom.CpreEvent
public import Quantum.StdModel.Qrom.CpreHyb

@[expose] public section

/-!
# The CPRE bound in the QROM for straight-line reductions

The QROM CPRE game of a straight-line reduction (`slRed`) is the hidden-cell hybrid of
`CpreHyb` (runtime 1 against runtime 2) plus runtime 2's win, which `CpreEvent` bounds by the
event of a cell in its target (`p2_cpre_le`).

* **The cell decoding** (`cellDec_of_cellInj`): injective step cells (`CellInj`) name their
  position and chain value.
* **Runtime 2's win** (`p2C_le`): with the game's charged calls `N = n + v` (the adversary's `n`
  hash calls; the reduction's and the decision's `v = c₀ + m k + c₁ + lenMax ch` step-cell
  reads), `p2C ≤ N² · gradeEta F`.
* **The bound** (`probAvg_cpre_slRed_le`):
  `probAvg ≤ ((n + v) √(gradeEta F) + √(4 n · n κ) + √(v κ))²`, `κ = kappaC Val F`, `F` the
  largest fiber of the step's truncation.
-/

open IPFunctor OracleComp OracleSpec Matrix
open scoped ENNReal

set_option synthInstance.maxSize 2000

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom Props HashSig
open Quantum.Xmss.Hybrid (uavg uavg_mono)
open Quantum.Sponge (portCharge)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-- **Injective step cells decode**: a step cell names its position and its chain value. -/
theorem cellDec_of_cellInj {P : Par} (h : CellInj ch P) : CellDec ch P := by
  rintro θ θ' ⟨j, ν⟩ ⟨j', ν'⟩ he
  obtain ⟨rfl, hν, hx⟩ := h j ν.1 _ j' ν'.1 _ ν.2 ν'.2 he
  obtain rfl : ν = ν' := Fin.ext hν
  exact ⟨rfl, hx⟩

/-- A step cell's read is charged `1` by `rCharge 1 1`. -/
theorem one_le_rCharge_read {P : Par} {z : HashDomain} (u : CMem ch → Option HashOutput → CMem ch)
    (hz : StepCell ch P z) : 1 ≤ rCharge (ch := ch) 1 1 P (.inl (.inl (.inr (.readH z u)))) := by
  obtain ⟨j, ν, x, hν, rfl⟩ := hz
  have h : stepRead (ch := ch) P
      (.readH (cellAt ch P j ν x) u : Quantum.Sponge.HwRead HashOutput HashDomain (CMem ch)) =
        true := by
    simp only [stepRead, decide_eq_true_eq]
    exact ⟨j, ν, x, hν, rfl⟩
  simp [rCharge, h]

section bound

variable [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] [Inhabited Val]
  {Q St S0 Fo : Type} {R : OracleSpec.{0, 0} Q}

/-- **Runtime 2's win** at `P` and `θ`: `p2C ≤ (n + v)² · gradeEta F`, `v = c₀ + m k + c₁ +
lenMax ch`, for injective step cells and truncation fibers of at most `F` values. -/
theorem p2C_le (hlen : StepLen ch) {P : Par} (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ F)
    (C : TwColl Par Tw Fn Msg Out)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → Fo → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val))
    (we : CpreQuery J Tw Fn Msg → ℕ) {c₀ m k c₁ n : ℕ}
    (hC : ∀ l t x, Common.QueryCostAtMost (C.eval romWorld l P t x) (stepW (ch := ch) P)
      (we (.eval l t x)))
    (hpre : Common.QueryCostAtMost pre (redW (ch := ch) P we) c₀)
    (hσ : ∀ st q, Common.QueryCostAtMost (σ st q) (redW (ch := ch) P we) m)
    (hpost : ∀ s0 f st, Common.QueryCostAtMost (post s0 f st) (redW (ch := ch) P we) c₁)
    (hn : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
    (hk : ∀ s0, IFreeM.IsChargeBound (adv s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k)
    (θ : (s : CSrc ch) → CD ch s) :
    p2C C P pre adv st0 σ post θ ≤
      ((n + (c₀ + m * k + c₁ + lenMax ch) : ℕ) : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (gradeEta HashOutput F) :=
  p2_cpre_le P θ hlen hinj hF (rCharge (ch := ch) 1 1 P) (fun _ ↦ le_rfl)
    (fun _ u hz ↦ one_le_rCharge_read u hz) C pre adv st0 σ post
    (chg_cpre_total C P pre adv st0 σ post we hC hpre hσ hpost hn hk θ)

/-- **The QROM CPRE bound of a straight-line reduction**: for an adversary of `n` hash calls and
`k` classical calls, a reduction whose setup, handler and output read at most `c₀`, `m` and `c₁`
step cells (evaluations charged by `we`), injective step cells and truncation fibers of at most
`F` values, `probAvg ≤ ((n + v) √(gradeEta F) + √(4 n · n κ) + √(v κ))²`,
`v = c₀ + m k + c₁ + lenMax ch`, `κ = kappaC Val F`. -/
theorem probAvg_cpre_slRed_le [Fintype Par] [SampleableType Par] [SampleableType Val]
    (C : TwColl Par Tw Fn Msg Out) (hlen : StepLen ch) (hinj : ∀ P, CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y : HashOutput ↦ ch.step.trunc y = o).card ≤ F)
    (pre : Unit → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : Unit → S0 → St) (σ : Unit → HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : Unit → S0 → Fo → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val))
    (we : Par → CpreQuery J Tw Fn Msg → ℕ) {c₀ m k c₁ n : ℕ}
    (hC : ∀ P l t x, Common.QueryCostAtMost (C.eval romWorld l P t x) (stepW (ch := ch) P)
      (we P (.eval l t x)))
    (hpre : ∀ P, Common.QueryCostAtMost (pre ()) (redW (ch := ch) P (we P)) c₀)
    (hσ : ∀ P st q, Common.QueryCostAtMost (σ () st q) (redW (ch := ch) P (we P)) m)
    (hpost : ∀ P s0 f st, Common.QueryCostAtMost (post () s0 f st) (redW (ch := ch) P (we P)) c₁)
    (hn : ∀ s0, IFreeM.IsChargeBound (adv () s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.hashCharge) n)
    (hk : ∀ s0, IFreeM.IsChargeBound (adv () s0)
      (Quantum.StdModel.cmdCharge Quantum.StdModel.callCharge) k) :
    romWorld.probAvg ((cpre romWorld ch C).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) ≤
      (((n + (c₀ + m * k + c₁ + lenMax ch) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (gradeEta HashOutput F) ^ (2⁻¹ : ℝ) +
        (4 * (n * (n * kappaC Val F))) ^ (2⁻¹ : ℝ) +
        (((c₀ + m * k + c₁ + lenMax ch : ℕ) : ℝ≥0∞) * kappaC Val F) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine (probAvg_cpre_slRed_le_hybrid C hlen (fun P ↦ cellDec_of_cellInj (hinj P)) hF pre adv
    st0 σ post we hC hpre hσ hpost hn hk).trans
    (pow_le_pow_left₀ zero_le (add_le_add (add_le_add ?_ le_rfl) le_rfl) 2)
  have hu := (uavg_mono fun P ↦ (uavg_mono fun θ ↦ p2C_le hlen (hinj P) hF C (pre ()) (adv ())
    (st0 ()) (σ ()) (post ()) (we P) (hC P) (hpre P) (hσ P) (hpost P) hn hk θ).trans
      (uavg_const_le _)).trans (uavg_const_le _)
  refine (ENNReal.rpow_le_rpow hu (by norm_num)).trans_eq ?_
  have e2 : (((2 : ℕ) : ℝ) * 2⁻¹) = 1 := by norm_num
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    e2, ENNReal.rpow_one]

end bound

end Quantum.StdModel.Qrom.CpreQ

end
