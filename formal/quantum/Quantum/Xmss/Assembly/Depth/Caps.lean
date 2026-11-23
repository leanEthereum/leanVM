module

public import Quantum.Xmss.Assembly.Security

@[expose] public section

/-!
# The classical costs of the leanXMSS QRPM chain for every number of calls

The sequential chain bounds the prefix's classical costs (Security's `uavg_twPR_le`, `clsBound`)
only for `q ≤ 2^64`: KeyLazy's target-free flips `kfSet`, `kfW` and CostRefined's `k`, `k'`
read costs (`kapRR`) are taken on the states of database grade at most `2^68 - progCap`, which
holds along the game only for `q ≤ 2^64` (CostRun's `progCap_add_le`). Every other ingredient is
parametric in `q`: the Enc constants (`encE0`, `encBeta`, `encGamma`, through `epsQ q`, `kapS q`,
`kapR6 q`), the `RecJ` charges (`recS q`, `recR q`), the flip-value recorded mass
(`flipMassCap q`) and the reparametrization averages.

This file redoes the grade-capped steps at an arbitrary grade `T` (`kfSetAt`, `kfWAt`,
`keepE_readK_leAt`, `kapRRAt`), at the rate `epsLev T 18` in place of `2^-301`, and chains them
as the sequential proofs do (`kJumpPre_leAt`, `recJPre_leAt`, `twPR_leAt`, `encE_leAt`,
`uavg_kfGameAt_le`, `uavg_progPreR_leAt`). At the game's grade `T = nW + nD q` the rate is
`epsQ q`, so the prefix's classical costs are bounded for every `q` (`uavg_twPR_leD`) by
`clsBoundD q`, the analogue of `clsBound q`.

It also fixes the depth-aware bound `qrpmDepthBound q d` (`d' = min d q`): the event's `h` part
`√(6 · 2^-128 · 2d' · 2q)` (two `h` rounds per permutation round of total width `2q`) plus the
capacity residual `capTermD q = 4q √(6 epsQ q)` of the `4q` sequentially charged `k`, `k'` calls,
and the hybrid `√(4 · 10d' · 6q κ) + √readCap` (ten rounds per permutation round).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The capacity rate at grade `T` -/

section rate

/-- `C/|Z| ≤ epsLev T 18` for `C` at most the two capacity counts at grade `T`. -/
theorem natCast_div_card_Z_le_epsLev {T C : ℕ} (hC : C ≤ capKJ T 18 + capKJ' T 18) :
    (C : ℝ) / Fintype.card Z ≤ epsLev T 18 := by
  unfold epsLev
  exact div_le_div_of_nonneg_right (by exact_mod_cast hC) (Nat.cast_nonneg _)

/-- The averaged count bound: `|Z|⁻¹ a ≤ epsLev T 18 · b` from `a ≤ C b`. -/
theorem inv_card_Z_mul_le_epsLev {T C : ℕ} (hC : C ≤ capKJ T 18 + capKJ' T 18) {a b : ℝ≥0∞}
    (h : a ≤ C * b) : (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ ENNReal.ofReal (epsLev T 18) * b := by
  have hZ : (0 : ℝ) < Fintype.card Z := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (Fintype.card Z : ℝ≥0∞)⁻¹ * C ≤ ENNReal.ofReal (epsLev T 18) := by
    rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast C, ← ENNReal.ofReal_natCast
      (Fintype.card Z), ← ENNReal.ofReal_div_of_pos hZ]
    exact ENNReal.ofReal_le_ofReal (natCast_div_card_Z_le_epsLev hC)
  calc (Fintype.card Z : ℝ≥0∞)⁻¹ * a ≤ (Fintype.card Z : ℝ≥0∞)⁻¹ * (C * b) := by gcongr
    _ = (Fintype.card Z : ℝ≥0∞)⁻¹ * C * b := (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal (epsLev T 18) * b := by gcongr

end rate

/-! ## KeyLazy's target-free flips at grade `T` -/

section kfreeAt

attribute [local instance] badRDec

/-- **KeyLazy's `kfSet` at grade `T`**: `FlipK`, few hardwired cells, `progCap + grade ≤ T`. -/
def kfSetAt (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (a : Z) : Set (Unit × HwReg X Z Mem) :=
  {q | FlipK π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ T}

/-- **KeyLazy's `kfSet'` at grade `T`.** -/
def kfSetAt' (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (a : Z) : Set (Unit × HwReg X Z Mem) :=
  {q | FlipK' π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ T}

theorem mem_kfSetAt {T : ℕ} {π : Equiv.Perm (X × Z)} {y : X} {a : Z}
    {q : Unit × HwReg X Z Mem} :
    q ∈ kfSetAt T π y a ↔ FlipK π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧
      progCap + dbGrade q.2.1 ≤ T :=
  Iff.rfl

theorem mem_kfSetAt' {T : ℕ} {π : Equiv.Perm (X × Z)} {y : X} {a : Z}
    {q : Unit × HwReg X Z Mem} :
    q ∈ kfSetAt' T π y a ↔ FlipK' π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ progCap ∧
      progCap + dbGrade q.2.1 ≤ T :=
  Iff.rfl

/-- **KeyLazy's `kfW` at grade `T`.** -/
noncomputable def kfWAt (T : ℕ) (π : Equiv.Perm (X × Z)) :
    HwProg X Z → Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ → ℝ≥0∞
  | .programK y a, σ => diagMass (kfSetAt T π y a) σ
  | .programK' y a, σ => diagMass (kfSetAt' T π y a) σ
  | .programH _ _, _ => 0

/-- **The target-free `k` flips averaged over the value**: at most `epsLev T 18` per unit of
trace. -/
theorem uavg_kfSetAt_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSetAt T π y a) σ ≤
      ENNReal.ofReal (epsLev T 18) * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSetAt T π y a) σ ≤
      ((capKJ T 18 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSetAt T π y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := mem_kfSetAt.mp (ht a₀ ha₀)
      exact card_flipK_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (mem_kfSetAt.mp (ht a ha)).1) a₀ ha₀
  exact inv_card_Z_mul_le_epsLev (Nat.le_add_right _ _) hs

/-- **The target-free `k'` flips averaged over the value.** -/
theorem uavg_kfSetAt'_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSetAt' T π y a) σ ≤
      ENNReal.ofReal (epsLev T 18) * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSetAt' T π y a) σ ≤
      ((capKJ' T 18 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSetAt' T π y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := mem_kfSetAt'.mp (ht a₀ ha₀)
      exact card_flipK'_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (mem_kfSetAt'.mp (ht a ha)).1) a₀ ha₀
  exact inv_card_Z_mul_le_epsLev (Nat.le_add_left _ _) hs

/-- **A fresh `k`, `k'` flip at grade at most `T - progCap` is a target-free flip.** -/
theorem kFlip_le_kfWAt {T : ℕ} (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hg : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    kFlip L c σ ≤ kfWAt T L.perm c σ := by
  cases c with
  | programH z u =>
    exact (diagMass_mono_supp (S' := ∅) fun q _ h ↦ absurd h (Set.notMem_empty q.2)).trans_eq
      (diagMass_empty σ)
  | programK y a =>
    refine diagMass_mono_supp fun q hq h ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∈ kFlipSet L (.programK y a) := h
    have hs' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap :=
      hs
    have hp' : ((q.2.1.1, Function.update q.2.1.2.1 y none, q.2.1.2.2), (q.2.2.1.1,
        Function.update q.2.2.1.2.1 y (some a), q.2.2.1.2.2), q.2.2.2.2) ∈
        HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap := hp
    obtain ⟨hN, hF⟩ := flipK_facts (tgtAnti_xmssTgtHw L) hx hs' hp'
    exact mem_kfSetAt.mpr ⟨hF, hN, hg q hq⟩
  | programK' y a =>
    refine diagMass_mono_supp fun q hq h ↦ ?_
    obtain ⟨hs, hx, hp⟩ : q.2 ∈ kFlipSet L (.programK' y a) := h
    have hs' : (q.2.1, q.2.2.1, q.2.2.2.2) ∉ HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap :=
      hs
    have hp' : ((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 y none), (q.2.2.1.1,
        q.2.2.1.2.1, Function.update q.2.2.1.2.2 y (some a)), q.2.2.2.2) ∈
        HwTargetBad L.perm trunc128 (xmssTgtHw L) progCap := hp
    obtain ⟨hN, hF⟩ := flipK'_facts (tgtAnti_xmssTgtHw L) hx hs' hp'
    exact mem_kfSetAt'.mpr ⟨hF, hN, hg q hq⟩

end kfreeAt

/-! ## The target-free flips along the game, cell by cell -/

section cellsAt

attribute [local instance] badRDec

theorem kfWAt_programK (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (a : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfWAt T π (.programK y a) σ = diagMass (kfSetAt T π y a) σ :=
  rfl

theorem kfWAt_programK' (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (a : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfWAt T π (.programK' y a) σ = diagMass (kfSetAt' T π y a) σ :=
  rfl

/-- The target-free flip weight of a program port, cell by cell. -/
theorem kfWAt_split_prog (T : ℕ) (π : Equiv.Perm (X × Z)) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) :
    kfWAt T π c σ = ∑ y, (tcK y c).elim 0 (fun b ↦ diagMass (kfSetAt T π y b) σ) +
      ∑ y, (tcK' y c).elim 0 (fun b ↦ diagMass (kfSetAt' T π y b) σ) := by
  cases c with
  | programH z u =>
    show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  | programK y a =>
    have h2 : ∑ y', (tcK' y' (.programK y a)).elim 0
        (fun b ↦ diagMass (kfSetAt' T π y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK_programK_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK_programK_self, h2, add_zero, Option.elim_some,
      kfWAt_programK]
  | programK' y a =>
    have h1 : ∑ y', (tcK y' (.programK' y a)).elim 0
        (fun b ↦ diagMass (kfSetAt T π y' b) σ) = 0 :=
      Finset.sum_eq_zero fun y' _ ↦ rfl
    rw [h1, zero_add,
      Finset.sum_eq_single y (fun y' _ hy' ↦ by rw [tcK'_programK'_ne (Ne.symm hy')]; rfl)
      (fun h ↦ absurd (Finset.mem_univ y) h), tcK'_programK'_self, Option.elim_some,
      kfWAt_programK']

/-- The averaged target-free `k` flips of a program port at the cell `y`. -/
theorem uavg_kfSetAt_prog_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    (c : HwProg X Z) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ *
        ∑ a : Z, (tcK y c).elim 0 (fun _ ↦ diagMass (kfSetAt T π y a) σ) ≤
      ENNReal.ofReal (epsLev T 18) * (tcK y c).elim 0 (fun _ ↦ ENNReal.ofReal σ.trace.re) :=
  elim_avg_le (tcK y c) (fun a ↦ diagMass (kfSetAt T π y a) σ) _ _ (uavg_kfSetAt_le hπ y hσ)

/-- The averaged target-free `k'` flips of a program port at the cell `y`. -/
theorem uavg_kfSetAt'_prog_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (y : X)
    (c : HwProg X Z) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ *
        ∑ a : Z, (tcK' y c).elim 0 (fun _ ↦ diagMass (kfSetAt' T π y a) σ) ≤
      ENNReal.ofReal (epsLev T 18) * (tcK' y c).elim 0 (fun _ ↦ ENNReal.ofReal σ.trace.re) :=
  elim_avg_le (tcK' y c) (fun a ↦ diagMass (kfSetAt' T π y a) σ) _ _ (uavg_kfSetAt'_le hπ y hσ)

/-- **The target-free flip weight, cell by cell.** -/
theorem kfWAt_split (T : ℕ) (π : Equiv.Perm (X × Z)) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ) :
    extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T π)) i σ =
      ∑ y, tcW (tcK y) m0R (fun b ↦ diagMass (kfSetAt T π y b)) i σ +
        ∑ y, tcW (tcK' y) m0R (fun b ↦ diagMass (kfSetAt' T π y b)) i σ := by
  rcases i with ((p | c) | c) | T'
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp
  · exact kfWAt_split_prog T π c σ
  · show (0 : ℝ≥0∞) = ∑ _y : X, (0 : ℝ≥0∞) + ∑ _y : X, (0 : ℝ≥0∞)
    simp

variable {Ω : QReg → Type}
  (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))

/-- **The target-free flips along a run, cell by cell.** -/
theorem totalWeight_kfWAt_eq (T : ℕ) (π : Equiv.Perm (X × Z)) :
    (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T π))) x
        initR =
      ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK y) m0R (fun b ↦ diagMass (kfSetAt T π y b))) x initR +
        ∑ y, (runtimeR m0R).totalWeight .instruments
          (tcW (tcK' y) m0R (fun b ↦ diagMass (kfSetAt' T π y b))) x initR := by
  refine (congrArg (fun w ↦ (runtimeR m0R).totalWeight .instruments w x initR)
    (funext fun i ↦ funext fun σ ↦ kfWAt_split T π i σ)).trans
    ((totalWeight_add_weight (runtimeR m0R) .instruments _ _ x initR).trans ?_)
  exact congrArg₂ (· + ·)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK y) m0R (fun b ↦ diagMass (kfSetAt T π y b))) x initR)
    (totalWeight_fintype_sum (runtimeR m0R) .instruments
      (fun y ↦ tcW (tcK' y) m0R (fun b ↦ diagMass (kfSetAt' T π y b))) x initR)

/-- **The resampled `k` flips of a cell along a run**: averaged over the value, at most
`epsLev T 18` times the traces at the `k` ports of the cell. -/
theorem uavg_totalWeight_kfSetAt_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18)
    (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ ↦ diagMass (kfSetAt T π y a))) x initR ≤
      ENNReal.ofReal (epsLev T 18) * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK y) m0R (fun _ ↦ diagMass (kfSetAt T π y a))) x
      initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (ENNReal.ofReal (epsLev T 18)) (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x
          initR))
  rcases i with ((p | c) | c) | T'
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact uavg_kfSetAt_prog_le hπ y c hσ
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

/-- **The resampled `k'` flips of a cell along a run.** -/
theorem uavg_totalWeight_kfSetAt'_le {T : ℕ} {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18)
    (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSetAt' T π y a))) x initR ≤
      ENNReal.ofReal (epsLev T 18) * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSetAt' T π y a))) x
      initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (ENNReal.ofReal (epsLev T 18)) (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x
          initR))
  rcases i with ((p | c) | c) | T'
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact uavg_kfSetAt'_prog_le hπ y c hσ
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

end cellsAt

/-! ## The target-free flips averaged over the keys -/

section keyAvgAt

attribute [local instance] badRDec

theorem diagMass_kfSetAt_eq_zero (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.1 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSetAt T π y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSetAt T π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s (mem_kfSetAt.mp hq).1.1, Complex.zero_re,
      ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSetAt'_eq_zero (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ)
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.2 y = none → σ ((), s) ((), s) = 0) :
    diagMass (kfSetAt' T π y b) σ = 0 := by
  unfold diagMass
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : q ∈ kfSetAt' T π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, h s (mem_kfSetAt'.mp hq).1.1, Complex.zero_re,
      ENNReal.ofReal_zero]
  · exact Set.indicator_of_notMem hq _

theorem diagMass_kfSetAt_congr (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    {σ σ' : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.1 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSetAt T π y b) σ = diagMass (kfSetAt T π y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSetAt T π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s (mem_kfSetAt.mp hq).1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

theorem diagMass_kfSetAt'_congr (T : ℕ) (π : Equiv.Perm (X × Z)) (y : X) (b : Z)
    {σ σ' : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (h : ∀ s : HwReg X Z Mem, s.2.1.2.2 y = none → σ ((), s) ((), s) = σ' ((), s) ((), s)) :
    diagMass (kfSetAt' T π y b) σ = diagMass (kfSetAt' T π y b) σ' := by
  unfold diagMass
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : q ∈ kfSetAt' T π y b
  · obtain ⟨⟨⟩, s⟩ := q
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, h s (mem_kfSetAt'.mp hq).1.1]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

variable (T : ℕ) (A : Adversary (X × Z)) (P₀ : PublicParameter) (π₀ : Equiv.Perm (X × Z))
  (h₀ : Z → X) (v : HPos → Digest)

/-- **Resampling the `k` key at one cell** (KeyLazy's `totalWeight_kfSet_update` at grade
`T`). -/
theorem totalWeight_kfSetAt_update (y : X) (k k' : X → Z) (a : Z) :
    (runtimeR m0R).totalWeight .instruments (tcW (tcK y) m0R fun b ↦ diagMass (kfSetAt T π₀ y b))
        (gameKK A P₀ π₀ h₀ v (Function.update k y a) k') initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R fun _ ↦ diagMass (kfSetAt T π₀ y a)) (gameKK A P₀ π₀ h₀ v k k')
          initR := by
  have ht : ∀ z, z ≠ y → Function.update k y a z = k z := fun z hz ↦ by
    rw [Function.update_apply, ite_eq_right hz]
  have hrel := krel_gameT (M := Selections) (tc := tcK y) (P := P₀) (π := π₀)
    (t := (h₀, Function.update k y a, k')) (t' := (h₀, k, k')) v cwUpd
    (fun s ↦ prel_slotPorts_k (x := y) ht s v) A
  rw [Function.update_self] at hrel
  exact totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.1 y = none)
    (fun _ _ ↦ progUpdate_k_none) (fun _ _ hb W ↦ tcK_some hb W)
    (g := fun b ↦ diagMass (kfSetAt T π₀ y b)) (g' := fun _ ↦ diagMass (kfSetAt T π₀ y a))
    (fun b σ h ↦ diagMass_kfSetAt_eq_zero T π₀ y b σ h)
    (fun _ σ h ↦ diagMass_kfSetAt_eq_zero T π₀ y a σ h)
    (fun σ σ' h ↦ diagMass_kfSetAt_congr T π₀ y a h)
    _ _ hrel initR initR fun _ _ _ _ ↦ rfl

/-- **Resampling the `k'` key at one cell.** -/
theorem totalWeight_kfSetAt'_update (y : X) (k k' : X → Z) (a : Z) :
    (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun b ↦ diagMass (kfSetAt' T π₀ y b))
        (gameKK A P₀ π₀ h₀ v k (Function.update k' y a)) initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSetAt' T π₀ y a)) (gameKK A P₀ π₀ h₀ v k k')
          initR := by
  have ht : ∀ z, z ≠ y → Function.update k' y a z = k' z := fun z hz ↦ by
    rw [Function.update_apply, ite_eq_right hz]
  have hrel := krel_gameT (M := Selections) (tc := tcK' y) (P := P₀) (π := π₀)
    (t := (h₀, k, Function.update k' y a)) (t' := (h₀, k, k')) v cwUpd
    (fun s ↦ prel_slotPorts_k' (x := y) ht s v) A
  rw [Function.update_self] at hrel
  exact totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.2 y = none)
    (fun _ _ ↦ progUpdate_k'_none) (fun _ _ hb W ↦ tcK'_some hb W)
    (g := fun b ↦ diagMass (kfSetAt' T π₀ y b)) (g' := fun _ ↦ diagMass (kfSetAt' T π₀ y a))
    (fun b σ h ↦ diagMass_kfSetAt'_eq_zero T π₀ y b σ h)
    (fun _ σ h ↦ diagMass_kfSetAt'_eq_zero T π₀ y a σ h)
    (fun σ σ' h ↦ diagMass_kfSetAt'_congr T π₀ y a h)
    _ _ hrel initR initR fun _ _ _ _ ↦ rfl

/-- **The target-free flips summed over the keys `k`, `k'`**: at most `epsLev T 18` times
`progCap` per key pair, for `PermGood π 18`. -/
theorem sum_kfTotAt_le {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hπ₀ : PermGood π₀ 18) :
    ∑ k, ∑ k', (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T π₀))) (gameKK A P₀ π₀ h₀ v k k') initR ≤
      ENNReal.ofReal (epsLev T 18) * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_two_cells
    (fun k k' ↦ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T π₀))) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun b ↦ diagMass (kfSetAt T π₀ y b)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun b ↦ diagMass (kfSetAt' T π₀ y b)) (gameKK A P₀ π₀ h₀ v k k')
        initR)
    (fun _ _ ↦ (totalWeight_kfWAt_eq _ T π₀).le)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ ↦ diagMass (kfSetAt T π₀ y a)) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSetAt' T π₀ y a)) (gameKK A P₀ π₀ h₀ v k k')
        initR)
    (fun y k k' a ↦ totalWeight_kfSetAt_update T A P₀ π₀ h₀ v y k k' a)
    (fun y k k' a ↦ totalWeight_kfSetAt'_update T A P₀ π₀ h₀ v y k k' a)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (gameKK A P₀ π₀ h₀ v k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (gameKK A P₀ π₀ h₀ v k k') initR)
    (ENNReal.ofReal (epsLev T 18)) progCap
    (fun y _ _ ↦ uavg_totalWeight_kfSetAt_le _ hπ₀ y)
    (fun y _ _ ↦ uavg_totalWeight_kfSetAt'_le _ hπ₀ y)
    (fun _ _ ↦ totalWeight_kTrace_le _ (hN_prog cwUpd A hperm hsign _ v))

end keyAvgAt

/-! ## The game's target-free flips, averaged -/

section gameAt

attribute [local instance] badRDec

/-- The target-free fresh `k`, `k'` program flips of the whole game at grade `T`. -/
noncomputable def kfGameAt (T : ℕ) (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T L.perm)))
    (gameR A L) initR

/-- The target-free fresh `k`, `k'` program flips of the prefix at grade `T`. -/
noncomputable def kfPreAt (T : ℕ) (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T L.perm)))
    (prefixR A L) initR

/-- The target-free flips of the prefix are at most those of the game. -/
theorem kfPreAt_le (T : ℕ) (A : Adversary (X × Z)) (L : HonestTable) :
    kfPreAt T A L ≤ kfGameAt T A L := by
  unfold kfPreAt kfGameAt
  rw [gameR_eq]
  exact totalWeight_le_bind₂ (runtimeR m0R) .instruments _ (prefixR A L) _ initR

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The fresh `k`, `k'` flips along the game are target-free flips at grade `T`**, for
`progCap + 6q + clsCap ≤ T` (KeyLazy's `kTot_le_kfTot`). -/
theorem kTot_le_kfGameAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable) :
    kTot A L ≤ kfGameAt T A L := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z Mem (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z Mem (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound (gameR A L) (portCharge κ) (6 * q + clsCap) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((advCalls_gameR hperm hsign L).add (clsCalls_gameR hperm hsign L))
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments (gameR A L) hx
    (isChargeBound_portCharge_zero _) querySupportedOn_initR
  unfold kTot costTot kfGameAt
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun _ τ ↦ ∀ a, τ a a ≠ 0 → dbGrade a.2.1 ≤ 6 * q + clsCap)
    (fun i E σ hP a ha ↦ ?_) (fun i τ _ hok ↦ ?_) (gameR A L) initR_posSemidef hfq
  · obtain ⟨e, he⟩ : ∃ e, σ (a, e) (a, e) ≠ 0 := by
      by_contra h
      exact ha (traceRight_diag_eq_zero fun e ↦ not_not.1 fun he ↦ h ⟨e, he⟩)
    have h := (hP.2 (a, e) (a, e) he).1
    rw [Set.mem_Iic, Nat.zero_add] at h
    exact h
  · rcases i with ((p | c) | c) | T'
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl
    · dsimp only [extWeight, sumWeight, hwCost]
      exact kFlip_le_kfWAt L c fun a ha ↦ by
        have := hok a ha
        omega
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl

/-- **The averaged target-free flips of the game at grade `T`** (KeyLazy's key averaging on
KeysReparam's `keyE`): on the `PermGood` tables at most `epsLev T 18 · progCap + progCap ·
keyBadCap`. -/
theorem uavg_kfGameAt_le (T : ℕ) :
    uavg (fun L ↦ if PermGood L.perm 18 then kfGameAt T A L else 0) ≤
      ENNReal.ofReal (epsLev T 18) * progCap + progCap * keyBadCap := by
  refine (uavg_le_of_injOn keyE (r0G treeQ 18) keyE_injOn card_keyE_le _
    (fun p x ↦ if PermGood (permK p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T (permK p))))
        (gameKK A (parK p) (permK p) (hkK p) (valK p x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) (ENNReal.ofReal (epsLev T 18) * progCap)
    (fun p ↦ ?_)).trans ?_
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (permK (keyE t).1) 18 := (permK_keyE t).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp]
      unfold kfGameAt
      rw [hgame_keyE A ht, permK_keyE t]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
        (fun i σ hσ ↦ ?_) (gameR A t.1) initR_posSemidef).trans
        (totalWeight_progs_le (gameR A t.1) (progCalls_gameR hperm hsign t.1))
      rcases i with ((p | c) | c) | T'
      · exact le_rfl
      · exact le_rfl
      · dsimp only [extWeight, sumWeight, hwCost]
        cases c with
        | programH z u => exact zero_le
        | programK y a => exact diagMass_le_trace _ hσ
        | programK' y a => exact diagMass_le_trace _ hσ
      · exact le_rfl
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (permK p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T (permK p))))
          (gameKK A (parK p) (permK p) (hkK p) (valK p w) k k') initR) _ _
        fun w ↦ sum_kfTotAt_le T A (parK p) (permK p) (hkK p) (valK p w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le
  · unfold keyBadCap
    gcongr
    exact keyE_bad_le

/-- **The programs at grade `T`**, averaged over the good tables (Security's `uavg_progPreR_le`
with `kTot_le_kfGameAt`, `uavg_kfGameAt_le`). -/
theorem uavg_progPreR_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) :
    uavg (fun L ↦ if GoodL L then progPreR A L else 0) ≤
      ENNReal.ofReal (epsLev T 18) * progCap + progCap * keyBadCap := by
  have hk : uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) ≤
      ENNReal.ofReal (epsLev T 18) * progCap + progCap * keyBadCap := by
    refine (uavg_mono fun L ↦ ?_).trans (uavg_kfGameAt_le hperm hsign T)
    by_cases hπ : PermGood L.perm 18
    · rw [ite_eq_left hπ, ite_eq_left hπ]
      exact kTot_le_kfGameAt hperm hsign hT L
    · rw [ite_eq_right hπ, ite_eq_right hπ]
  refine (uavg_mono fun L ↦ ?_).trans (uavg_progTot_le_kTot hk)
  by_cases hg : GoodL L
  · rw [ite_eq_left hg, ite_eq_left hg.1.1]
    exact progPreR_le_progTot A L
  · rw [ite_eq_right hg]
    exact zero_le

end gameAt

/-! ## The jump split and the `RecJ` weight at grade `T` -/

section jumpAt

/-- **The jump states split at grade `T`** (EncPorts' `kJumpW_le`). -/
theorem kJumpW_leAt {T : ℕ} (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hc : ProgOf (tableHw L) c)
    (hsupp : ∀ q, σ q q ≠ 0 → Quantum.Sponge.HwLe q.2.2.1 (tableHw L) ∧
      dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ T) :
    kJumpW L c σ ≤ kfWAt T L.perm c σ + recJW L c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsum : ∀ (p : Unit × HwReg X Z Mem → Prop) [DecidablePred p],
      ENNReal.ofReal (∑ q, (if p q then (1 : ℝ) else 0) * (σ q q).re) =
        ∑ q, ENNReal.ofReal ((if p q then (1 : ℝ) else 0) * (σ q q).re) := fun p _ ↦
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)
  have key : ∀ S : Set (Unit × HwReg X Z Mem),
      (∀ q, σ q q ≠ 0 → KJump L c q.2 → q ∈ S ∨ RecJ L c q.2) →
      kJumpW L c σ ≤ diagMass S σ + recJW L c σ := fun S hS ↦ by
    unfold kJumpW recJW diagMass
    rw [hsum (fun q ↦ KJump L c q.2), hsum (fun q ↦ RecJ L c q.2), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · rw [h0, Complex.zero_re, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · exact ofReal_ind_mul_le S (fun a ↦ ENNReal.ofReal (σ a a).re) q rfl (hS q h0)
  cases c with
  | programH z v =>
    refine (key ∅ fun _ _ h ↦ h.elim).trans_eq ?_
    show diagMass ∅ σ + _ = (0 : ℝ≥0∞) + _
    rw [diagMass_empty]
  | programK y a =>
    refine key (kfSetAt T L.perm y a) fun q h0 h ↦ ?_
    obtain ⟨hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have h3 : (tableHw L).2.1 y = some b := hW.2.1 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc) ▸ rfl)) h2
    · exact .inl (mem_kfSetAt.mpr ⟨hF, hg1, hg2⟩)
    · exact .inr hR
  | programK' y a =>
    refine key (kfSetAt' T L.perm y a) fun q h0 h ↦ ?_
    obtain ⟨hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have h3 : (tableHw L).2.2 y = some b := hW.2.2 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc) ▸ rfl)) h2
    · exact .inl (mem_kfSetAt'.mpr ⟨hF, hg1, hg2⟩)
    · exact .inr hR

open scoped Classical in
/-- **The program ports of the `RecJ` potential at grade `T`** (RecJ's `recJW_add_prog_le`). -/
theorem recJW_add_prog_leAt {T : ℕ} (L : HonestTable) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hc : ProgOf (tableHw L) c)
    (hsupp : ∀ q, σ q q ≠ 0 → Quantum.Sponge.HwLe q.2.2.1 (tableHw L) ∧
      dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ T) :
    recJW L c σ + ∑' r, potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ))
        (MatrixMap.conj (hwProgKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ)) σ +
        (recN : ℝ≥0∞) * kfWAt T L.perm c σ := by
  have hφ0 : ∀ s : HwReg X Z Mem, 0 ≤ (recPotN L.perm recN s : ℝ) := fun s ↦ Nat.cast_nonneg _
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hne : ∀ q : Unit × HwReg X Z Mem, (σ q q).re ≠ 0 → σ q q ≠ 0 :=
    fun q h h0 ↦ h (by rw [h0, Complex.zero_re])
  rw [tsum_potential_prog_eq hφ0 c hσ, potential_diagPot_sqrt hφ0]
  cases c with
  | programH z v =>
    refine (ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programH z v) q.2) ∅
      (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programH z v) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun _ _ h ↦ h.elim) (fun q _ _ ↦ by
        rw [recPotN_progH]) (fun q _ ↦ by
        rw [recPotN_progH]
        exact le_add_of_nonneg_right (Nat.cast_nonneg _))).trans_eq ?_
    show _ + _ * diagMass ∅ σ = _ + _ * 0
    rw [diagMass_empty]
  | programK y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programK y a) q.2)
      (kfSetAt T L.perm y a) (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programK y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.1 y ≠ none → q.2.2.1.2.1 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : (tableHw L).2.1 y = some b := hW.2.1 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK_le L.perm recN y a q.2 hWa
    · exact_mod_cast recPotN_progK_add_one_le L.perm recN y a (hwKs_lt_recN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq (mem_kfSetAt.mpr ⟨hF, hg1, hg2⟩), add_zero] at hle
      exact_mod_cast hle
    · have : recPotN L.perm recN (progMap (.programK y a) q.2) ≤
          recPotN L.perm recN q.2 + recN :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this
  | programK' y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programK' y a) q.2)
      (kfSetAt' T L.perm y a) (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programK' y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.2 y ≠ none → q.2.2.1.2.2 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : (tableHw L).2.2 y = some b := hW.2.2 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK'_le L.perm recN y a q.2 hWa
    · exact_mod_cast recPotN_progK'_add_one_le L.perm recN y a (hwKs_lt_recN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq (mem_kfSetAt'.mpr ⟨hF, hg1, hg2⟩), add_zero] at hle
      exact_mod_cast hle
    · have : recPotN L.perm recN (progMap (.programK' y a) q.2) ≤
          recPotN L.perm recN q.2 + recN :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this

end jumpAt

section prefixAt

attribute [local instance] badRDec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The jump weight of the prefix splits at grade `T`** (EncPorts' `kJumpPre_le`). -/
theorem kJumpPre_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable) :
    kJumpPre A L ≤ kfPreAt T A L + recJPre A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i τ ↦ PreInv q i τ ∧ PortIn Selections (tableHw L) i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.2.2.1 (tableHw L) → τ a a = 0)
    (P := fun i E σ ↦ P i E σ ∧ hwSupp Selections m0R (tableHw L) i E σ)
    (fun i E σ h ↦ ⟨hP i E σ h.1, h.2.1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2.2 (a, e) ha⟩)
    (w' := fun i σ ↦ extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T L.perm)) i σ +
      extWeight (hwCost (fun _ _ ↦ 0) (recJW L)) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef
    (forallQueries_and hx (forallQueries_hwSupp_prefixR A L))).trans_eq
      (totalWeight_add_weight (runtimeR m0R) .instruments _ _ (prefixR A L) initR)
  rcases i with ((p | c) | c) | T'
  · exact zero_le
  · exact zero_le
  · refine kJumpW_leAt L c hσ hI.2.1 fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2, ?_⟩
    · by_contra h
      exact ha (hI.2.2 a h)
    · have h1 : dbGrade a.2.1 ≤ nD q := (hI.1.2.1 a a ha).1.1
      unfold nD at h1
      omega
  · exact zero_le

/-- **The `RecJ` weight of the challenge prefix at grade `T`** (RecJ's `recJPre_le`): on a table
with `PermGood π 18`, at most `recS q` per sponge call, `recR q` per classical call and `recN`
times the target-free fresh flips `kfPreAt T`. -/
theorem recJPre_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hπ : PermGood L.perm 18) :
    recJPre A L ≤ (ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞)) + (recN : ℝ≥0∞) * kfPreAt T A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  have hφ0 : ∀ s : HwReg X Z Mem, 0 ≤ (recPotN L.perm recN s : ℝ) := fun s ↦ Nat.cast_nonneg _
  set K := diagPot fun s : HwReg X Z Mem ↦ √(recPotN L.perm recN s : ℝ) with hK
  set wS : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re with hwS
  set wR : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0) with hwR
  set wK : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kfWAt T L.perm)) with hwK
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0R) .instruments K
    (fun i E σ ↦ P i E σ ∧ hwSupp Selections m0R (tableHw L) i E σ)
    (fun i τ ↦ PreInv q i τ ∧ PortIn Selections (tableHw L) i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.2.2.1 (tableHw L) → τ a a = 0)
    (fun i E σ h ↦ ⟨hP i E σ h.1, h.2.1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2.2 (a, e) ha⟩)
    (extWeight (hwCost (fun _ _ ↦ 0) (recJW L)))
    (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ +
      (ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ))
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef
    (forallQueries_and hx (forallQueries_hwSupp_prefixR A L))
  · have hgood : Good L.perm (union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) :=
      (good_congr (U := union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) (U' := emptyDbs)
        (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)).2 good_emptyDbs
    have h0 : potential K initR = 0 := (potential_basis_init m0R hφ0 ()).trans (by
      rw [recPotN_of_good L.perm recN (s := ((Database.empty, Database.empty, Database.empty),
        hwEmpty X Z, m0R)) hgood, Nat.cast_zero, ENNReal.ofReal_zero])
    have e := (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ)
      (fun i σ ↦ ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ)
      (prefixR A L) initR).trans (congrArg₂ (· + ·)
        (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wS (prefixR A L) initR)
        ((totalWeight_add_weight (runtimeR m0R) .instruments
          (fun i σ ↦ ENNReal.ofReal (recR q) * wR i σ)
          (fun i σ ↦ (recN : ℝ≥0∞) * wK i σ) (prefixR A L) initR).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wR (prefixR A L) initR)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wK (prefixR A L)
              initR))))
    have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR ≤
        ((6 * q : ℕ) : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m0R) .instruments
        (fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) (prefixR A L)
        (advCalls_prefixR hperm hsign L) initR_posSemidef).trans_eq
          ((congrArg (((6 * q : ℕ) : ℝ≥0∞) * ·) (ofReal_trace_basis_init m0R ())).trans
            (mul_one _))
    have hR : (runtimeR m0R).totalWeight .instruments wR (prefixR A L) initR ≤ clsCap :=
      (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((p | c) | c) | T'
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) (prefixR A L) initR_posSemidef).trans
        (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))
    calc recJPre A L
        ≤ potential K initR + (runtimeR m0R).totalWeight .instruments
          (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ +
            (ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ)) (prefixR A L) initR := h
      _ = ENNReal.ofReal (recS q) *
            (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR +
          (ENNReal.ofReal (recR q) *
            (runtimeR m0R).totalWeight .instruments wR (prefixR A L) initR +
            (recN : ℝ≥0∞) * (runtimeR m0R).totalWeight .instruments wK (prefixR A L) initR) := by
        rw [h0, zero_add, e]
      _ ≤ ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          (ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞) + (recN : ℝ≥0∞) * kfPreAt T A L) :=
        add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (add_le_add (mul_le_mul_of_nonneg_left hR zero_le) le_rfl)
      _ = _ := (add_assoc _ _ _).symm
  · rcases i with ((p | c) | c) | T'
    · have hb : ∀ r : Unit, ((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ =
          MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential K (((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (recS_nonneg q)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hS_rec L hπ p hσ hI.1)
    · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
          MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential K (((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * ENNReal.ofReal σ.trace.re + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (recR_nonneg q)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hR_rec L hπ c hσ hI.1)
    · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
          MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
      show recJW L c σ + ∑' r, potential K (((runtimeR m0R).step (.inl (.inr c))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * kfWAt T L.perm c σ))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
      refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r)))).trans
        (recJW_add_prog_leAt L c hσ hI.2.1 fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2, ?_⟩)
      · by_contra h
        exact ha (hI.2.2 a h)
      · have h1 : dbGrade a.2.1 ≤ nD q := (hI.1.2.1 a a ha).1.1
        unfold nD at h1
        omega
    · show (0 : ℝ≥0∞) + ∑' r, potential K (((runtimeR m0R).step (.inr T')).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      exact tsum_potential_recStep_diag hφ0 (fun _ _ _ _ _ ↦ rfl) T' hσ

end prefixAt

/-! ## The `k`, `k'` read costs at grade `T` -/

section readAt

attribute [local instance] badRDec

/-- **The rate of a `k`, `k'` read at grade `T`**: `epsLev T 18`, plus `2^-301` so that it
dominates CostRefined's rate. -/
noncomputable def rhoAt (T : ℕ) : ℝ := epsLev T 18 + (2 ^ 301 : ℝ)⁻¹

theorem rhoAt_nonneg (T : ℕ) : 0 ≤ rhoAt T := by
  have := epsLev_nonneg T 18
  unfold rhoAt
  positivity

/-- **The charge of a `k`, `k'` read per unit of trace at grade `T`** (CostRefined's `kapRR`
with `rhoAt T` for `2^-301`). -/
noncomputable def kapRRAt (T : ℕ) : ℝ :=
  rhoAt T + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(rhoAt T)

theorem kapRRAt_nonneg (T : ℕ) : 0 ≤ kapRRAt T := by
  have := rhoAt_nonneg T
  unfold kapRRAt
  positivity

theorem kapRR_le_kapRRAt (T : ℕ) : kapRR ≤ kapRRAt T := by
  have h : (2 ^ 301 : ℝ)⁻¹ ≤ rhoAt T := le_add_of_nonneg_left (epsLev_nonneg T 18)
  unfold kapRR kapRRAt
  gcongr

/-- **The linear charge of a read port at grade `T`**: `2 encRW + hwMoveW + kapRRAt T tr σ`. -/
noncomputable def aRWAt (T : ℕ) (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  2 * encRW L c σ + hwMoveW L c σ + ENNReal.ofReal (kapRRAt T * σ.trace.re)

theorem aRW_le_aRWAt (T : ℕ) (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    aRW L c σ ≤ aRWAt T L c σ := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  unfold aRW aRWAt
  gcongr
  exact kapRR_le_kapRRAt T

/-- **The empty-cell term of a `k` read for `BadR` at grade `T`** (CostRefined's
`keepE_readK_le`). -/
theorem keepE_readK_leAt {T : ℕ} (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    (upd : Mem → Option Z → Mem) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    keepE (BadR L progCap) (.readK x upd) σ ≤ epsLev T 18 * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (natCast_div_card_Z_le_epsLev (Nat.le_add_right (capKJ T 18) (capKJ' T 18)))
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR L progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_hwTargetBad_fillK (s := (q.2.1, q.2.2.1, q.2.2.2.2)) hB hx.2 b)
        hB)
    · exact card_filter_le_of_imp (card_flip_readK_bad_le (L := L) (N := progCap) (T := T)
        (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · exact epsLev_nonneg T 18

/-- **The empty-cell term of a `k'` read for `BadR` at grade `T`.** -/
theorem keepE_readK'_leAt {T : ℕ} (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    (upd : Mem → Option Z → Mem) {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    keepE (BadR L progCap) (.readK' x upd) σ ≤ epsLev T 18 * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (natCast_div_card_Z_le_epsLev (Nat.le_add_left (capKJ' T 18) (capKJ T 18)))
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR L progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_hwTargetBad_fillK' (s := (q.2.1, q.2.2.1, q.2.2.2.2)) hB hx.2 b)
        hB)
    · exact card_filter_le_of_imp (card_flip_readK'_bad_le (L := L) (N := progCap) (T := T)
        (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · exact epsLev_nonneg T 18

/-- **The refined cost of a template `k` read at grade `T`**: at most `kapRRAt T tr σ`. -/
theorem readCost_readKPort_leAt {T : ℕ} (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    readCost (BadR L progCap) (readKPort x) σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) :=
  readCost_le_of_keep (BadR L progCap) (readKPort x) (fun _ _ ↦ rfl) hσ (rhoAt_nonneg T)
    ((keepE_readK_leAt L hπ x _ hσ hsupp).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (Complex.nonneg_iff.1 hσ.trace_nonneg).1))

/-- **The refined cost of a template `k'` read at grade `T`.** -/
theorem readCost_readK'Port_leAt {T : ℕ} (L : HonestTable) (hπ : PermGood L.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    readCost (BadR L progCap) (readK'Port x) σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) :=
  readCost_le_of_keep (BadR L progCap) (readK'Port x) (fun _ _ ↦ rfl) hσ (rhoAt_nonneg T)
    ((keepE_readK'_leAt L hπ x _ hσ hsupp).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by positivity)) (Complex.nonneg_iff.1 hσ.trace_nonneg).1))

/-- **The refined cost of a read port at the prefix's calls at grade `T`, linearized**
(CostRefined's `dRref_le_prefix`). -/
theorem dRref_le_prefixAt {q T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hπ : PermGood L.perm 18) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) {s : ℝ} (hs : 0 < s) :
    dRref L c σ ≤ ENNReal.ofReal (1 + s) * aRWAt T L c σ +
      ENNReal.ofReal (1 + s⁻¹) * pRW L c σ := by
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hR : dRref L c σ = readCost (BadR L progCap) c σ := by
    unfold dRref readCostT
    rw [ite_eq_left hnb]
  rw [hR]
  by_cases ht : IsTrial trialUpd c
  · exact (readCost_trial_le L ht hσ hs).trans (add_le_add (mul_le_mul_of_nonneg_left
      (aRW_le_aRWAt T L c hσ) zero_le) le_rfl)
  have hsupp : ∀ a, σ a a ≠ 0 → progCap + dbGrade a.2.1 ≤ T := fun a h0 ↦ by
    have h1 : dbGrade a.2.1 ≤ nD q := (hI.2.1 a a h0).1.1
    unfold nD at h1
    omega
  have hk : readCost (BadR L progCap) c σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) := by
    rcases readOk_of_okCharge hI.1 with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
    · exact readCost_readKPort_leAt L hπ x hσ hsupp
    · exact readCost_readK'Port_leAt L hπ x hσ hsupp
    · exact absurd ht' ht
  refine hk.trans (le_trans ?_ le_self_add)
  refine (le_add_self).trans (le_mul_of_one_le_left zero_le ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end readAt

/-! ## The prefix's classical costs at grade `T` -/

section twAt

attribute [local instance] badRDec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The prefix's refined classical costs at grade `T`** (CostRefined's `twPR_le` with
`kapRRAt T` for `kapRR`). -/
theorem twPR_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hπ : PermGood L.perm 18) :
    twPR A L ≤ ((2 * encRPre A L + hwMovePre A L + ENNReal.ofReal (kapRRAt T) * clsCap) ^
      (2⁻¹ : ℝ) + (cwRecPre A L + recBadPre A L) ^ (2⁻¹ : ℝ)) ^ 2 + progPreR A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  set wa : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (aRWAt T L) fun _ _ ↦ 0)
  set wp : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (pRW L) fun _ _ ↦ 0)
  set wg : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (dPof L))
  have ha : (runtimeR m0R).totalWeight .instruments wa (prefixR A L) initR ≤
      2 * encRPre A L + hwMovePre A L + ENNReal.ofReal (kapRRAt T) * clsCap := by
    refine (totalWeight_le_lin (runtimeR m0R) .instruments wa
      (extWeight (hwCost (encRW L) fun _ _ ↦ 0)) (extWeight (hwCost (hwMoveW L) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal (kapRRAt T) *
        extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ) 2 1 (fun i σ _ ↦ ?_) (prefixR A L)
      initR_posSemidef).trans ?_
    · rcases i with ((p | c) | c) | T'
      · exact zero_le
      · show aRWAt T L c σ ≤ 2 * encRW L c σ + 1 * hwMoveW L c σ +
          ENNReal.ofReal (kapRRAt T) * ENNReal.ofReal σ.trace.re
        exact le_of_eq (by rw [one_mul, ← ENNReal.ofReal_mul (kapRRAt_nonneg T)]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
        .instruments (ENNReal.ofReal (kapRRAt T)) _ (prefixR A L) initR)).trans
        (mul_le_mul_of_nonneg_left
          (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)) zero_le))
  have hp : (runtimeR m0R).totalWeight .instruments wp (prefixR A L) initR ≤
      cwRecPre A L + recBadPre A L := by
    refine (totalWeight_le_add (runtimeR m0R) .instruments wp
      (extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0))
      (extWeight (hwCost (recBadW L) fun _ _ ↦ 0)) 1 1 (fun i σ _ ↦ ?_) (prefixR A L)
      initR_posSemidef).trans_eq ?_
    · rcases i with ((p | c) | c) | T'
      · exact zero_le
      · show pRW L c σ ≤ 1 * cwRecW Prod.snd trialUpd c σ + 1 * recBadW L c σ
        exact le_of_eq (by rw [one_mul, one_mul]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul, one_mul]
      rfl
  refine le_sq_add_of_forall_lin fun s hs ↦ ?_
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ + wg i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T'
    · exact zero_le
    · show dRref L c σ ≤ ENNReal.ofReal (1 + s) * aRWAt T L c σ +
        ENNReal.ofReal (1 + s⁻¹) * pRW L c σ + 0
      rw [add_zero]
      exact dRref_le_prefixAt hT L hπ c hσ hI hs
    · show dPof L c σ ≤ ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0 + dPof L c σ
      simp only [mul_zero, zero_add, le_refl]
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wa wp wg (ENNReal.ofReal (1 + s))
      (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixR A L) initR_posSemidef).trans ?_
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left hp zero_le)) le_rfl

end twAt

/-! ## The Enc term at grade `T` -/

/-- **The constant of the prefix's linear charge at grade `T`** (EncRefined's `encEC` with
`kapRRAt T` for `kapRR`). -/
noncomputable def encECAt (T q : ℕ) : ℝ≥0∞ :=
  2 * encE0 q + (2 * encDelta + 1) * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) +
    ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞)

/-- **The averaged programs at grade `T`**: `epsLev T 18 · progCap + progCap · keyBadCap`
(Security's `progBound` with `epsLev T 18` for `2^-301`). -/
noncomputable def progBoundAt (T : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (epsLev T 18) * progCap + progCap * keyBadCap

/-- **The averaged `RecJ` weight at grade `T`** (RecJ's `recCap` with `progBoundAt T`). -/
noncomputable def recCapAt (T q : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) + ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞)) +
    (recN : ℝ≥0∞) * progBoundAt T

/-- **The prefix's classical costs at grade `T`** (Security's `clsBound`). -/
noncomputable def clsBoundAt (T q : ℕ) : ℝ≥0∞ :=
  ((encECAt T q + 2 * encBeta q * flipMassCap q +
      2 * encGamma q * (progBoundAt T + recCapAt T q)) ^ (2⁻¹ : ℝ) +
    flipMassCap q ^ (2⁻¹ : ℝ)) ^ 2 + progBoundAt T

/-- **The prefix's classical costs for every `q`**: `clsBoundAt` at the game's grade
`nW + nD q` (rate `epsQ q`). -/
noncomputable def clsBoundD (q : ℕ) : ℝ≥0∞ := clsBoundAt (nW + nD q) q

section encAt

attribute [local instance] badRDec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The refined Enc term at grade `T`** (EncRefined's `encRPre_le_lin`). -/
theorem encRPre_le_linAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hπ : PermGood L.perm 18) :
    encRPre A L ≤ encE0 q + encBeta q * (cwRecPre A L + recBadPre A L) +
      encGamma q * (kfPreAt T A L + recJPre A L) + encDelta * offHeadPre A L := by
  have h1 := encRPre_le_cntEP hperm hsign L
  have hj := kJumpPre_leAt hperm hsign hT L
  have h3 : cntEP A L ≤ 2 ^ 22 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 22 *
      (ENNReal.ofReal (3 * ((nW + nD q : ℕ) : ℝ)) * (cwRecPre A L + recBadPre A L) +
        3 * offHeadPre A L + (ENNReal.ofReal (kapS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 q) * (clsCap : ℝ≥0∞) +
            (potCap q : ℝ≥0∞) * (kfPreAt T A L + recJPre A L))) :=
    (cntEP_le hperm hsign L hπ).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left le_self_add zero_le) le_rfl)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hj zero_le))) zero_le))
  refine h1.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 zero_le) le_rfl)
    le_rfl).trans_eq ?_)
  unfold encE0 encBeta encGamma encDelta
  ring

/-- **The prefix's linear charge at grade `T`** (EncRefined's `encE_le`). -/
theorem encE_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hπ : PermGood L.perm 18) :
    2 * encRPre A L + hwMovePre A L + ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞) ≤
      encECAt T q + 2 * encBeta q * (cwRecPre A L + recBadPre A L) +
        2 * encGamma q * (kfPreAt T A L + recJPre A L) + hwHeadPre A L := by
  have h1 := encRPre_le_linAt hperm hsign hT L hπ
  have h2 := offHeadPre_le hperm hsign L
  have h3 := hwMovePre_le hperm hsign L
  have h4 : encRPre A L ≤ encE0 q + encBeta q * (cwRecPre A L + recBadPre A L) +
      encGamma q * (kfPreAt T A L + recJPre A L) +
        encDelta * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 zero_le))
  refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h4 zero_le) h3) le_rfl).trans_eq ?_
  unfold encECAt
  ring

/-- **The prefix's linear charge at a good table at grade `T`** (Security's `encE_le_good`). -/
theorem encE_le_goodAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (L : HonestTable)
    (hg : GoodL L) :
    2 * encRPre A L + hwMovePre A L + ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞) ≤
      encECAt T q + 2 * encBeta q * (cwRecPre A L + recBadPre A L) +
        2 * encGamma q * (kfGameAt T A L + recJPre A L) := by
  have h := encE_leAt hperm hsign hT L hg.1.1
  rw [hwHeadPre_eq_zero_all hperm hsign L, add_zero] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add (kfPreAt_le T A L) le_rfl) zero_le))

/-- **The averaged `RecJ` weight at grade `T`** (RecJ's `uavg_recJPre_le`). -/
theorem uavg_recJPre_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) :
    uavg (fun L ↦ if GoodL L then recJPre A L else 0) ≤ recCapAt T q :=
  uavg_ite_le_add_mul (fun L hL ↦ recJPre_leAt hperm hsign hT L hL.1.1)
    ((uavg_mono fun L ↦ by
      by_cases hL : GoodL L
      · rw [ite_eq_left hL, ite_eq_left hL.1.1]
        exact kfPreAt_le T A L
      · rw [ite_eq_right hL]
        exact zero_le).trans (uavg_kfGameAt_le hperm hsign T))

/-- **The prefix's refined classical costs at grade `T`**, averaged over the good tables
(Security's `uavg_twPR_le`). -/
theorem uavg_twPR_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (hleaf : NoLeafReuse A) :
    uavg (fun L ↦ if GoodL L then twPR A L else 0) ≤ clsBoundAt T q := by
  have hr : uavg (fun L ↦ if GoodL L then kfGameAt T A L + recJPre A L else 0) ≤
      progBoundAt T + recCapAt T q := by
    refine (uavg_mono (g := fun L ↦ (if PermGood L.perm 18 then kfGameAt T A L else 0) +
      if GoodL L then recJPre A L else 0) fun L ↦ ?_).trans ?_
    · by_cases hg : GoodL L
      · rw [ite_eq_left hg, ite_eq_left hg.1.1, ite_eq_left hg]
      · rw [ite_eq_right hg]
        exact zero_le
    · rw [uavg_add]
      exact add_le_add (uavg_kfGameAt_le hperm hsign T) (uavg_recJPre_leAt hperm hsign hT)
  exact uavg_ite_cost_le_add (fun L hg ↦ twPR_leAt hperm hsign hT L hg.1.1)
    (encE_le_goodAt hperm hsign hT) (uavg_flipMass_le hperm hsign hleaf) hr
    (uavg_progPreR_leAt hperm hsign hT)

/-- **The prefix's refined classical costs for every `q`**, averaged over the good tables:
at most `clsBoundD q` (no range condition on `q`). -/
theorem uavg_twPR_leD (hleaf : NoLeafReuse A) :
    uavg (fun L ↦ if GoodL L then twPR A L else 0) ≤ clsBoundD q :=
  uavg_twPR_leAt hperm hsign (T := nW + nD q) (by unfold nW nD; omega) hleaf

end encAt

/-! ## The depth-aware bound -/

/-- **The capacity residual of the event bound**: the `4q` sequentially charged `k`, `k'` calls
at the capacity rate `epsQ q` each. -/
noncomputable def capTermD (q : ℕ) : ℝ≥0∞ :=
  ((4 * q : ℕ) : ℝ≥0∞) * (6 * ENNReal.ofReal (epsQ q)) ^ (2⁻¹ : ℝ)

/-- **The adversary term at depth `d`**: the `h` rounds, at most `2 min d q` of total width `2q`
at the `h` rate `2^-128` (EventPar's `√(6 ε d q)`), plus the capacity residual. -/
noncomputable def advTermD (q d : ℕ) : ℝ≥0∞ :=
  (6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
    capTermD q

/-- **The event term at depth `d`** (Security's `eventTerm` with `advTermD`, `clsBoundD`). -/
noncomputable def eventTermD (q d : ℕ) : ℝ≥0∞ :=
  (advTermD q d + verTerm q + (clsBoundD q + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 +
    readTerm + trialCap + goodTerm

/-- **The hybrid term at depth `d`**: at most `10 min d q` rounds of total hidden mass
`6q κ` (GradedPar's `√(4 d μ)`), plus the read ports' mass. -/
noncomputable def hybTermD (q d : ℕ) : ℝ≥0∞ :=
  (4 * (((10 * min d q : ℕ) : ℝ≥0∞) * (((6 * q : ℕ) : ℝ≥0∞) * kappaS))) ^ (2⁻¹ : ℝ) +
    readCap ^ (2⁻¹ : ℝ)

/-- **The depth-aware leanXMSS QRPM bound** (Security's `qrpmBound` with `eventTermD`,
`hybTermD`). -/
noncomputable def qrpmDepthBound (q d : ℕ) : ℝ≥0∞ :=
  (eventTermD q d ^ (2⁻¹ : ℝ) + hybTermD q d) ^ 2 + r0Term

end Quantum.Xmss.Assembly

end
