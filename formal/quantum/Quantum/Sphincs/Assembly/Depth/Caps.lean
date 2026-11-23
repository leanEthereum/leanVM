module

public import Quantum.Sphincs.Assembly.EventSide

@[expose] public section

/-!
# The classical costs of leanSPHINCS's QRPM event side for every number of calls

EventSide's `uavg_twPR_le_es` bounds the averaged prefix costs only for `q ≤ 2^64`: KeyLazy's
target-free flips (`kfPre`, `kfGame`, at grade `2^68`), CostRefined's `k`, `k'` read costs
(`kapRR`, at grade `2^68`) and the program-jump split of RecJ and EncRefined
(`totalWeight_recJW_le`, `totalWeight_kJumpW_le` at grade `2^68`) are taken on the states of
database grade at most `2^68 - progCap`, which holds along the game only for `q ≤ 2^64`
(CostRun's `progCap_add_le`). Every other ingredient is parametric in `q`: the Enc constants
(`encE0`, `encBeta`, `encGamma`, through `epsQ`, `kapS`, `kapR6`, `potCap`), the `RecJ` charges
(`rjS`, `rjR`, `recCapS`), the flip-value recorded mass (`flipCapS`, `uavg_flipMass_goodES`,
`cwReView_cf`) and the key averages.

This file redoes the grade-capped steps at an arbitrary grade `T` (leanXMSS's
`Quantum.Xmss.Assembly.Depth.Caps`), at the rate `epsLev T 18` of the target-free flips in place
of `2^-301` and the read rate `rhoAt T = 2 epsLev T 18 + 2^-301` in place of `2^-301`:

* **The target-free flips at grade `T`** (`uavg_kfSet_leAt`, `sum_kfTot_le_of_krelAt`,
  `kfGameAt`, `kfPreAt`, `kW_le_kfGameAt`, `uavg_kfPreAt_le`, `uavg_kW_leAt`);
* **the `k`, `k'` reads at grade `T`** (`keepE_readK_leAt`, `kapRRAt`, `aRWAt`,
  `dRref_le_prefixAt`, `twPR_leAt`);
* **the program-jump split at grade `T`** (`recJPre_leAt`, `uavg_recJPre_leAt`, `cntEP_leAt`,
  `encRPre_le_linAt`, `encE_leAt`);
* **the event side's classical costs** (`clsBoundAt`, `uavg_twPR_le_esAt`): at the prefix's
  grade `nW progCap + 6q + clsCap` the rate `epsLev` is EncPorts' `epsQ (6q + clsCap) progCap`,
  so the averaged costs are at most `clsBoundSD q` for every `q` (`uavg_twPR_le_esD`, with
  CwReFail's failed-search bound `cfEps`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest Message PublicParameter)
open Quantum.Xmss (X Z extProgCharge)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add diagMass diagMass_empty
  totalWeight_fintype_sum totalWeight_const_mul_weight totalWeight_le_totalWeight
  totalWeight_add_weight totalWeight_chargeTrace_le)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extWeight sumWeight extCls
  kapRR kapRR_nonneg epsLev epsLev_nonneg capKJ capKJ' tcK tcK' tcK_some tcK'_some
  progUpdate_k_none progUpdate_k'_none elim_avg_le card_flipK_le card_flipK'_le sum_two_cells
  sum_pair_le isChargeBound_mono_charge forallQueries_of_charge_step progJump progChargeR
  querySupportedOn_runtimeR_step isChargeBound_portCharge_zero traceRight_diag_eq_zero
  readCost_le_of_keep card_filter_le_of_imp totalWeight_le_lin totalWeight_le_add
  le_sq_add_of_forall_lin totalWeight_le_of_forallQueries uavg_ite_le_add_mul
  ofReal_trace_basis_init portCh tsum_potential_prog_le)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

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

/-- **The target-free `k` flips averaged over the value at grade `T`**: at most `epsLev T 18` per
unit of trace (KeyLazy's `uavg_kfSet_le`). -/
theorem uavg_kfSet_leAt {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P T : ℕ) (y : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet π P T y a) σ ≤
      ENNReal.ofReal (epsLev T 18) * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSet π P T y a) σ ≤
      ((capKJ T 18 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSet π P T y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := ht a₀ ha₀
      exact card_flipK_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (ht a ha).1) a₀ ha₀
  exact inv_card_Z_mul_le_epsLev (Nat.le_add_right _ _) hs

/-- **The target-free `k'` flips averaged over the value at grade `T`.** -/
theorem uavg_kfSet'_leAt {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P T : ℕ) (y : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, diagMass (kfSet' π P T y a) σ ≤
      ENNReal.ofReal (epsLev T 18) * ENNReal.ofReal σ.trace.re := by
  have hs : ∑ a : Z, diagMass (kfSet' π P T y a) σ ≤
      ((capKJ' T 18 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re :=
    sum_diagMass_le_card (fun a ↦ kfSet' π P T y a) _ hσ fun q _ t ht a₀ ha₀ ↦ by
      obtain ⟨-, hW, hT⟩ := ht a₀ ha₀
      exact card_flipK'_le (W := q.2.2.1) (D := q.2.1) hπ (by omega) t
        (fun a ha ↦ (ht a ha).1) a₀ ha₀
  exact inv_card_Z_mul_le_epsLev (Nat.le_add_left _ _) hs

variable {Ω : QReg → Type}
  (x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))

/-- **The resampled `k` flips of a cell along a run at grade `T`**: averaged over the value, at
most `epsLev T 18` times the traces at the `k` ports of the cell. -/
theorem uavg_totalWeight_kfSet_leAt {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P T : ℕ)
    (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π P T y a))) x initR ≤
      ENNReal.ofReal (epsLev T 18) * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK y) m0R (fun _ ↦ diagMass (kfSet π P T y a))) x
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
  · exact elim_avg_le (tcK y c) (fun a ↦ diagMass (kfSet π P T y a) σ) _ _
      (uavg_kfSet_leAt hπ P T y hσ)
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

/-- **The resampled `k'` flips of a cell along a run at grade `T`.** -/
theorem uavg_totalWeight_kfSet'_leAt {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) (P T : ℕ)
    (y : X) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ a : Z, (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π P T y a))) x initR ≤
      ENNReal.ofReal (epsLev T 18) * (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re)) x initR := by
  refine ((congrArg ((Fintype.card Z : ℝ≥0∞)⁻¹ * ·) (totalWeight_fintype_sum (runtimeR m0R)
    .instruments (fun a ↦ tcW (tcK' y) m0R (fun _ ↦ diagMass (kfSet' π P T y a))) x
      initR).symm).trans
    (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ _ x initR).symm).trans_le
    ((totalWeight_le_totalWeight (runtimeR m0R) .instruments (fun i σ hσ ↦ ?_) x
      initR_posSemidef).trans_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
        (ENNReal.ofReal (epsLev T 18)) (tcW (tcK' y) m0R (fun _ τ ↦ ENNReal.ofReal τ.trace.re))
          x initR))
  rcases i with ((p | c) | c) | T'
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]
  · exact elim_avg_le (tcK' y c) (fun a ↦ diagMass (kfSet' π P T y a) σ) _ _
      (uavg_kfSet'_leAt hπ P T y hσ)
  · show (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ _a : Z, (0 : ℝ≥0∞) ≤ ENNReal.ofReal (epsLev T 18) * 0
    rw [Finset.sum_const_zero, mul_zero, mul_zero]

end kfreeAt

/-! ## The target-free flips summed over the keys at grade `T` -/

section keySumAt

variable (π : Equiv.Perm (X × Z)) (P T : ℕ)

/-- **Resampling the `k` key at one cell** (KeyLazy's `totalWeight_kfSet_update` at grade `T`). -/
theorem totalWeight_kfSet_updateAt {Ω : QReg → Type} (y : X) (a a' : Z)
    (x x' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (h : KRel (tcK y) a a' x x') :
    (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π P T y b)) x initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π P T y a)) x' initR :=
  totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.1 y = none) (a := a) (a' := a')
    (fun _ _ ↦ progUpdate_k_none) (fun _ _ hb W ↦ tcK_some hb W)
    (g := fun b ↦ diagMass (kfSet π P T y b))
    (g' := fun _ ↦ diagMass (kfSet π P T y a))
    (fun b σ h ↦ diagMass_kfSet_eq_zero π P T y b σ h)
    (fun _ σ h ↦ diagMass_kfSet_eq_zero π P T y a σ h)
    (fun _ _ h ↦ diagMass_kfSet_congr π P T y a h)
    _ _ h initR initR fun _ _ _ _ ↦ rfl

/-- **Resampling the `k'` key at one cell** at grade `T`. -/
theorem totalWeight_kfSet'_updateAt {Ω : QReg → Type} (y : X) (a a' : Z)
    (x x' : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (h : KRel (tcK' y) a a' x x') :
    (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π P T y b)) x initR =
      (runtimeR m0R).totalWeight .instruments
        (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π P T y a)) x' initR :=
  totalWeight_tcW_eq_of_krel m0R (Fr := fun W ↦ W.2.2 y = none) (a := a) (a' := a')
    (fun _ _ ↦ progUpdate_k'_none) (fun _ _ hb W ↦ tcK'_some hb W)
    (g := fun b ↦ diagMass (kfSet' π P T y b))
    (g' := fun _ ↦ diagMass (kfSet' π P T y a))
    (fun b σ h ↦ diagMass_kfSet'_eq_zero π P T y b σ h)
    (fun _ σ h ↦ diagMass_kfSet'_eq_zero π P T y a σ h)
    (fun _ _ h ↦ diagMass_kfSet'_congr π P T y a h)
    _ _ h initR initR fun _ _ _ _ ↦ rfl

variable {π} in
/-- **The target-free flips summed over the keys at grade `T`** (KeyLazy's
`sum_kfTot_le_of_krel`): at most `epsLev T 18 · progCap` per key pair. -/
theorem sum_kfTot_le_of_krelAt {Ω : QReg → Type}
    (F : (X → Z) → (X → Z) →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Ω (QReg.of Unit))
    (hk : ∀ y k k' a, KRel (tcK y) a (k y) (F (Function.update k y a) k') (F k k'))
    (hk' : ∀ y k k' a, KRel (tcK' y) a (k' y) (F k (Function.update k' y a)) (F k k'))
    (hp : ∀ k k', IFreeM.IsChargeBound (F k k') (progChargeR HPos Selections) progCap)
    (hπ : PermGood π 18) :
    ∑ k, ∑ k', (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW π P T))) (F k k') initR ≤
      ENNReal.ofReal (epsLev T 18) * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_two_cells
    (fun k k' ↦ (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW π P T))) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun b ↦ diagMass (kfSet π P T y b)) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun b ↦ diagMass (kfSet' π P T y b)) (F k k') initR)
    (fun _ _ ↦ (totalWeight_kfW_eq π P T _).le)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ ↦ diagMass (kfSet π P T y a)) (F k k') initR)
    (fun y k k' a ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ ↦ diagMass (kfSet' π P T y a)) (F k k') initR)
    (fun y k k' a ↦ totalWeight_kfSet_updateAt π P T y a (k y) _ _ (hk y k k' a))
    (fun y k k' a ↦ totalWeight_kfSet'_updateAt π P T y a (k' y) _ _ (hk' y k k' a))
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (F k k') initR)
    (fun y k k' ↦ (runtimeR m0R).totalWeight .instruments
      (tcW (tcK' y) m0R fun _ τ ↦ ENNReal.ofReal τ.trace.re) (F k k') initR)
    (ENNReal.ofReal (epsLev T 18)) progCap
    (fun y _ _ ↦ uavg_totalWeight_kfSet_leAt _ hπ P T y)
    (fun y _ _ ↦ uavg_totalWeight_kfSet'_leAt _ hπ P T y)
    (fun k k' ↦ totalWeight_kTrace_le _ (hp k k'))

end keySumAt

/-! ## The target-free flips of the game and of its prefix at grade `T` -/

/-- **The target-free fresh flips along the realized game** with trial update `upd`, at hardwired
grade `N` and grade `T` (KeyLazy's `kfGame` at grade `T`). -/
noncomputable def kfGameAt (upd : TrialUpd Selections) (pol : DigestPolicy) (A : SAdversary)
    (N T : ℕ) (p : Pub) (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (fun _ _ ↦ 0) (kfW p.perm N T)))
    (realizeT v (gameT Selections upd pol p A)) initR

/-- **The target-free fresh flips of the challenge prefix's programs** at hardwired grade
`progCap` and grade `T` (RecJ's `kfPre` at grade `T`). -/
noncomputable def kfPreAt (pol : DigestPolicy) (A : SAdversary) (T : ℕ) (p : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments
    (extWeight (hwCost (fun _ _ ↦ 0) (kfW p.perm progCap T))) (prefixR pol A p v) initR

section sumsAt

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The target-free flips of the game summed over the keys at grade `T`**: at most
`epsLev T 18 · progCap` per key pair, for `PermGood π 18`. -/
theorem sum_kfGameAt_le (upd : TrialUpd Selections) (pol : DigestPolicy) (N T : ℕ)
    (P₀ : PublicParameter) {π : Equiv.Perm (X × Z)} (h₀ : Z → X) (v : (s : HPos) → XD s)
    (hπ : PermGood π 18) :
    ∑ k, ∑ k', kfGameAt upd pol A N T ⟨P₀, π, (h₀, k, k')⟩ v ≤
      ENNReal.ofReal (epsLev T 18) * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_kfTot_le_of_krelAt N T
    (fun k k' ↦ realizeT v (gameT Selections upd pol ⟨P₀, π, (h₀, k, k')⟩ A))
    (fun y k k' a ↦ krel_gameT_k pol A P₀ π h₀ v y k k' a upd)
    (fun y k k' a ↦ krel_gameT_k' pol A P₀ π h₀ v y k k' a upd)
    (fun _ _ ↦ hN_prog upd pol A hperm hsign _ v) hπ

/-- **The prefix's target-free flips summed over the keys at grade `T`.** -/
theorem sum_kfPreAt_le (pol : DigestPolicy) (T : ℕ) (P₀ : PublicParameter)
    {π : Equiv.Perm (X × Z)} (h₀ : Z → X) (v : (s : HPos) → XD s) (hπ : PermGood π 18) :
    ∑ k, ∑ k', kfPreAt pol A T ⟨P₀, π, (h₀, k, k')⟩ v ≤
      ENNReal.ofReal (epsLev T 18) * ∑ _k : X → Z, ∑ _k' : X → Z, (progCap : ℝ≥0∞) :=
  sum_kfTot_le_of_krelAt progCap T (fun k k' ↦ prefixR pol A ⟨P₀, π, (h₀, k, k')⟩ v)
    (fun y k k' a ↦ krel_prefixR_k pol A P₀ π h₀ v y k k' a)
    (fun y k k' a ↦ krel_prefixR_k' pol A P₀ π h₀ v y k k' a)
    (fun _ _ ↦ progCalls_prefixR hperm hsign pol _ v) hπ

/-- **ProgSafe's `kW` is target-free at grade `T`** (KeyLazy's `kW_le_kfGame`): with
`N + 6q + clsCap ≤ T` the fresh flips of `Bad (evData pub v) N` are at most `kfGameAt`. -/
theorem kW_le_kfGameAt {N T : ℕ} (hN : N + (6 * q + clsCap) ≤ T) (upd : TrialUpd Selections)
    (pol : DigestPolicy) (pub : Pub) (v : (s : HPos) → XD s)
    [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) N)] :
    kW (Bad (evData pub v) N) m0R (realizeT v (gameT Selections upd pol pub A)) initR ≤
      kfGameAt upd pol A N T pub v := by
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z (Mem HPos) (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound (realizeT v (gameT Selections upd pol pub A)) (portCharge κ)
      (6 * q + clsCap) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((hN_sponge upd pol A hperm hsign pub v).add (hN_cls upd pol A hperm hsign pub v))
  have hfq := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments _ hx
    (isChargeBound_portCharge_zero _) querySupportedOn_initR
  unfold kW kfGameAt
  refine totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun _ τ ↦ ∀ a, τ a a ≠ 0 → dbGrade a.2.1 ≤ 6 * q + clsCap)
    (fun i E σ hP a ha ↦ ?_) (fun i τ _ hok ↦ ?_) _ initR_posSemidef hfq
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
      exact kFlip_le_kfW (evData pub v) N _ c fun a ha ↦ by
        have := hok a ha
        omega
    · show (0 : ℝ≥0∞) ≤ 0
      exact le_rfl

end sumsAt

section coordsAt

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
  {Q V : Type} [Fintype Q] [Fintype V] (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z))
  (hk : Q → Z → X) (val : Q → V → (s : HPos) → XD s)
  (good : Q × (((X → Z) × (X → Z)) × V) → Prop) [DecidablePred good]
  (hgood : ∀ θ, good θ → PermGood (perm θ.1) 18)
include hperm hsign hgood

/-- **RecJ's `κ` at grade `T`** (KeyLazy's `uavg_kfPre_le`): over template data whose keys are
uniform coordinates, on a guard implying `PermGood π 18`, the averaged `kfPreAt T` is at most
`epsLev T 18 · progCap`. -/
theorem uavg_kfPreAt_le (pol : DigestPolicy) (T : ℕ) :
    uavg (fun θ : Q × (((X → Z) × (X → Z)) × V) ↦ if good θ then
      kfPreAt pol A T ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2) else 0) ≤
      ENNReal.ofReal (epsLev T 18) * progCap := by
  refine uavg_le_of_sum_le (sum_prod_le_card _ fun p ↦ ?_)
  by_cases hp : PermGood (perm p) 18
  · calc ∑ x : ((X → Z) × (X → Z)) × V, (if good (p, x) then
          kfPreAt pol A T ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val p x.2) else 0)
        ≤ ∑ x : ((X → Z) × (X → Z)) × V,
            kfPreAt pol A T ⟨par p, perm p, (hk p, x.1.1, x.1.2)⟩ (val p x.2) :=
          Finset.sum_le_sum fun x _ ↦ by
            by_cases hg : good (p, x)
            · rw [ite_eq_left hg]
            · rw [ite_eq_right hg]
              exact zero_le
      _ ≤ ENNReal.ofReal (epsLev T 18) * progCap * Fintype.card (((X → Z) × (X → Z)) × V) :=
          sum_pair_le (fun k k' w ↦ kfPreAt pol A T ⟨par p, perm p, (hk p, k, k')⟩ (val p w)) _ _
            fun w ↦ sum_kfPreAt_le hperm hsign pol T (par p) (hk p) (val p w) hp
  · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right fun hg ↦ hp (hgood _ hg)]
    exact zero_le

/-- **ProgSafe's `hk` at grade `T`** (KeyLazy's `uavg_kW_le`): with `N + 6q + clsCap ≤ T`, the
averaged fresh flips `kW` of the realized game are at most `epsLev T 18 · progCap`. -/
theorem uavg_kW_leAt {N T : ℕ} (hN : N + (6 * q + clsCap) ≤ T) (upd : TrialUpd Selections)
    (pol : DigestPolicy)
    [∀ θ : Q × (((X → Z) × (X → Z)) × V), DecidablePred (· ∈ Bad (S := HPos)
      (evData ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2)) N)] :
    uavg (fun θ : Q × (((X → Z) × (X → Z)) × V) ↦ if good θ then
      kW (Bad (evData ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ (val θ.1 θ.2.2)) N) m0R
        (realizeT (val θ.1 θ.2.2)
          (gameT Selections upd pol ⟨par θ.1, perm θ.1, (hk θ.1, θ.2.1.1, θ.2.1.2)⟩ A)) initR
      else 0) ≤ ENNReal.ofReal (epsLev T 18) * progCap := by
  refine uavg_le_of_sum_le (sum_prod_le_card _ fun p ↦ ?_)
  by_cases hp : PermGood (perm p) 18
  · refine (Finset.sum_le_sum fun x _ ↦ ?_).trans (sum_pair_le
      (fun k k' w ↦ kfGameAt upd pol A N T ⟨par p, perm p, (hk p, k, k')⟩ (val p w)) _ _
        fun w ↦ sum_kfGameAt_le hperm hsign upd pol N T (par p) (hk p) (val p w) hp)
    by_cases hg : good (p, x)
    · rw [ite_eq_left hg]
      exact kW_le_kfGameAt hperm hsign hN upd pol _ _
    · rw [ite_eq_right hg]
      exact zero_le
  · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right fun hg ↦ hp (hgood _ hg)]
    exact zero_le

end coordsAt

/-! ## The `k`, `k'` read costs at grade `T` -/

section readAt

/-- **The rate of a `k`, `k'` read at grade `T`**: twice `epsLev T 18` (Struct and Enc, and
coverage), plus `2^-301` so that it dominates CostRefined's rate. -/
noncomputable def rhoAt (T : ℕ) : ℝ := 2 * epsLev T 18 + (2 ^ 301 : ℝ)⁻¹

theorem rhoAt_nonneg (T : ℕ) : 0 ≤ rhoAt T := by
  have := epsLev_nonneg T 18
  unfold rhoAt
  positivity

/-- **The charge of a `k`, `k'` read per unit of trace at grade `T`** (CostRefined's `kapRR` with
`rhoAt T` for `2^-301`). -/
noncomputable def kapRRAt (T : ℕ) : ℝ :=
  rhoAt T + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(rhoAt T)

theorem kapRRAt_nonneg (T : ℕ) : 0 ≤ kapRRAt T := by
  have := rhoAt_nonneg T
  unfold kapRRAt
  positivity

theorem kapRR_le_kapRRAt (T : ℕ) : kapRR ≤ kapRRAt T := by
  have h : (2 ^ 301 : ℝ)⁻¹ ≤ rhoAt T :=
    le_add_of_nonneg_left (mul_nonneg zero_le_two (epsLev_nonneg T 18))
  unfold kapRR kapRRAt
  gcongr

/-- The doubled `k` count over `|Z|` is at most `rhoAt T`. -/
theorem two_capKJ_div_le_rhoAt (T : ℕ) :
    ((2 * capKJ T 18 : ℕ) : ℝ) / Fintype.card Z ≤ rhoAt T := by
  have h := natCast_div_card_Z_le_epsLev (T := T) (Nat.le_add_right (capKJ T 18) (capKJ' T 18))
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc]
  unfold rhoAt
  exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left h zero_le_two) (by positivity)

/-- The doubled `k'` count over `|Z|` is at most `rhoAt T`. -/
theorem two_capKJ'_div_le_rhoAt (T : ℕ) :
    ((2 * capKJ' T 18 : ℕ) : ℝ) / Fintype.card Z ≤ rhoAt T := by
  have h := natCast_div_card_Z_le_epsLev (T := T) (Nat.le_add_left (capKJ' T 18) (capKJ T 18))
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc]
  unfold rhoAt
  exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left h zero_le_two) (by positivity)

/-- **The linear charge of a read port at grade `T`**: `2 encRW + hwMoveW + kapRRAt T tr σ`. -/
noncomputable def aRWAt (T : ℕ) (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  2 * encRW p v c σ + hwMoveW p v c σ + ENNReal.ofReal (kapRRAt T * σ.trace.re)

theorem aRW_le_aRWAt (T : ℕ) (p : Pub) (v : (s : HPos) → XD s) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) : aRW p v c σ ≤ aRWAt T p v c σ := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  unfold aRW aRWAt
  gcongr
  exact kapRR_le_kapRRAt T

/-- **The empty-cell term of a `k` read for `BadR` at grade `T`** (CostRefined's
`keepE_readK_le`). -/
theorem keepE_readK_leAt {T : ℕ} (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (x : X) (upd : Mem HPos → Option Z → Mem HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    keepE (BadR p v progCap) (.readK x upd) σ ≤ rhoAt T * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (two_capKJ_div_le_rhoAt T)
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR p v progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_bad_fillK (s := q.2) hB hx.2 b) hB)
    · exact card_filter_le_of_imp (card_flip_readK_bad_le (d := evData p v) (N := progCap)
        (T := T) (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · exact rhoAt_nonneg T

/-- **The empty-cell term of a `k'` read for `BadR` at grade `T`.** -/
theorem keepE_readK'_leAt {T : ℕ} (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (x : X) (upd : Mem HPos → Option Z → Mem HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    keepE (BadR p v progCap) (.readK' x upd) σ ≤ rhoAt T * σ.trace.re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have htr : σ.trace.re = ∑ q, (σ q q).re := by rw [Matrix.trace, Complex.re_sum]; rfl
  rw [htr, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : σ q q = 0
  · exact le_of_eq (by rw [h0, Complex.zero_re, mul_zero, mul_zero])
  refine mul_le_mul_of_nonneg_right ?_ (hre q)
  split_ifs with hx
  · refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _))
      (two_capKJ'_div_le_rhoAt T)
    unfold flipCnt
    by_cases hB : q.2 ∈ BadR p v progCap
    · refine (Nat.le_zero.mpr ?_).trans (Nat.zero_le _)
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (iff_of_true (mem_bad_fillK' (s := q.2) hB hx.2 b) hB)
    · exact card_filter_le_of_imp (card_flip_readK'_bad_le (d := evData p v) (N := progCap)
        (T := T) (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hB (hsupp q h0) hx.2 hx.1)
        fun b hb ↦ by
          by_contra hn
          exact hb (iff_of_false hn hB)
  · exact rhoAt_nonneg T

/-- **The refined cost of a template `k` read at grade `T`**: at most `kapRRAt T tr σ`. -/
theorem readCost_readKPort_leAt {T : ℕ} (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    readCost (BadR p v progCap) (readKPort x) σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) :=
  readCost_le_of_keep (BadR p v progCap) (readKPort x) (fun _ _ ↦ rfl) hσ (rhoAt_nonneg T)
    (keepE_readK_leAt p v hπ x _ hσ hsupp)

/-- **The refined cost of a template `k'` read at grade `T`.** -/
theorem readCost_readK'Port_leAt {T : ℕ} (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hsupp : ∀ q, σ q q ≠ 0 → progCap + dbGrade q.2.1 ≤ T) :
    readCost (BadR p v progCap) (readK'Port x) σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) :=
  readCost_le_of_keep (BadR p v progCap) (readK'Port x) (fun _ _ ↦ rfl) hσ (rhoAt_nonneg T)
    (keepE_readK'_leAt p v hπ x _ hσ hsupp)

/-- **The refined cost of a read port at the prefix's calls at grade `T`, linearized**
(CostRefined's `dRref_le_prefix`). -/
theorem dRref_le_prefixAt {q T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (p : Pub)
    (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) {s : ℝ} (hs : 0 < s) :
    dRref p v c σ ≤
      ENNReal.ofReal (1 + s) * aRWAt T p v c σ + ENNReal.ofReal (1 + s⁻¹) * pRW p v c σ := by
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hR : dRref p v c σ = readCost (BadR p v progCap) c σ := by
    unfold dRref readCostT
    rw [ite_eq_left hnb]
  rw [hR]
  by_cases ht : IsTrial trialUpd c
  · exact (readCost_trial_le p v ht hσ hs).trans (add_le_add (mul_le_mul_of_nonneg_left
      (aRW_le_aRWAt T p v c hσ) zero_le) le_rfl)
  have hsupp : ∀ a, σ a a ≠ 0 → progCap + dbGrade a.2.1 ≤ T := fun a h0 ↦ by
    have h1 : dbGrade a.2.1 ≤ 6 * q + clsCap := (hI.2.1 a a h0).1.1
    omega
  have hok : ReadOk c := hI.1
  have hk : readCost (BadR p v progCap) c σ ≤ ENNReal.ofReal (kapRRAt T * σ.trace.re) := by
    rcases hok with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
    · exact readCost_readKPort_leAt p v hπ x hσ hsupp
    · exact readCost_readK'Port_leAt p v hπ x hσ hsupp
    · exact absurd ht' ht
  refine hk.trans (le_trans ?_ le_self_add)
  refine (le_add_self).trans (le_mul_of_one_le_left zero_le ?_)
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end readAt

/-! ## The prefix's classical costs at grade `T` -/

section twAt

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The prefix's refined classical costs at grade `T`** (CostRefined's `twPR_le` with `kapRRAt T`
for `kapRR`): for `progCap + 6q + clsCap ≤ T`, at data with `PermGood π 18`,
`twPR ≤ (√(2 encRPre + hwMovePre + kapRRAt T clsCap) + √(cwRecPre + recBadPre))² + progPreR`. -/
theorem twPR_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) :
    twPR pol A p v ≤ ((2 * encRPre pol A p v + hwMovePre pol A p v +
      ENNReal.ofReal (kapRRAt T) * clsCap) ^ (2⁻¹ : ℝ) +
        (cwRecPre pol A p v + recBadPre pol A p v) ^ (2⁻¹ : ℝ)) ^ 2 + progPreR pol A p v := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign pol p v
  set wa : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (aRWAt T p v) fun _ _ ↦ 0)
  set wp : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (pRW p v) fun _ _ ↦ 0)
  set wg : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (dPof p v))
  have ha : (runtimeR m0R).totalWeight .instruments wa (prefixR pol A p v) initR ≤
      2 * encRPre pol A p v + hwMovePre pol A p v + ENNReal.ofReal (kapRRAt T) * clsCap := by
    refine (totalWeight_le_lin (runtimeR m0R) .instruments wa
      (extWeight (hwCost (encRW p v) fun _ _ ↦ 0)) (extWeight (hwCost (hwMoveW p v) fun _ _ ↦ 0))
      (fun i σ ↦ ENNReal.ofReal (kapRRAt T) *
        extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ) 2 1 (fun i σ _ ↦ ?_) (prefixR pol A p v)
      initR_posSemidef).trans ?_
    · rcases i with ((sp | c) | c) | T'
      · exact zero_le
      · show aRWAt T p v c σ ≤ 2 * encRW p v c σ + 1 * hwMoveW p v c σ +
          ENNReal.ofReal (kapRRAt T) * ENNReal.ofReal σ.trace.re
        exact le_of_eq (by rw [one_mul, ← ENNReal.ofReal_mul (kapRRAt_nonneg T)]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul]
      refine add_le_add le_rfl ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
        .instruments (ENNReal.ofReal (kapRRAt T)) _ (prefixR pol A p v) initR)).trans
        (mul_le_mul_of_nonneg_left
          (totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v))
          zero_le))
  have hp : (runtimeR m0R).totalWeight .instruments wp (prefixR pol A p v) initR ≤
      cwRecPre pol A p v + recBadPre pol A p v := by
    refine (totalWeight_le_add (runtimeR m0R) .instruments wp
      (extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0))
      (extWeight (hwCost (recBadW p v) fun _ _ ↦ 0)) 1 1 (fun i σ _ ↦ ?_) (prefixR pol A p v)
      initR_posSemidef).trans_eq ?_
    · rcases i with ((sp | c) | c) | T'
      · exact zero_le
      · show pRW p v c σ ≤ 1 * cwRecW Prod.snd trialUpd c σ + 1 * recBadW p v c σ
        exact le_of_eq (by rw [one_mul, one_mul]; rfl)
      · exact zero_le
      · exact zero_le
    · rw [one_mul, one_mul]
      rfl
  refine le_sq_add_of_forall_lin fun s hs ↦ ?_
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ ENNReal.ofReal (1 + s) * wa i σ + ENNReal.ofReal (1 + s⁻¹) * wp i σ + wg i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((sp | c) | c) | T'
    · exact zero_le
    · show dRref p v c σ ≤ ENNReal.ofReal (1 + s) * aRWAt T p v c σ +
        ENNReal.ofReal (1 + s⁻¹) * pRW p v c σ + 0
      rw [add_zero]
      exact dRref_le_prefixAt hT p v hπ c hσ hI hs
    · show dPof p v c σ ≤
        ENNReal.ofReal (1 + s) * 0 + ENNReal.ofReal (1 + s⁻¹) * 0 + dPof p v c σ
      simp only [mul_zero, zero_add, le_refl]
    · exact zero_le
  · refine (totalWeight_le_lin (runtimeR m0R) .instruments _ wa wp wg (ENNReal.ofReal (1 + s))
      (ENNReal.ofReal (1 + s⁻¹)) (fun _ _ _ ↦ le_rfl) (prefixR pol A p v)
      initR_posSemidef).trans ?_
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha zero_le)
      (mul_le_mul_of_nonneg_left hp zero_le)) le_rfl

/-- **The `RecJ` weight of the challenge prefix at grade `T`** (RecJ's `recJPre_le`):
`recJPre ≤ 6q rjS + clsCap rjR + rjN progCap · kfPreAt T`. -/
theorem recJPre_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy)
    (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) :
    recJPre pol A p v ≤ ((6 * q : ℕ) * ENNReal.ofReal (rjS (6 * q + clsCap) progCap) +
      (clsCap : ℝ≥0∞) * ENNReal.ofReal (rjR (6 * q + clsCap) progCap)) +
      (rjN progCap : ℝ≥0∞) * kfPreAt pol A T p v :=
  totalWeight_recJW_le trialUpd (evData p v) hπ m0R .instruments () (prefixR pol A p v)
    hT (keyHw p) (advCalls_prefixR hperm hsign pol p v)
    (clsCalls_prefixR hperm hsign pol p v) (okChg_prefixR pol p v)
    (progCalls_prefixR hperm hsign pol p v) (staysInR_keyHw pol A p v)

/-- **The averaged `RecJ` weight at grade `T`** (RecJ's `uavg_recJPre_le`): from the averaged
bound `κ` of `kfPreAt T`, at most `recCapS q κ`. -/
theorem uavg_recJPre_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy)
    {Θ : Type} [Fintype Θ] (P : Θ → Pub) (V : Θ → (s : HPos) → XD s) (good : Θ → Prop)
    [DecidablePred good] (hgood : ∀ θ, good θ → PermGood (P θ).perm 18)
    {κ : ℝ≥0∞} (hkf : uavg (fun θ ↦ if good θ then kfPreAt pol A T (P θ) (V θ) else 0) ≤ κ) :
    uavg (fun θ ↦ if good θ then recJPre pol A (P θ) (V θ) else 0) ≤ recCapS q κ :=
  uavg_ite_le_add_mul (fun θ hθ ↦ recJPre_leAt hperm hsign hT pol (P θ) (V θ) (hgood θ hθ)) hkf

end twAt

/-! ## The Enc term at grade `T` -/

/-- **The constant of the prefix's linear charge at grade `T`** (EncRefined's `encEC` with
`kapRRAt T` for `kapRR`). -/
noncomputable def encECAt (T q : ℕ) : ℝ≥0∞ :=
  2 * encE0 q + (2 * encDelta + 1) * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) +
    ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞)

section encAt

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The refined joint count on the challenge prefix at grade `T`** (EncRefined's `cntEP_le` with
`kfPreAt T` for `kfPre`). -/
theorem cntEP_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) :
    cntEP pol A p v ≤ 2 ^ 15 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 15 *
      (ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)) * cwRecPre pol A p v +
        3 * offHeadPre pol A p v +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) *
            (kfPreAt pol A T p v + recJPre pol A p v))) := by
  obtain ⟨P, hP, hx⟩ := forallQueries_encInv (q := q) hperm hsign pol p v
  have h := totalWeight_cntEW_le cwTrialUpd_trialUpd trialKeep_trialUpd (fun _ _ _ ↦ rfl)
    (evData p v) m0R P (EncInv q) hP (cSq (6 * q + clsCap) progCap)
    (cRq (6 * q + clsCap) progCap) (progJump (encPot Prod.snd (evData p v)))
    (fun sp _ hσ hI ↦ hS_port Prod.snd (EncReadOk trialUpd) (evData p v) hπ m0R sp hσ hI)
    (fun c _ ht hσ hI ↦ hR_port Prod.snd trialUpd (evData p v) hπ m0R c ht hσ hI)
    (fun c _ _ hI ↦ readNoBot_of_noBot c hI.2.2)
    (fun c _ hσ _ ↦ tsum_potential_prog_le (encPot_nonneg Prod.snd (evData p v)) c hσ)
    .instruments () (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v)
    (progCalls_prefixR hperm hsign pol p v) hx
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  set C : ℝ := ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)
  set wM : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0)
  set wO : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (offHeadW trialUpd (evData p v)) fun _ _ ↦ 0)
  set wR : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0)
  set wJ : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kJumpW (evData p v)))
  set wS : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re
  set wX : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * wS i σ +
      ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * wR i σ +
      (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * wJ i σ
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (EncInv q) hP
    (w := portCh X Z HPos Selections (cSq (6 * q + clsCap) progCap)
      (fun c σ ↦ trialChgR Prod.snd trialUpd (evData p v) c σ + cRq (6 * q + clsCap) progCap c σ)
      (progJump (encPot Prod.snd (evData p v))))
    (w' := fun i σ ↦ ENNReal.ofReal (3 * C) * wM i σ + 3 * wO i σ + wX i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx
  · have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR pol A p v) initR ≤
        ((6 * q : ℕ) : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m0R) .instruments
        (fun i ↦ if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1)
        (prefixR pol A p v) (advCalls_prefixR hperm hsign pol p v) initR_posSemidef).trans_eq
          ((congrArg (((6 * q : ℕ) : ℝ≥0∞) * ·) (ofReal_trace_basis_init m0R ())).trans
            (mul_one _))
    have hR : (runtimeR m0R).totalWeight .instruments wR (prefixR pol A p v) initR ≤ clsCap :=
      (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((sp | c) | c) | T'
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) (prefixR pol A p v) initR_posSemidef).trans
        (totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v))
    obtain ⟨W, hWW, hxW⟩ := staysInR_keyHw pol A p v
    have hJ : (runtimeR m0R).totalWeight .instruments wJ (prefixR pol A p v) initR ≤
        kfPreAt pol A T p v + recJPre pol A p v :=
      totalWeight_kJumpW_le trialUpd (evData p v) m0R .instruments () (prefixR pol A p v)
        hT (keyHw p) (advCalls_prefixR hperm hsign pol p v)
        (clsCalls_prefixR hperm hsign pol p v) (okChg_prefixR pol p v)
        (progCalls_prefixR hperm hsign pol p v) W hWW hxW
    have hX : (runtimeR m0R).totalWeight .instruments wX (prefixR pol A p v) initR ≤
        ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) *
            (kfPreAt pol A T p v + recJPre pol A p v) :=
      (totalWeight_le_lin (runtimeR m0R) .instruments wX wS wR
        (fun i σ ↦ (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * wJ i σ) _ _ (fun _ _ _ ↦ le_rfl)
        (prefixR pol A p v) initR_posSemidef).trans
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (mul_le_mul_of_nonneg_left hR zero_le))
          ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wJ
            (prefixR pol A p v) initR)).trans (mul_le_mul_of_nonneg_left hJ zero_le)))
    exact hle.trans ((totalWeight_le_lin (runtimeR m0R) .instruments _ wM wO wX _ _
      (fun _ _ _ ↦ le_rfl) (prefixR pol A p v) initR_posSemidef).trans (add_le_add le_rfl hX))
  · rcases i with ((sp | c) | c) | T'
    · show cSq (6 * q + clsCap) progCap sp σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
          (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
            (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * 0 +
              (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * 0)
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (kapS_nonneg _ _)]
      cases sp with
      | h => exact zero_le
      | k => exact le_rfl
      | k' => exact le_rfl
    · show trialChgR Prod.snd trialUpd (evData p v) c σ + cRq (6 * q + clsCap) progCap c σ ≤
        ENNReal.ofReal (3 * C) * cwRecW Prod.snd trialUpd c σ +
          3 * offHeadW trialUpd (evData p v) c σ +
          (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
            (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
            ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * ENNReal.ofReal σ.trace.re +
              (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * 0)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact readChargeR_le Prod.snd trialUpd (EncReadOk trialUpd) (evData p v) m0R c hσ hI
    · show progJump (encPot Prod.snd (evData p v)) c σ ≤ ENNReal.ofReal (3 * C) * 0 + 3 * 0 +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) *
          (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * 0 +
            (potCap (6 * q + clsCap) progCap : ℝ≥0∞) * kJumpW (evData p v) c σ)
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, zero_add]
      exact progJump_le_port Prod.snd (EncReadOk trialUpd) (evData p v) m0R c hσ hI
    · exact zero_le

/-- **The refined Enc term at grade `T`** (EncRefined's `encRPre_le_lin`). -/
theorem encRPre_le_linAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy)
    (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) :
    encRPre pol A p v ≤ encE0 q + encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
      encGamma q * (kfPreAt pol A T p v + recJPre pol A p v) +
        encDelta * offHeadPre pol A p v := by
  have h1 := encRPre_le_cntEP hperm hsign pol p v
  have h3 : cntEP pol A p v ≤ 2 ^ 15 * ((6 * q + progCap : ℕ) : ℝ≥0∞) + 2 ^ 15 *
      (ENNReal.ofReal (3 * ((nW progCap + (6 * q + clsCap) : ℕ) : ℝ)) *
          (cwRecPre pol A p v + recBadPre pol A p v) +
        3 * offHeadPre pol A p v +
        (ENNReal.ofReal (kapS (6 * q + clsCap) progCap) * ((6 * q : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (kapR6 (6 * q + clsCap) progCap) * (clsCap : ℝ≥0∞) +
          (potCap (6 * q + clsCap) progCap : ℝ≥0∞) *
            (kfPreAt pol A T p v + recJPre pol A p v))) :=
    (cntEP_leAt hperm hsign hT pol p v hπ).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left le_self_add zero_le) le_rfl) le_rfl) zero_le))
  refine h1.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 zero_le) le_rfl)
    le_rfl).trans_eq ?_)
  unfold encE0 encBeta encGamma encDelta
  ring

/-- **The prefix's linear charge at grade `T`** (EncRefined's `encE_le` with `kapRRAt T`). -/
theorem encE_leAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18) :
    2 * encRPre pol A p v + hwMovePre pol A p v +
        ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞) ≤
      encECAt T q + 2 * encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
        2 * encGamma q * (kfPreAt pol A T p v + recJPre pol A p v) := by
  have h1 := encRPre_le_linAt hperm hsign hT pol p v hπ
  have h2 := offHeadPre_le p v hperm hsign pol
  have h3 : hwMovePre pol A p v ≤ ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞) :=
    (hwMovePre_le_offHeadPre p v hperm hsign pol).trans h2
  have h4 : encRPre pol A p v ≤ encE0 q +
      encBeta q * (cwRecPre pol A p v + recBadPre pol A p v) +
      encGamma q * (kfPreAt pol A T p v + recJPre pol A p v) +
        encDelta * (ENNReal.ofReal (2 / Fintype.card Z) * (clsCap : ℝ≥0∞)) :=
    h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 zero_le))
  refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h4 zero_le) h3) le_rfl).trans_eq ?_
  unfold encECAt
  ring

end encAt

/-! ## The event side's classical costs for every number of calls -/

/-- **The averaged target-free fresh flips at grade `T`**: `epsLev T 18 · progCap` (EventSide's
`kfCapS` with `epsLev T 18` for `2^-301`). -/
noncomputable def kfCapAt (T : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (epsLev T 18) * progCap

/-- **The averaged prefix costs at grade `T`** (EventSide's `clsBoundS` with `encECAt T`,
`kfCapAt T`). -/
noncomputable def clsBoundAt (T q : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ((encECAt T q + 2 * encBeta q * flipCapS q ε +
      2 * encGamma q * (kfCapAt T + recCapS q (kfCapAt T))) ^ (2⁻¹ : ℝ) +
    flipCapS q ε ^ (2⁻¹ : ℝ)) ^ 2 + kfCapAt T

/-- **The averaged prefix costs for every `q`**: `clsBoundAt` at the prefix's grade
`nW progCap + 6q + clsCap` (rate `epsQ (6q + clsCap) progCap`), with CwReFail's failed-search
bound `cfEps`. -/
noncomputable def clsBoundSD (q : ℕ) : ℝ≥0∞ :=
  clsBoundAt (nW progCap + (6 * q + clsCap)) q cfEps

section proofAt

attribute [local instance] badDecES

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

variable (par : PublicParameter) (perm : Equiv.Perm (X × Z)) (hk : Z → X)
  (hπ : PermGood perm 18)
include hπ

set_option synthInstance.maxSize 2000 in
/-- **The averaged fresh flips of the game at grade `T`** (EventSide's `uavg_kW_goodES`): at most
`kfCapAt T`. -/
theorem uavg_kW_goodESAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      kW (Bad (S := HPos) (evData (pubES par perm hk θ.1) θ.2) progCap) m0R
        (realizeT θ.2 (gameT Selections cwUpd strPol (pubES par perm hk θ.1) A)) initR
      else 0) ≤ kfCapAt T := by
  have h := uavg_kW_leAt hperm hsign (Q := Unit) (fun _ ↦ par) (fun _ ↦ perm) (fun _ ↦ hk)
    (fun _ w ↦ w) (fun θ ↦ GoodES par perm hk θ.2) (fun _ _ ↦ hπ) hT cwUpd strPol
  exact (uavg_snd_marg (K := Unit) _).symm.trans_le h

set_option synthInstance.maxSize 2000 in
/-- **The averaged target-free fresh flips of the prefix at grade `T`** (EventSide's
`uavg_kfPre_goodES`): at most `kfCapAt T`. -/
theorem uavg_kfPre_goodESAt (T : ℕ) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      kfPreAt strPol A T (pubES par perm hk θ.1) θ.2 else 0) ≤ kfCapAt T := by
  have h := uavg_kfPreAt_le hperm hsign (Q := Unit) (fun _ ↦ par) (fun _ ↦ perm) (fun _ ↦ hk)
    (fun _ w ↦ w) (fun θ ↦ GoodES par perm hk θ.2) (fun _ _ ↦ hπ) strPol T
  exact (uavg_snd_marg (K := Unit) _).symm.trans_le h

set_option synthInstance.maxSize 2000 in
/-- **The averaged program flips of the prefix at grade `T`** (EventSide's
`uavg_progPreR_goodES`): at most `kfCapAt T`. -/
theorem uavg_progPreR_goodESAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      progPreR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ kfCapAt T := by
  refine uavg_ite_le_of_le _ (fun θ hθ ↦ ?_) (uavg_kW_goodESAt hperm hsign par perm hk hπ hT)
  refine (progPreR_le_progW_es (A := A) (pubES par perm hk θ.1) θ.2).trans ?_
  have hρ := querySupportedOn_init_keyHeld (pubES par perm hk θ.1) m0R (A := QReg.of Unit)
    (SubState.basis ()).matrix
  exact progW_le_kW_gameT progCap cwUpd strPol (pubES par perm hk θ.1) θ.2 A m0R hθ.head
    initR_posSemidef hρ

set_option synthInstance.maxSize 2000 in
/-- **The prefix's refined classical costs averaged at grade `T`** (EventSide's
`uavg_twPR_le_es` with `twPR_leAt`, `encE_leAt`, `uavg_recJPre_leAt`): for
`progCap + 6q + clsCap ≤ T`, given the failed searches `CwReView ε`, at most `clsBoundAt T q ε`. -/
theorem uavg_twPR_le_esAt {T : ℕ} (hT : progCap + (6 * q + clsCap) ≤ T) {ε : ℝ≥0∞}
    (hre : ∀ kk, CwReView strPol A (pubES par perm hk kk) ε) :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ clsBoundAt T q ε := by
  have hkf := uavg_kfPre_goodESAt hperm hsign par perm hk hπ T
  have hrj := uavg_recJPre_leAt hperm hsign hT strPol
    (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ pubES par perm hk θ.1) (fun θ ↦ θ.2)
    (GoodES par perm hk) (fun _ _ ↦ hπ) hkf
  have htw : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      twPR strPol A (pubES par perm hk θ.1) θ.2 ≤
        ((2 * encRPre strPol A (pubES par perm hk θ.1) θ.2 +
          hwMovePre strPol A (pubES par perm hk θ.1) θ.2 +
            ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
          (cwRecPre strPol A (pubES par perm hk θ.1) θ.2 +
            recBadPre strPol A (pubES par perm hk θ.1) θ.2) ^ (2⁻¹ : ℝ)) ^ 2 +
          progPreR strPol A (pubES par perm hk θ.1) θ.2 := fun θ _ ↦
    twPR_leAt hperm hsign hT strPol (pubES par perm hk θ.1) θ.2 hπ
  have hE : ∀ θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s), GoodES par perm hk θ →
      2 * encRPre strPol A (pubES par perm hk θ.1) θ.2 +
          hwMovePre strPol A (pubES par perm hk θ.1) θ.2 +
            ENNReal.ofReal (kapRRAt T) * (clsCap : ℝ≥0∞) ≤
        encECAt T q + 2 * encBeta q * (cwRecPre strPol A (pubES par perm hk θ.1) θ.2 +
            recBadPre strPol A (pubES par perm hk θ.1) θ.2) +
          2 * encGamma q * (kfPreAt strPol A T (pubES par perm hk θ.1) θ.2 +
            recJPre strPol A (pubES par perm hk θ.1) θ.2) := fun θ _ ↦
    encE_leAt hperm hsign hT strPol (pubES par perm hk θ.1) θ.2 hπ
  exact uavg_ite_cost_le_add_sph htw hE (uavg_flipMass_goodES hperm hsign par perm hk hπ hre)
    (uavg_ite_add_le hkf hrj) (uavg_progPreR_goodESAt hperm hsign par perm hk hπ hT)

set_option synthInstance.maxSize 2000 in
/-- **The prefix's refined classical costs averaged, for every number of calls** (no range
condition on `q`): at most `clsBoundSD q` (`uavg_twPR_le_esAt` at the prefix's grade with
CwReFail's `cwReView_cf`, `ε = cfEps`). -/
theorem uavg_twPR_le_esD :
    uavg (fun θ : ((X → Z) × (X → Z)) × ((s : HPos) → XD s) ↦ if GoodES par perm hk θ then
      twPR strPol A (pubES par perm hk θ.1) θ.2 else 0) ≤ clsBoundSD q :=
  uavg_twPR_le_esAt hperm hsign par perm hk hπ (T := nW progCap + (6 * q + clsCap))
    (by unfold nW; omega) fun _ ↦ cwReView_cf hperm hsign strPol valFree_strPol _ hπ

end proofAt

end Quantum.Sphincs.Assembly

end
