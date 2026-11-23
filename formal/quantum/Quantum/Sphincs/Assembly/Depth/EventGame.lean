module

public import Quantum.Sphincs.Assembly.Depth.Event
public import Quantum.Sphincs.Assembly.EventRef

@[expose] public section

/-!
# leanSPHINCS's depth-aware event bound over the whole game

The integration's event hypothesis: at data with `PermGood π 18`,
`ewR p v (gameR pol A p v) ≤ (advTermSD v q d + verTerm v q + √(twPR + verLin v q))²`, from a
parallel prefix program `xP` whose event weight bounds the prefix's and whose classical weight is
at most `twPR`.

* **The verification for any prefix amplitude** (`ewR_le_sqrt_of_fresh_amp`,
  `ewR_le_sqrt_of_prefix_amp`): EventSqrt's `ewR_le_sqrt_of_fresh` with `advTerm v q` replaced by
  any `T₀`.
* **The prefix** (`ewPrefix_le_depth_of_par`): Event's `rpow_inv_two_eventWeight_runtimeR_par_le`
  at `q_h = 2q`, `d_h = 2 min d q`, `n_k = 4q`, `K = clsCap` is at most
  `(advTermSD v q d + √twPR)²`; with the verification, `ewR_le_depth_of_par`.
* `advTermSD v q d = √(6 epsHS v · 2 min d q · 2q) + capTermSD q`, `capTermSD q` the `4q` capacity
  calls at twice the capacity rate.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs
open HashSig (Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extWeight portR keepCost
  rpow_inv_two_eventWeight_keepReads_le querySupportedOn_runtimeR_step' noBot_runtimeR
  eventWeight_eq_tsum_run₂ eventWeight_bind₂ tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq
  pow_two_rpow_inv_two)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default. -/
set_option synthInstance.maxSize 2000

/-! ## The adversary term with depth -/

/-- **The capacity term at width `q`**: `4q` calls of `k`, `k'` at twice the capacity rate below
the prefix's entries. -/
noncomputable def capTermSD (q : ℕ) : ℝ≥0∞ :=
  ((4 * q : ℕ) : ℝ≥0∞) * (6 * (2 * capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18)) ^
    (2⁻¹ : ℝ)

/-- **The adversary term at depth `d`**: the `h` rounds, at most `2 min d q` of total width `2q`
at the `h` rate `epsHS v`, plus the capacity term. -/
noncomputable def advTermSD (v : (s : HPos) → XD s) (q d : ℕ) : ℝ≥0∞ :=
  (6 * epsHS v * ((2 * min d q : ℕ) : ℝ≥0∞) * ((2 * q : ℕ) : ℝ≥0∞)) ^ (2⁻¹ : ℝ) + capTermSD q

/-! ## The verification for any prefix amplitude, and the depth-aware event bound -/

section game

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The event bound over the whole game for any prefix amplitude** (EventSqrt's
`ewR_le_sqrt_of_fresh` with `advTerm v q` replaced by `T₀`): for an event `B` with up-closed
slices and the fresh bound `verEps v q`, a prefix event weight at most `(T₀ + √T)²` gives a game
event weight at most `(T₀ + verTerm v q + √(T + verLin v q))²`. -/
theorem ewR_le_sqrt_of_fresh_amp (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (B : Set (HwReg X Z (Mem HPos))) [DecidablePred (· ∈ B)] (hup : ∀ W m, UpClosed (slice B W m))
    (hε : ∀ W m, FreshBound (slice B W m) (6 * q + clsCap + 3 * verifyBlocks + 1) (verEps v q))
    {T₀ T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR ≤
      (T₀ + T ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR ≤
      (T₀ + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).posSemidef_branch_apply
    a initR_posSemidef
  have hinit : QuerySupportedOn
      (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1)
      (Set.Iic 0) initR := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty X Z, m0R) : HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (fun i r t σ hσ ↦ querySupportedOn_runtimeR_step' m0R i r t σ hσ) .instruments
    (calls_prefixR_sph hperm hsign pol p v) hinit ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR m0R .instruments (prefixR pol A p v)
    (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le B hup m0R
    (N := 6 * q + clsCap + 3 * verifyBlocks) (verEps_ne_top v q) hε .instruments
    (realizeT v (verifyT Selections p a))
    (chg_verifyT_one_sph p v a) (chg_verifyT_nonKeep_sph p v a)
    (t := 0 + (6 * q + clsCap)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
      initR).trace.re ≤ 1 :=
    (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initR_posSemidef).trans (ENNReal.ofReal_le_one.mpr
        ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) m0R).init).trace_re_le_one)
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0R) .instruments (hwProjector B)
    (prefixR pol A p v) initR
  have hm : ∑' j, (∑' a, (if j < 3 * verifyBlocks then verEps v q else 0) *
      ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
        initR).trace.re) ^ (2⁻¹ : ℝ) ≤ verTerm v q := by
    calc _ ≤ ∑' j, ((if j < 3 * verifyBlocks then verEps v q else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTerm v q := by
          unfold verTerm
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector B)
      (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a initR) +
      ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) *
        ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a
          initR).trace.re) ≤
      (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR +
        verLin v q := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) * _
        ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps v q) * 1 := by gcongr
      _ = verLin v q := mul_one _
  have hpre' : ((runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v)
      initR + verLin v q) ^ (2⁻¹ : ℝ) ≤ T₀ + (T + verLin v q) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := T₀ ^ 2) (δ := 0) (C := verLin v q)
      (b := T) (a := (runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v)
        initR) (by
          rw [pow_two_rpow_inv_two, add_zero, add_comm]
          exact hpreT)
    rwa [pow_two_rpow_inv_two, zero_add] at h
  have hew : (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR =
      ∑' a, (runtimeR m0R).eventWeight .instruments (hwProjector B)
        (realizeT v (verifyT Selections p a))
        (((runtimeR m0R).run₂ .instruments (prefixR pol A p v)).branch a initR) := by
    rw [gameR_eq]
    exact eventWeight_bind₂ (runtimeR m0R) .instruments (hwProjector B) (prefixR pol A p v) _
      initR_posSemidef
  have hfin : (runtimeR m0R).eventWeight .instruments (hwProjector B) (gameR pol A p v) initR ^
      (2⁻¹ : ℝ) ≤ T₀ + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0R).eventWeight .instruments (hwProjector B) (prefixR pol A p v) initR +
          verLin v q) ^ (2⁻¹ : ℝ) + verTerm v q :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ T₀ + (T + verLin v q) ^ (2⁻¹ : ℝ) + verTerm v q := add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **The event bound over the whole game from a bound at the end of the prefix**, for any prefix
amplitude `T₀`: `ewR ≤ (T₀ + verTerm v q + √(T + verLin v q))²` at `PermGood π 18`. -/
theorem ewR_le_sqrt_of_prefix_amp (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {T₀ T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap))
      (prefixR pol A p v) initR ≤ (T₀ + T ^ (2⁻¹ : ℝ)) ^ 2) :
    ewR p v (gameR pol A p v) ≤ (T₀ + verTerm v q + (T + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  ewR_le_sqrt_of_fresh_amp hperm hsign pol p v (BadR p v progCap)
    (fun W m ↦ upClosed_slice_bad W m) (fun W m ↦ freshBound_slice_badR p v hπ _ W m) hpreT

omit hperm hsign in
/-- **The depth-aware event bound at the end of the prefix**: a parallel prefix program `xP`
(`2q` calls of `h` in `2 min d q` rounds, `4q` calls of `k`, `k'`, `clsCap` classical calls, no
mixed rounds) whose event weight bounds the prefix's and whose classical weight is at most
`twPR pol A p v` gives `ew ≤ (advTermSD v q d + √twPR)²`. -/
theorem ewPrefix_le_depth_of_par (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {d : ℕ} {α : Type}
    (xP : QComp (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
      (QReg.of Unit) (QReg.of Unit) α)
    (hev : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap))
      (prefixR pol A p v) initR ≤ ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight
        .instruments (hwProjector (BadR p v progCap)) xP initR)
    (htw : ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref p v) (dPof p v)))) xP
        initR ≤ twPR pol A p v)
    (hxq : IFreeM.IsChargeBound xP (portCharge (portWidth (portR X Z HPos Selections) .h))
      (2 * q))
    (hxd : IFreeM.IsChargeBound xP (portCharge (portDepth (portR X Z HPos Selections) .h))
      (2 * min d q))
    (hxk : IFreeM.IsChargeBound xP (portCharge (capWidth (portR X Z HPos Selections))) (4 * q))
    (hxK : IFreeM.IsChargeBound xP (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z (Mem HPos) (recSpec HPos Selections)))) clsCap)
    (hxm : IFreeM.IsChargeBound xP (portCharge (mixedRounds (portR X Z HPos Selections))) 0) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap)) (prefixR pol A p v)
        initR ≤ (advTermSD v q d + twPR pol A p v ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := rpow_inv_two_eventWeight_runtimeR_par_le p v hπ .instruments xP hxq hxd hxk hxK hxm
    (SubState.basis ())
  have h' : ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments
      (hwProjector (BadR p v progCap)) xP initR ^ (2⁻¹ : ℝ) ≤
      advTermSD v q d + twPR pol A p v ^ (2⁻¹ : ℝ) := by
    refine le_trans h ?_
    unfold advTermSD capTermSD
    gcongr
    exact htw
  have h2 := ENNReal.rpow_le_rpow h' (by norm_num : (0 : ℝ) ≤ 2)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h2
  exact hev.trans h2

/-- **The depth-aware event bound over the whole game** (the integration's event hypothesis): at
data with `PermGood π 18`,
`ewR p v (gameR pol A p v) ≤ (advTermSD v q d + verTerm v q + √(twPR + verLin v q))²`, from a
parallel prefix program as in `ewPrefix_le_depth_of_par`. -/
theorem ewR_le_depth_of_par (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {d : ℕ} {α : Type}
    (xP : QComp (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
      (QReg.of Unit) (QReg.of Unit) α)
    (hev : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR p v progCap))
      (prefixR pol A p v) initR ≤ ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight
        .instruments (hwProjector (BadR p v progCap)) xP initR)
    (htw : ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref p v) (dPof p v)))) xP
        initR ≤ twPR pol A p v)
    (hxq : IFreeM.IsChargeBound xP (portCharge (portWidth (portR X Z HPos Selections) .h))
      (2 * q))
    (hxd : IFreeM.IsChargeBound xP (portCharge (portDepth (portR X Z HPos Selections) .h))
      (2 * min d q))
    (hxk : IFreeM.IsChargeBound xP (portCharge (capWidth (portR X Z HPos Selections))) (4 * q))
    (hxK : IFreeM.IsChargeBound xP (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z (Mem HPos) (recSpec HPos Selections)))) clsCap)
    (hxm : IFreeM.IsChargeBound xP (portCharge (mixedRounds (portR X Z HPos Selections))) 0) :
    ewR p v (gameR pol A p v) ≤
      (advTermSD v q d + verTerm v q + (twPR pol A p v + verLin v q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  ewR_le_sqrt_of_prefix_amp hperm hsign pol p v hπ
    (ewPrefix_le_depth_of_par pol p v hπ xP hev htw hxq hxd hxk hxK hxm)

end game

end Quantum.Sphincs.Assembly

end
