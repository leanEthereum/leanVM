module

public import Quantum.Xmss.Assembly.Depth.Event
public import Quantum.Xmss.Assembly.Depth.Caps
public import Quantum.Xmss.Assembly.Depth.Sim
public import Quantum.Xmss.Assembly.Depth.Refuse

@[expose] public section

/-!
# The depth-aware event bound over the whole game

The assembly's event hypothesis: on a `PermGood` table,
`ewR (gameR A) L ≤ (advTermD q d + verTerm q + √(twPR A L + verLin q))²`, from a parallel prefix
program `xP` whose event weight bounds the prefix's and whose classical weight is at most `twPR`.

* **The verification for any prefix amplitude** (`ewR_le_sqrt_of_prefix_amp`): CostRefined's
  `ewR_le_sqrt_of_prefix` with `advTerm q` replaced by any `T₀`.
* **The capacity rate at the game's grade** (`capRateBound_le_epsLev`,
  `capRateBound_game_le_epsQ`): `capRateBound Z (progCap + (2q + 4q + clsCap + 1)) 18 ≤ epsQ q`.
* **The prefix** (`ewPrefix_le_depth_of_par`): Event's `rpow_inv_two_eventWeight_runtimeR_par_le`
  at `q_h = 2q`, `d_h = 2 min d q`, `n_k = 4q`, `K = clsCap` is at most
  `(advTermD q d + √twPR)²`; with the verification, `ewR_le_depth_of_par`.
* **The assembly's event hypothesis** (`ewR_le_depth_serialize_refusePar`): for a parallel
  adversary `Ap` of width `q` in `d` rounds, at `A := serialize (refusePar Ap)`, with Sim's
  parallel prefix `prefixRPar`, its run and weight transfers and its charges.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Quantum.Xmss Quantum.Xmss.Hybrid HashSig
  LeanXmss LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The capacity rate at the game's grade -/

/-- The capacity rate at grade `T` is at most `epsLev T 18`, the two capacity counts summed. -/
theorem capRateBound_le_epsLev (T : ℕ) :
    capRateBound Z T 18 ≤ ENNReal.ofReal (epsLev T 18) := by
  have hZ : (0 : ℝ) < Fintype.card Z := Nat.cast_pos.mpr Fintype.card_pos
  have h : ENNReal.ofReal (epsLev T 18) =
      ((capKJ T 18 + capKJ' T 18 : ℕ) : ℝ≥0∞) / Fintype.card Z := by
    unfold epsLev
    rw [ENNReal.ofReal_div_of_pos hZ, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [h]
  exact max_le
    (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.le_add_right (capKJ T 18) (capKJ' T 18))) _)
    (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.le_add_left (capKJ' T 18) (capKJ T 18))) _)

/-- **The capacity rate of the parallel prefix's fresh bounds** (`2q` calls of `h`, `4q` of `k`,
`k'`, `clsCap` classical calls) is at most `epsQ q`. -/
theorem capRateBound_game_le_epsQ (q : ℕ) :
    capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18 ≤ ENNReal.ofReal (epsQ q) := by
  have hT : progCap + (2 * q + 4 * q + clsCap + 1) = nW + nD q := by
    unfold nW nD
    omega
  rw [hT]
  exact capRateBound_le_epsLev _

/-! ## The verification for any prefix amplitude, and the depth-aware event bound -/

section event

attribute [local instance] badRDec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The event bound over the whole game from a bound at the end of the prefix**, for any prefix
amplitude `T₀` (CostRefined's `ewR_le_sqrt_of_prefix` with `advTerm q` replaced by `T₀`). -/
theorem ewR_le_sqrt_of_prefix_amp (L : HonestTable) (hπ : PermGood L.perm 18) {T₀ T : ℝ≥0∞}
    (hpreT : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L)
      initR ≤ (T₀ + T ^ (2⁻¹ : ℝ)) ^ 2) :
    ewR (gameR A) L ≤ (T₀ + verTerm q + (T + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0R).run₂ .instruments (prefixR A L)).posSemidef_branch_apply a
    initR_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (querySupportedOn_runtimeR_step m0R) .instruments (calls_prefixR hperm hsign L)
    querySupportedOn_initR ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR m0R .instruments (prefixR A L) (SubState.basis ()).matrix
    ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadR L progCap)
    (fun W m ↦ upClosed_slice_bad W m.2) m0R (N := 6 * q + clsCap + 3 * verifyBlocks)
    (verEps_ne_top q) (fun W m ↦ freshBound_slice_badR L hπ _ W m) .instruments
    (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
    (chg_verifyT_one (pubOf L) (valueAt L) a) (chg_verifyT_nonKeep (pubOf L) (valueAt L) a)
    (t := 0 + (6 * q + clsCap)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
      initR).trace.re ≤ 1 :=
    (((runtimeR m0R).run₂ .instruments (prefixR A L)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initR_posSemidef).trans ofReal_trace_initR_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0R) .instruments
    (hwProjector (BadR L progCap)) (prefixR A L) initR
  have hm : ∑' j, (∑' a, (if j < 3 * verifyBlocks then verEps q else 0) *
      ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
        initR).trace.re) ^ (2⁻¹ : ℝ) ≤ verTerm q := by
    calc _ ≤ ∑' j, ((if j < 3 * verifyBlocks then verEps q else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTerm q := by
          unfold verTerm
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadR L progCap))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) +
      ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) *
        ENNReal.ofReal (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a
          initR).trace.re) ≤
      (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR +
        verLin q := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * _
        ≤ ((3 * verifyBlocks : ℕ) : ℝ≥0∞) * keepCost X Z (verEps q) * 1 := by
          gcongr
      _ = verLin q := mul_one _
  have hpre' : ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
      (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) ≤
      T₀ + (T + verLin q) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := T₀ ^ 2) (δ := 0) (C := verLin q)
      (b := T) (a := (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
        (prefixR A L) initR) (by
          rw [pow_two_rpow_inv_two, add_zero, add_comm]
          exact hpreT)
    rwa [pow_two_rpow_inv_two, zero_add] at h
  have hew : ewR (gameR A) L = ∑' a, (runtimeR m0R).eventWeight .instruments
      (hwProjector (BadR L progCap)) (realizeT (valueAt L) (verifyT Selections (pubOf L) a))
      (((runtimeR m0R).run₂ .instruments (prefixR A L)).branch a initR) := by
    unfold ewR
    rw [gameR_eq]
    exact eventWeight_bind₂ (runtimeR m0R) .instruments (hwProjector (BadR L progCap))
      (prefixR A L) _ initR_posSemidef
  have hfin : ewR (gameR A) L ^ (2⁻¹ : ℝ) ≤ T₀ + verTerm q + (T + verLin q) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
          (prefixR A L) initR + verLin q) ^ (2⁻¹ : ℝ) + verTerm q :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ T₀ + (T + verLin q) ^ (2⁻¹ : ℝ) + verTerm q := add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

omit hperm hsign in
/-- **The depth-aware event bound at the end of the prefix**: a parallel prefix program `xP`
(`2q` calls of `h` in `2 min d q` rounds, `4q` calls of `k`, `k'`, `clsCap` classical calls, no
mixed rounds) whose event weight bounds the prefix's and whose classical weight is at most
`twPR A L` gives `ew ≤ (advTermD q d + √twPR)²`. -/
theorem ewPrefix_le_depth_of_par (L : HonestTable) (hπ : PermGood L.perm 18) {d : ℕ} {α : Type}
    (xP : QComp (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
      (QReg.of Unit) (QReg.of Unit) α)
    (hev : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L)
      initR ≤ ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments
        (hwProjector (BadR L progCap)) xP initR)
    (htw : ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L)))) xP initR ≤
        twPR A L)
    (hxq : IFreeM.IsChargeBound xP (portCharge (portWidth (portR X Z HPos Selections) .h))
      (2 * q))
    (hxd : IFreeM.IsChargeBound xP (portCharge (portDepth (portR X Z HPos Selections) .h))
      (2 * min d q))
    (hxk : IFreeM.IsChargeBound xP (portCharge (capWidth (portR X Z HPos Selections))) (4 * q))
    (hxK : IFreeM.IsChargeBound xP (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) clsCap)
    (hxm : IFreeM.IsChargeBound xP (portCharge (mixedRounds (portR X Z HPos Selections))) 0) :
    (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L) initR ≤
      (advTermD q d + twPR A L ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := rpow_inv_two_eventWeight_runtimeR_par_le L hπ .instruments xP hxq hxd hxk hxK hxm
    (SubState.basis ())
  have hcap : 6 * capRateBound Z (progCap + (2 * q + 4 * q + clsCap + 1)) 18 ≤
      6 * ENNReal.ofReal (epsQ q) := by
    gcongr
    exact capRateBound_game_le_epsQ q
  have h' : ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments
      (hwProjector (BadR L progCap)) xP initR ^ (2⁻¹ : ℝ) ≤
      advTermD q d + twPR A L ^ (2⁻¹ : ℝ) := by
    refine le_trans h ?_
    unfold advTermD capTermD
    gcongr
    exact htw
  have h2 := ENNReal.rpow_le_rpow h' (by norm_num : (0 : ℝ) ≤ 2)
  rw [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h2
  exact hev.trans h2

/-- **The depth-aware event bound over the whole game** (the assembly's hypothesis `hev`):
on a `PermGood` table, `ewR (gameR A) L ≤ (advTermD q d + verTerm q + √(twPR A L + verLin q))²`,
from a parallel prefix program as in `ewPrefix_le_depth_of_par`. -/
theorem ewR_le_depth_of_par (L : HonestTable) (hπ : PermGood L.perm 18) {d : ℕ} {α : Type}
    (xP : QComp (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
      (QReg.of Unit) (QReg.of Unit) α)
    (hev : (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap)) (prefixR A L)
      initR ≤ ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments
        (hwProjector (BadR L progCap)) xP initR)
    (htw : ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
      (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L)))) xP initR ≤
        twPR A L)
    (hxq : IFreeM.IsChargeBound xP (portCharge (portWidth (portR X Z HPos Selections) .h))
      (2 * q))
    (hxd : IFreeM.IsChargeBound xP (portCharge (portDepth (portR X Z HPos Selections) .h))
      (2 * min d q))
    (hxk : IFreeM.IsChargeBound xP (portCharge (capWidth (portR X Z HPos Selections))) (4 * q))
    (hxK : IFreeM.IsChargeBound xP (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) clsCap)
    (hxm : IFreeM.IsChargeBound xP (portCharge (mixedRounds (portR X Z HPos Selections))) 0) :
    ewR (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  ewR_le_sqrt_of_prefix_amp hperm hsign L hπ
    (ewPrefix_le_depth_of_par L hπ xP hev htw hxq hxd hxk hxK hxm)

/-- **The assembly's event hypothesis** from a family of parallel prefix programs `xP L` as in
`ewPrefix_le_depth_of_par`, given on the good tables. -/
theorem ewR_le_depth_of_par_good {d : ℕ} {α : Type}
    (xP : HonestTable → QComp (parSpec (recHwSpec X Z HPos Selections)
      (portR X Z HPos Selections)) (QReg.of Unit) (QReg.of Unit) α)
    (hev : ∀ L, GoodL L → (runtimeR m0R).eventWeight .instruments (hwProjector (BadR L progCap))
      (prefixR A L) initR ≤ ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight
        .instruments (hwProjector (BadR L progCap)) (xP L) initR)
    (htw : ∀ L, GoodL L → ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight
      .instruments (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L))))
        (xP L) initR ≤ twPR A L)
    (hxq : ∀ L, IFreeM.IsChargeBound (xP L)
      (portCharge (portWidth (portR X Z HPos Selections) .h)) (2 * q))
    (hxd : ∀ L, IFreeM.IsChargeBound (xP L)
      (portCharge (portDepth (portR X Z HPos Selections) .h)) (2 * min d q))
    (hxk : ∀ L, IFreeM.IsChargeBound (xP L) (portCharge (capWidth (portR X Z HPos Selections)))
      (4 * q))
    (hxK : ∀ L, IFreeM.IsChargeBound (xP L) (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) clsCap)
    (hxm : ∀ L, IFreeM.IsChargeBound (xP L)
      (portCharge (mixedRounds (portR X Z HPos Selections))) 0) :
    ∀ L, GoodL L →
      ewR (gameR A) L ≤ (advTermD q d + verTerm q + (twPR A L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 :=
  fun L hg ↦ ewR_le_depth_of_par hperm hsign L hg.1.1 (xP L) (hev L hg) (htw L hg) (hxq L)
    (hxd L) (hxk L) (hxK L) (hxm L)

end event

/-! ## The assembly's event hypothesis for a parallel adversary -/

section par

attribute [local instance] badRDec

variable (Ap : AdversaryPar PublicKey SigningRequest (Option Signature) Forgery (X × Z))
  {q d : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk) (cmdChargePar signChargePar) lifetime)

include hq in
/-- The prefix's calls of `h`: at most `2q`. -/
theorem prefixRPar_hWidth (L : HonestTable) :
    IFreeM.IsChargeBound (prefixRPar Ap L)
      (portCharge (portWidth (portR X Z HPos Selections) .h)) (2 * q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_width Ap L hq _ (K := 1)
    (c := fun p ↦ if p = .h then 1 else 0) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if p = SpongePort.h then 1 else 0) ≤ 1
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · rw [portWidth_round_const]
    cases p <;> simp

include hq hd in
/-- The prefix's rounds of `h`: at most `2 min d q`. -/
theorem prefixRPar_hDepth (L : HonestTable) :
    IFreeM.IsChargeBound (prefixRPar Ap L)
      (portCharge (portDepth (portR X Z HPos Selections) .h)) (2 * min d q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_depth Ap L hq hd _ (K := 1)
    (c := fun p ↦ if p = .h then 1 else 0) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if (if p = SpongePort.h then 1 else 0) = 0 then 0 else 1) ≤ 1
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · unfold portDepth
    rw [portWidth_round_const]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · cases p <;> simp
    · cases p <;> simp [Nat.min_eq_left hm, hm.ne']

include hq in
/-- The prefix's calls of `k` and `k'`: at most `4q`. -/
theorem prefixRPar_capWidth (L : HonestTable) :
    IFreeM.IsChargeBound (prefixRPar Ap L)
      (portCharge (capWidth (portR X Z HPos Selections))) (4 * q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_width Ap L hq _ (K := 2)
    (c := fun p ↦ if p = .h then 0 else 1) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if p = SpongePort.k then 1 else 0) + (if p = SpongePort.k' then 1 else 0) ≤ 2
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · rw [capWidth, portWidth_round_const, portWidth_round_const]
    cases p <;> simp

include hs in
/-- The prefix's classical calls: at most `clsCap`. -/
theorem prefixRPar_cls (L : HonestTable) :
    IFreeM.IsChargeBound (prefixRPar Ap L) (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) clsCap := by
  rw [portCharge_eq_callCharge]
  refine isChargeBound_prefixRPar_cls Ap L hs _ (fun i ↦ ?_) fun m p ↦
    clsCount_round (port := portR X Z HPos Selections) (cls := hwExtCls X Z Mem
      (recSpec HPos Selections)) (fun _ ↦ rfl) m fun _ ↦ p
  rcases i with ((p | c) | c) | j <;> simp [clsCount, Par.widthCharge, hwExtCls, hwCls, rCharge]

/-- The prefix has no rounds mixing ports. -/
theorem prefixRPar_mixed (L : HonestTable) :
    IFreeM.IsChargeBound (prefixRPar Ap L)
      (portCharge (mixedRounds (portR X Z HPos Selections))) 0 := by
  rw [portCharge_eq_callCharge]
  exact isChargeBound_prefixRPar_zero Ap L _ (fun _ ↦ rfl) fun m p ↦ by
    change (if (∀ _ : Fin m, p = .h) ∨ (∀ _ : Fin m, p = .k) ∨ (∀ _ : Fin m, p = .k')
      then 0 else 1) = 0
    cases p <;> simp

include hq hd hs in
/-- **The assembly's event hypothesis** for a parallel adversary `Ap` of width `q` in `d` rounds:
at `A := serialize (refusePar Ap)`, on every good table,
`ewR (gameR A) L ≤ (advTermD q d + verTerm q + √(twPR A L + verLin q))²`. -/
theorem ewR_le_depth_serialize_refusePar :
    ∀ L, GoodL L → ewR (gameR (serialize (refusePar Ap))) L ≤
      (advTermD q d + verTerm q +
        (twPR (serialize (refusePar Ap)) L + verLin q) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hq' := fun pk ↦ isChargeBound_refusePar (A := Ap) (pk := pk) (hq pk)
  have hd' := fun pk ↦ isChargeBound_refusePar (A := Ap) (pk := pk) (hd pk)
  have hs' := fun pk ↦ isChargeBound_refusePar (A := Ap) (pk := pk) (hs pk)
  exact ewR_le_depth_of_par_good (fun pk ↦ isChargeBound_toSeq_perm (hq' pk))
    (fun pk ↦ isChargeBound_toSeq_sign (hs' pk)) (prefixRPar (refusePar Ap))
    (fun L _ ↦ (eventWeight_prefixRPar_eq (refusePar Ap) L _ initR).le)
    (fun L _ ↦ (twPR_eq_par (refusePar Ap) L).symm.le)
    (prefixRPar_hWidth (refusePar Ap) hq') (prefixRPar_hDepth (refusePar Ap) hq' hd')
    (prefixRPar_capWidth (refusePar Ap) hq') (prefixRPar_cls (refusePar Ap) hs')
    (prefixRPar_mixed (refusePar Ap))

end par

end Quantum.Xmss.Assembly

end
