module

public import Quantum.Qrom.Sphincs.DepthGame
public import Quantum.Qrom.Sphincs.DepthCharges
public import Quantum.Qrom.Sphincs.DepthBound

@[expose] public section

/-!
# The end of leanSPHINCS's QROM chain against parallel adversaries: runtime 2's win

End's event bound over the whole game (`ewGameQ_le`) adds the verification's reads to the bound
`(advTermQ q S + √twPQ)²` at the end of the challenge prefix. For a parallel adversary the bound
at the end of the prefix has another adversary term, so the end bound is restated for any
adversary term `a` (`ewGameQ_le_of`, `p2Q_le_of`, same proof), and the prefix bound of the
serialized adversary comes from the round runtime (`ewPrefixQD_le`): the serialized prefix runs
as the prefix with batched rounds (`runTWEq_prefixQ`), the serialization of the prefix with
rounds (`prefixQB_serialize`), where DepthPar's `eventWeight_runtimeR_serialize_le` applies:
every cell of `BadRQ` is a one-cell target event, so a round of width `w` costs
`√(6 · epsQ S · w)` and the rounds together `advTermQD q d S = √(6 · epsQ S · min d q · q)`. The
classical costs `twPQ` are those of the serialized adversary, unchanged.

Averaged over the hidden values (`uavg_p2Q_le_depth`), linear in `epsQ S★`:
`E p2Q ≤ (advBarQD q d + verBarQ + √(T + verLinBarQ))² + readErrQ`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Quantum.Xmss.Hybrid
open Quantum.Sphincs (Disclosures Covered price)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls noBot_runtimeR
  querySupportedOn_runtimeR_step' rpow_inv_two_eventWeight_keepReads_le keepCost
  eventWeight_bind₂ eventWeight_eq_tsum_run₂ tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq
  uavg_const uavg_sq_rpow_add_le eventWeight_runtimeR_serialize_le)

attribute [local irreducible] sphincsRom

/-! ## The end bound for any adversary term -/

section event

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **The event bound over the whole game, for any adversary term `a`**: from a bound
`(a + √twPQ)²` at the end of the challenge prefix, End's `ewGameQ_le` with `a` for
`advTermQ q S`: `ew ≤ (a + verTermQ S + √(twPQ + verLinQ S))²`. -/
theorem ewGameQ_le_of (pk : PublicKey) (hon : HonestCells) (S : Disclosures) (θ : TVals)
    {a : ℝ≥0∞}
    (hpreT : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol A θ) initQ ≤ (a + twPQ pk hon S strPol A θ ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S)) (gameQ strPol A θ)
        initQ ≤
      (a + verTermQ S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hρa := fun a ↦ ((runtimeR m0Q).run₂ .instruments
    (prefixQ strPol A θ)).posSemidef_branch_apply a initQ_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (querySupportedOn_runtimeR_step' (X := PairOut) (Z := Qrom.HashDomain) m0Q) .instruments
    (calls_prefixQ A hhash hsign θ) querySupportedOn_dbGrade_initQ ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q .instruments
    (prefixQ strPol A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadRQ pk hon S)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (N := q + clsCapQ + verifyCalls) (ε := epsQ S)
    (epsQ_ne_top S) (fun W m ↦ freshBound_slice_badRQ W m _) .instruments
    (realizeT θ (verifyT SelMem a)) (chg_verifyT_oneQ θ a) (chg_verifyT_nonKeepQ θ a)
    (t := 0 + (q + clsCapQ)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments
      (prefixQ strPol A θ)).branch a initQ).trace.re ≤ 1 :=
    (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initQ_posSemidef).trans ofReal_trace_initQ_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0Q) .instruments
    (hwProjector (BadRQ pk hon S)) (prefixQ strPol A θ) initQ
  have hm : ∑' j, (∑' a, (if j < verifyCalls then epsQ S else 0) *
      ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a
        initQ).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQ S := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then epsQ S else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQ S := by
          unfold verTermQ
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadRQ pk hon S))
      (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a initQ) +
      (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) *
        ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a
          initQ).trace.re) ≤
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
        (prefixQ strPol A θ) initQ + verLinQ S := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * 1 := by
          gcongr
      _ = verLinQ S := mul_one _
  have hpre' : ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol A θ) initQ + verLinQ S) ^ (2⁻¹ : ℝ) ≤
      a + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := a ^ 2) (δ := 0) (C := verLinQ S)
      (b := twPQ pk hon S strPol A θ) (a := (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (prefixQ strPol A θ) initQ) (by
          rw [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm a]))
    rwa [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameQ strPol A θ) initQ = ∑' a, (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (realizeT θ (verifyT SelMem a))
        (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a initQ) := by
    rw [gameQ_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0Q) .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol A θ) _ initQ_posSemidef
  have hfin : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameQ strPol A θ) initQ ^ (2⁻¹ : ℝ) ≤
      a + verTermQ S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
          (prefixQ strPol A θ) initQ + verLinQ S) ^ (2⁻¹ : ℝ) + verTermQ S :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ a + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) + verTermQ S :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **Runtime 2's win at `θ`, for any adversary term `a`**:
`p2Q ≤ (a + verTermQ S★ + √(twPQ + verLinQ S★))² + readErrQ`, `S★ = starQ θ`. -/
theorem p2Q_le_of (θ : TVals) {a : ℝ≥0∞}
    (hpreT : (runtimeR m0Q).eventWeight .instruments
      (hwProjector (BadRQ (pkQ θ) (honQ θ) (starQ θ))) (prefixQ strPol A θ) initQ ≤
        (a + twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ ^ (2⁻¹ : ℝ)) ^ 2) :
    p2Q strPol A θ ≤ (a + verTermQ (starQ θ) +
      (twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ + verLinQ (starQ θ)) ^ (2⁻¹ : ℝ)) ^ 2 +
        readErrQ :=
  (p2Q_le_eventWeight A hsign θ).trans
    (add_le_add (ewGameQ_le_of A hhash hsign (pkQ θ) (honQ θ) (starQ θ) θ hpreT) le_rfl)

end event

/-! ## The event at the end of the prefix, with rounds -/

section rounds

/-- **The adversary term with rounds**: `√(6 · epsQ S · min d q · q)`. -/
noncomputable def advTermQD (q d : ℕ) (S : Disclosures) : ℝ≥0∞ :=
  (6 * epsQ S * ((min d q : ℕ) : ℝ≥0∞) * q) ^ (2⁻¹ : ℝ)

set_option linter.constructorNameAsVariable false in
/-- **The fresh bound of the event at one cell**: `epsQ S`. -/
theorem freshBound_slice_badRQAt {pk : PublicKey} {hon : HonestCells} {S : Disclosures}
    (c : Qrom.HashDomain) (W : Hw PairOut Qrom.HashDomain) (m : QMem) (t : ℕ) :
    FreshBound (slice (CellTargetBadAt (tgtR pk hon S) c) W m) t (epsQ S) := by
  classical
  refine freshBound_slice_cellTargetBadAt c W m (fun x _ ↦ ?_) t
  change ((Finset.univ.filter fun ω ↦ ω ∈ sphTgtQ pk hon S W m.2 x).card : ℝ≥0∞) /
    Fintype.card (HashOutput × HashOutput) ≤ _
  have hsub : (Finset.univ.filter fun ω ↦ ω ∈ sphTgtQ pk hon S W m.2 x) ⊆
      (Finset.univ.filter fun ω ↦ ω ∈ structTgtQ pk hon W m.2 x) ∪
        (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ Covered S (pairView ω)) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hω ⊢
    exact hω.imp id fun h ↦ h.2.2
  refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))) _) ?_
  rw [epsQ, Nat.cast_add, ENNReal.add_div, ← covFrac_eq S, ← pairFiber_div_card]
  exact add_le_add (ENNReal.div_le_div_right (by exact_mod_cast card_structTgtQ_le W m.2 x) _)
    le_rfl

theorem hwExtCls_eqS :
    hwExtCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) =
      extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) := by
  funext i
  rcases i with i | j <;> rfl

variable (hcomm : ∀ R : QuantumRuntime (RSpecS SelMem), RoundsCommute TPos SelMem hmsgRoute R)
  (A : SAdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar)
    signatureLimit)
include hcomm hw hr hs

/-- **The event bound at the end of the challenge prefix, with rounds**: the serialized
adversary's prefix has `ew ≤ (advTermQD q d S + √twPQ)²`, its classical costs unchanged. -/
theorem ewPrefixQD_le (pk : PublicKey) (hon : HonestCells) (S : Disclosures) (θ : TVals) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol (SufCma.serialize A) θ) initQ ≤
      (advTermQD q d S + twPQ pk hon S strPol (SufCma.serialize A) θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hR := runTWEq_prefixQ (hcomm (runtimeR m0Q)) strPol A θ
  have hxq : IFreeM.IsChargeBound (prefixQPar strPol A θ) (portCharge (spongeWidth
      (ePort PairOut Qrom.HashDomain QMem (recSpec TPos SelMem))
      (hwExtCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) q := by
    rw [hwExtCls_eqS]
    exact width_prefixQPar strPol A hw hs θ
  have hxd : IFreeM.IsChargeBound (prefixQPar strPol A θ) (portCharge (spongeRounds
      (ePort PairOut Qrom.HashDomain QMem (recSpec TPos SelMem))
      (hwExtCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) (min d q) := by
    rw [hwExtCls_eqS]
    exact rounds_prefixQPar_min strPol A hw hr hs θ
  have hxK : IFreeM.IsChargeBound (prefixQPar strPol A θ) (portCharge (clsCount
      (ePort PairOut Qrom.HashDomain QMem (recSpec TPos SelMem))
      (hwExtCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem)))) clsCapQ := by
    rw [hwExtCls_eqS]
    exact cls_prefixQPar strPol A hw hs θ
  have h := eventWeight_runtimeR_serialize_le (BadRQ pk hon S) (labelFree_badRQ pk hon S)
    (fun c ↦ CellTargetBadAt (tgtR pk hon S) c) (fun c ↦ cellTargetBadAt_subset c)
    (fun _ hs ↦ exists_mem_cellTargetBadAt hs)
    (fun c s s' h₁ h₂ h₃ ↦ mem_cellTargetBadAt_congr c s s' h₁ h₂ h₃)
    (fun _ W m ↦ upClosed_slice_cellTargetBad W m) (fun W m ↦ upClosed_slice_badRQ W m) m0Q
    (empty_not_mem_badRQ m0Q) (ε := epsQ S) (epsQ_ne_top S)
    (fun c W m ↦ freshBound_slice_badRQAt c W m _) (fun W m ↦ freshBound_slice_badRQ W m _)
    (fun c σ ↦ readCostT (BadRQ pk hon S) c σ)
    (fun c σ ↦ flipCost (BadRQ pk hon S) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQ pk hon S) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQ pk hon S) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    (prefixQPar strPol A θ) hxq hxd hxK (SubState.basis ())
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol (SufCma.serialize A) θ) initQ =
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
        (prefixQB strPol A θ) initQ := by
    unfold QuantumRuntime.eventWeight
    rw [hR.1]
  have htw : twPQ pk hon S strPol (SufCma.serialize A) θ =
      (runtimeR m0Q).totalWeight .instruments
        (Quantum.Xmss.Assembly.extWeight (hwCost (fun c σ ↦ readCostT (BadRQ pk hon S) c σ)
          fun c σ ↦ flipCost (BadRQ pk hon S) (hwProgKraus c) 0 σ)) (prefixQB strPol A θ) initQ :=
    hR.2 _ (fun _ ↦ rfl) _
  rw [hew, htw, prefixQB_serialize]
  exact h

end rounds

/-! ## Averaged over the hidden values -/

section average

theorem advTermQD_eq (q d : ℕ) (S : Disclosures) :
    advTermQD q d S = ((6 * ((min d q : ℕ) : ℝ≥0∞) * q) * epsQ S) ^ (2⁻¹ : ℝ) := by
  unfold advTermQD
  ring_nf

theorem advBarQD_eq (q d : ℕ) :
    advBarQD q d = ((6 * ((min d q : ℕ) : ℝ≥0∞) * q) * epsBarQ) ^ (2⁻¹ : ℝ) := by
  unfold advBarQD
  ring_nf

variable (A : SAdversary) {q : ℕ} (d : ℕ)
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **Runtime 2's win, averaged, with rounds** (Minkowski over the hidden values): with the
prefix bounds at `advTermQD q d S★` and the prefix's averaged classical cost at most `T`,
`E p2Q ≤ (advBarQD q d + verBarQ + √(T + verLinBarQ))² + readErrQ`. -/
theorem uavg_p2Q_le_depth {T : ℝ≥0∞}
    (hpreT : ∀ θ, (runtimeR m0Q).eventWeight .instruments
      (hwProjector (BadRQ (pkQ θ) (honQ θ) (starQ θ))) (prefixQ strPol A θ) initQ ≤
        (advTermQD q d (starQ θ) + twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ ^ (2⁻¹ : ℝ)) ^ 2)
    (hcost : uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ) ≤ T) :
    uavg (p2Q strPol A) ≤
      (advBarQD q d + verBarQ + (T + verLinBarQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  refine (uavg_mono fun θ ↦ p2Q_le_of A hhash hsign θ (hpreT θ)).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  simp only [advTermQD_eq, verTermQ_eq, advBarQD_eq]
  refine (uavg_sq_rpow_add3_le _ _ _).trans (pow_le_pow_left₀ zero_le
    (add_le_add (add_le_add ?_ ?_) ?_) 2)
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_add]
    refine add_le_add hcost ?_
    unfold verLinQ verLinBarQ keepCost
    rw [uavg_const_mul, uavg_add, uavg_add, uavg_const, uavg_const]
    gcongr
    exact uavg_epsQ_le

end average

end Quantum.Qrom.Sphincs

end
