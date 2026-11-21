module

public import Quantum.Qrom.Xmss.DepthHybrid

@[expose] public section

/-!
# The end of leanXMSS's QROM chain against parallel adversaries: runtime 2's win

End's event bound over the whole game (`ewGameQ_le`) adds the verification's reads to the bound
`(advTermQ q + √twPQ)²` at the end of the challenge prefix. For a parallel adversary the bound at
the end of the prefix has another adversary term, so the end bound is restated for any adversary
term `a` (`ewGameQ_le_of`, `p2Q_le_of`, `uavg_p2Q_le_of`, same proofs), and the prefix bound of
the serialized adversary comes from the round runtime (`ewPrefixQD_le`, DepthPar's
`eventWeight_runtimeR_serialize_le`): every cell of `BadRQ` is a one-cell target event, so a
round of width `w` costs `√(6 · 2^-128 · w)` and the rounds together
`advTermQD q d = √(6 · 2^-128 · min d q · q)`. The classical costs `twPQ` are those of the
serialized adversary, unchanged.
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Quantum.Xmss.Hybrid Quantum.SufCma
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls noBot_runtimeR
  querySupportedOn_runtimeR_step' rpow_inv_two_eventWeight_keepReads_le keepCost
  eventWeight_bind₂ eventWeight_eq_tsum_run₂ tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq
  uavg_const uavg_sq_rpow_add_le eventWeight_runtimeR_serialize_le)

attribute [local irreducible] xmssRom

/-! ## The end bound for any adversary term -/

section event

variable (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

/-- **The event bound over the whole game, for any adversary term `a`**: from a bound
`(a + √twPQ)²` at the end of the challenge prefix, End's `ewGameQ_le` with `a` for `advTermQ q`:
`ew ≤ (a + verTermQ + √(twPQ hon A θ + verLinQ))²`. -/
theorem ewGameQ_le_of (hon : HonestCells) (θ : HPos → Digest) {a : ℝ≥0∞}
    (hpreT : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (prefixQ A θ)
      initQ ≤ (a + twPQ hon A θ ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ) initQ ≤
      (a + verTermQ + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hε : (2 ^ 128 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by positivity)
  have hρa := fun a ↦ ((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).posSemidef_branch_apply a
    initQ_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := HashOutput) (Z := HashDomain) m0Q) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (querySupportedOn_runtimeR_step' (X := HashOutput) (Z := HashDomain) m0Q) .instruments
    (calls_prefixQ A hhash hsign θ) querySupportedOn_dbGrade_initQ ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := HashOutput) (Z := HashDomain) m0Q .instruments
    (prefixQ A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadRQ hon)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (N := q + clsCapQ + verifyCalls) hε
    (fun W m ↦ freshBound_slice_badRQ W m _) .instruments
    (realizeT θ (verifyT SelMem a)) (chg_verifyT_oneQ θ a) (chg_verifyT_nonKeepQ θ a)
    (t := 0 + (q + clsCapQ)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
      initQ).trace.re ≤ 1 :=
    (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initQ_posSemidef).trans ofReal_trace_initQ_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0Q) .instruments
    (hwProjector (BadRQ hon)) (prefixQ A θ) initQ
  have hm : ∑' j, (∑' a, (if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) *
      ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
        initQ).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQ := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQ := by
          unfold verTermQ
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadRQ hon))
      (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a initQ) +
      (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
          initQ).trace.re) ≤
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (prefixQ A θ) initQ +
        verLinQ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
      _ = verLinQ := mul_one _
  have hpre' : ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
      (prefixQ A θ) initQ + verLinQ) ^ (2⁻¹ : ℝ) ≤
      a + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := a ^ 2) (δ := 0) (C := verLinQ)
      (b := twPQ hon A θ) (a := (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ hon)) (prefixQ A θ) initQ) (by
          rw [sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm a]))
    rwa [sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ)
      initQ = ∑' a, (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
        (realizeT θ (verifyT SelMem a))
        (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a initQ) := by
    rw [gameQ_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0Q) .instruments (hwProjector (BadRQ hon))
      (prefixQ A θ) _ initQ_posSemidef
  have hfin : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ)
      initQ ^ (2⁻¹ : ℝ) ≤ a + verTermQ + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
          (prefixQ A θ) initQ + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ a + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **Runtime 2's win at `θ`, for any adversary term `a`**:
`p2Q ≤ (a + verTermQ + √(twPQ + verLinQ))² + readErrQ`. -/
theorem p2Q_le_of (θ : HPos → Digest) {a : ℝ≥0∞}
    (hpreT : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ (honQ θ)))
      (prefixQ A θ) initQ ≤ (a + twPQ (honQ θ) A θ ^ (2⁻¹ : ℝ)) ^ 2) :
    p2Q A θ ≤ (a + verTermQ + (twPQ (honQ θ) A θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ :=
  (p2Q_le_eventWeight A θ).trans (add_le_add (ewGameQ_le_of A hhash hsign (honQ θ) θ hpreT)
    le_rfl)

/-- **Runtime 2's win, averaged, for any adversary term `a`** (Jensen for `(a + √f)²`): with
the prefix's averaged classical cost at most `T`,
`E p2Q ≤ (a + verTermQ + √(T + verLinQ))² + readErrQ`. -/
theorem uavg_p2Q_le_of {a T : ℝ≥0∞}
    (hpreT : ∀ θ, (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ (honQ θ)))
      (prefixQ A θ) initQ ≤ (a + twPQ (honQ θ) A θ ^ (2⁻¹ : ℝ)) ^ 2)
    (hcost : uavg (fun θ : HPos → Digest ↦ twPQ (honQ θ) A θ) ≤ T) :
    uavg (p2Q A) ≤ (a + verTermQ + (T + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  set c := a + verTermQ
  refine (uavg_mono fun θ ↦ p2Q_le_of A hhash hsign θ (hpreT θ)).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  have h := uavg_sq_rpow_add_le (fun _ : HPos → Digest ↦ c ^ 2)
    (fun θ ↦ twPQ (honQ θ) A θ + verLinQ)
  simp only [sq_rpow_inv_two_eq, uavg_const, uavg_add] at h
  refine h.trans (pow_le_pow_left₀ zero_le (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (add_le_add hcost le_rfl) (by norm_num))) 2)

end event

/-! ## The event at the end of the prefix, with rounds -/

section rounds

/-- **The adversary term with rounds**: `√(6 · 2^-128 · min d q · q)`. -/
noncomputable def advTermQD (q d : ℕ) : ℝ≥0∞ :=
  (6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * ((min d q : ℕ) : ℝ≥0∞) * q) ^ (2⁻¹ : ℝ)

/-- **The fresh bound of the event at one cell**: `2^-128`. -/
theorem freshBound_slice_badRQAt {hon : HonestCells} (c : HashDomain)
    (W : Hw HashOutput HashDomain) (m : QMem) (t : ℕ) :
    FreshBound (slice (CellTargetBadAt (tgtR hon) c) W m) t (2 ^ 128)⁻¹ := by
  classical
  refine freshBound_slice_cellTargetBadAt c W m (fun x _ ↦ ?_) t
  rw [← fiber_div_card_hashOutput]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_xmssTgtQ_le (hon := hon) W m.2 x) _

variable (A : AdversaryPar) {q d : ℕ}
  (hw : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.widthCharge) q)
  (hr : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdChargePar SufCma.signChargePar) lifetime)

include hw hr hs in
/-- **The event bound at the end of the challenge prefix, with rounds**: the serialized
adversary's prefix has `ew ≤ (advTermQD q d + √twPQ)²`, its classical costs unchanged. -/
theorem ewPrefixQD_le (hon : HonestCells) (θ : HPos → Digest) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
      (prefixQ (SufCma.serialize A) θ) initQ ≤
      (advTermQD q d + twPQ hon (SufCma.serialize A) θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hxq : IFreeM.IsChargeBound (prefixQPar A θ) (portCharge (spongeWidth
      (ePort HashOutput HashDomain QMem (recSpec HPos SelMem))
      (hwExtCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) q := by
    rw [hwExtCls_eq]
    exact width_prefixQPar A hw hs θ
  have hxd : IFreeM.IsChargeBound (prefixQPar A θ) (portCharge (spongeRounds
      (ePort HashOutput HashDomain QMem (recSpec HPos SelMem))
      (hwExtCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) (min d q) := by
    rw [hwExtCls_eq]
    exact rounds_prefixQPar_min A hw hr hs θ
  have hxK : IFreeM.IsChargeBound (prefixQPar A θ) (portCharge (clsCount
      (ePort HashOutput HashDomain QMem (recSpec HPos SelMem))
      (hwExtCls HashOutput HashDomain QMem (recSpec HPos SelMem)))) clsCapQ := by
    rw [hwExtCls_eq]
    exact cls_prefixQPar A hw hs θ
  have h := eventWeight_runtimeR_serialize_le (BadRQ hon) (labelFree_badRQ hon)
    (fun c ↦ CellTargetBadAt (tgtR hon) c) (fun c ↦ cellTargetBadAt_subset c)
    (fun _ hs ↦ exists_mem_cellTargetBadAt hs)
    (fun c s s' h₁ h₂ h₃ ↦ mem_cellTargetBadAt_congr c s s' h₁ h₂ h₃)
    (fun _ W m ↦ upClosed_slice_cellTargetBad W m) (fun W m ↦ upClosed_slice_badRQ W m) m0Q
    (empty_not_mem_badRQ m0Q) (ε := (2 ^ 128 : ℝ≥0∞)⁻¹)
    (ENNReal.inv_ne_top.mpr (by positivity)) (fun c W m ↦ freshBound_slice_badRQAt c W m _)
    (fun W m ↦ freshBound_slice_badRQ W m _)
    (fun c σ ↦ readCostT (BadRQ hon) c σ) (fun c σ ↦ flipCost (BadRQ hon) (hwProgKraus c) 0 σ)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadRQ hon) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadRQ hon) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    (prefixQPar A θ) hxq hxd hxK (SubState.basis ())
  unfold twPQ advTermQD
  rw [prefixQ_serialize]
  exact h

end rounds

end Quantum.Qrom.Xmss

end
