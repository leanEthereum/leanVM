module

public import Quantum.StdModel.Qrom.SphincsEncCtrDefs
public import Quantum.StdModel.Qrom.SphincsTcr

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4, given the live invariant

`probAvg_encTcrCtrIn_encRed_le_ju`: the committed bound `EncTcr.encTcrCtrIn_probAvg_le` at
`encCtr`, `slotColl`, the encoding slots and `n = 7`, against B4, with the live invariant
`EncJu`. Its output reads at most six cells of the classes (`encRedPost_gc`), so on a live
memory with no charged read it leaves at most six (`encJu_post`). The two other live hypotheses,
the setup establishing `EncJu` and the handler keeping it, are left as hypotheses here.
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.StdModel.Qrom.EncTcr (Mem Gc upd rl mem₀ Inv Charged cntAfter)

attribute [local irreducible] encRedPost encRedSign encRedPre

section generic

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type} {e : CtrEnc Par Tw Msg Dig}
  {G : Tw → Prop} {n : ℕ}

/-- **A post of `k` reads at the classes leaves at most `k` charged reads** on the live runs from a
memory with none. -/
theorem liveRedRun_cnt_le_post {ans : (q' : CtrQuery Tw Msg Fn CMsg) →
      OracleComp romWorld.Oracles ((CtrSpec Par Tw Msg Dig Fn CMsg Out).Range q')}
    {α : Type} {post : OracleComp (romWorld.Oracles + CtrSpec Par Tw Msg Dig Fn CMsg Out) α}
    {k : ℕ} {log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {μ : Option (Mem n)}
    {r : α × QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)} {μ' : Option (Mem n)}
    (hrun : LiveRedRun (rl n) (upd e G n) ans post log μ r μ')
    (hk : Common.QueryCostAtMost post
      (gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) k)
    (hna : Common.QueryCostAtMost post
      (ansCost (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out)) 0)
    (h0 : ∀ m, μ = some m → m.cnt.val = 0) (m : Mem n) (hm : μ' = some m) : m.cnt.val ≤ k := by
  have h := liveRedRun_count (upd e G n) (rl n) ans (gCostR (Gc e G))
    (fun μ ↦ μ.elim 0 fun m ↦ m.cnt.val) (fun z μ v ↦ ?_) post hk hna hrun
  · rw [hm] at h
    have h00 : (μ.elim 0 fun m ↦ m.cnt.val) = 0 := by
      rcases μ with _ | m₀
      · rfl
      · exact h0 m₀ rfl
    have h1 := h.1
    change m.cnt.val ≤ (μ.elim 0 fun m ↦ m.cnt.val) + k at h1
    rw [h00] at h1
    omega
  · rcases μ with _ | m
    · exact Nat.zero_le _
    rcases hst : stepRd (rl n) (upd e G n .red z) z (some m) v with _ | m'
    · exact Nat.zero_le _
    obtain ⟨rfl, -⟩ := stepRd_some hst
    change (cntAfter e G n m z).val ≤ m.cnt.val + gCostR (Gc e G) (.inl (.inr z))
    unfold cntAfter
    split_ifs with hch
    · have hg : gCostR (Gc e G) (R' := CtrSpec Par Tw Msg Dig Fn CMsg Out) (.inl (.inr z)) =
          1 := by simp [gCostR, gCost, Gc, hch.1]
      rw [hg]
      change min (m.cnt.val + 1) (n + 1) ≤ _
      omega
    · omega

end generic

/-- **B4's output on a live memory with no charged read leaves at most six.** -/
theorem encJu_post (P : PublicParameter) (a : EncData) (f : Forgery) (st : EncData × SignLog)
    (log : QueryLog EncCtrPorts) (μ : Option (Mem nB)) (hJ : EncJu P a (st, log) μ)
    (r : (Quantum.Sphincs.Slot × Digest × ℕ) × QueryLog EncCtrPorts) (μ' : Option (Mem nB))
    (hrun : LiveRedRun (rl nB) (upd encCtr EncTwIn nB)
      ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encRedPost romWorld a f st) log
      μ r μ') (m : Mem nB) (hm : μ' = some m) : m.cnt.val + 1 ≤ nB := by
  have h := liveRedRun_cnt_le_post hrun (encRedPost_gc a f st)
    (SphInst.encRedPost_ansCost a f st) (fun m₀ hm₀ ↦ (hJ.2.2.2.2.2 m₀ hm₀).2) m hm
  change m.cnt.val + 1 ≤ 7
  omega

/-- The encoding inputs are cells. -/
theorem lenOk_encCtr : EncTcr.LenOk encCtr :=
  fun P t mc ↦ encHash_lengthLe () P t mc

/-- The encoding inputs at an encoding slot determine the slot, under any parameter. -/
theorem encSep_encCtr : EncTcr.EncSep encCtr EncTwIn :=
  fun P _ mc _ _ _ hG h ↦ (SphInst.encHash_param_tweak_eq hG P mc h).2

/-- `2^128` hash outputs per digest, with the classical decision of the fibers. -/
theorem card_truncateHash_fiber_le_enc' (o : Digest) :
    (@Finset.filter HashOutput (fun y ↦ encCtr.hash.trunc y = o)
      (fun _ ↦ Classical.propDecidable _) Finset.univ).card ≤ 2 ^ 128 := by
  convert Quantum.StdModel.Xmss.card_truncateHash_fiber_le o using 3
  exact Iff.rfl

attribute [local instance] secretsSampleable encRndSampleable in
open scoped Classical in
/-- **EncTCR+C at leanSPHINCS B4, given the live invariant**: if the setup's live runs establish
`EncJu` and the handler's keep it, then for an adversary of `q` hash calls
`probAvg ≤ (q √(6 · 2^128 / 2^256) + 7 √(gradeEta 2^128))²`. -/
theorem probAvg_encTcrCtrIn_encRed_le_ju (A : SAdv romWorld) {q : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
    (hpreU : ∀ P (a : EncData × QueryLog EncCtrPorts) μ, LiveRedRun (rl nB)
      (upd encCtr EncTwIn nB) ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P)
      (encRedPre romWorld) [] (some mem₀) a μ → EncJu P a.1 ((a.1, []), a.2) μ)
    (hσU : ∀ P a st log μ M, (∀ m, μ = some m → Inv encCtr EncTwIn nB P log m) →
      EncJu P a (st, log) μ →
      ∀ r μ', LiveRedRun (rl nB) (upd encCtr EncTwIn nB)
        ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).answer P) (encRedSign romWorld st M) log
        μ r μ' → EncJu P a (r.1.2, r.2) μ') :
    romWorld.probAvg ((encTcrCtrIn romWorld encCtr slotColl EncTwIn).game
        (encRed romWorld A)) ≤
      (q * (6 * (((2 ^ 128 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput)) ^ (2⁻¹ : ℝ) +
        (nB : ℝ≥0∞) * ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine EncTcr.encTcrCtrIn_probAvg_le encCtr slotColl EncTwIn nB lenOk_encCtr encSep_encCtr
    ?_ ?_ card_truncateHash_fiber_le_enc' (fun _ ↦ encRedPre romWorld) (fun _ a ↦ A a.pk)
    (fun _ a ↦ (a, [])) (fun _ ↦ encRedSign romWorld) (fun _ ↦ encRedPost romWorld)
    ?_ ?_ ?_ ?_ EncJu ?_ ?_ ?_
  · exact fun P _ _ ↦ SphInst.encHash_layout_injOn P _
  · exact fun _ _ _ _ _ _ mc hG h ↦ SphInst.slotColl_enc_tweak_eq hG mc h
  · exact fun a ↦ hq a.pk
  · exact encRedPre_gc
  · exact fun st M ↦ SphInst.encRedSign_ansCost st M
  · exact fun a f st ↦ SphInst.encRedPost_ansCost a f st
  · exact fun P a μ h ↦ hpreU P a μ h
  · exact fun P a st log μ M hI hJ r μ' h ↦ hσU P a st log μ M hI hJ r μ' h
  · exact fun P a f st log μ _ hJ r μ' h m hm ↦ encJu_post P a f st log μ hJ r μ' h m hm

end Quantum.StdModel.Qrom.SphEnc

end
