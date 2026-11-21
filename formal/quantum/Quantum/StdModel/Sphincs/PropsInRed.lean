module

public import Quantum.StdModel.Sphincs.PropsIn
public import Quantum.StdModel.Sphincs.Reduction

@[expose] public section

/-!
# Theorem 2 with SM-TCR-C and EncTCR+C restricted to the in-range tweaks

The reductions `tcrRed W A` and `encRed W A` submit targets only at tweaks where the inputs of
the collections determine the tweak: `tcrRed` at the slot of a target position, whose kind is the
target function's and which is in range (`TcrTwIn`), `encRed` at the encoding slot of a key in use
(`EncTwIn`). Their successes in the restricted games `Props.smTcrIn` and `Props.encTcrCtrIn` are
therefore their successes in the unrestricted games (`smTcrSucc_tcrRed_eq`,
`encTcrCtrSucc_encRed_eq`), and Theorem 2 holds with the restricted games
(`sphincs_suf_le_propsIn`, `sphincs_suf_le_propsIn_keccak`).
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Slot)
open Quantum.Qrom.Sphincs (sphincsOver RawPos Pos SlotInRange)

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props

/-! ## The target tweaks -/

/-- The tweaks of SM-TCR targets: a slot of the target function's kind, in range. -/
def TcrTwIn : TcrFn → Slot → Prop
  | .leaf, .leaf .. => True
  | .node, s@(.node ..) => SlotInRange s
  | .forsNode, s@(.forsNode ..) => SlotInRange s
  | .forsRoots, .forsRoots _ => True
  | _, _ => False

/-- The tweaks of EncTCR+C targets: the encoding slots. -/
def EncTwIn : Slot → Prop
  | .enc .. => True
  | _ => False

/-- A target position's slot is a tweak of its target function. -/
theorem tcrTwIn_keySlot (p : Pos) (hp : IsTarget p.1) : TcrTwIn (tcrFnOf p.1) (keySlot p.1) := by
  have hr := slotInRange_keySlot p (tcr_ne_hmsg (tcr_keyPart_of_isTarget hp))
  obtain ⟨p, hin⟩ := p
  cases p with
  | leaf => trivial
  | node => exact hr
  | forsNode => exact hr
  | forsRoots => trivial
  | _ => exact False.elim hp

/-- Every target of the setup's transcript is at a tweak of its target function. -/
theorem tcrIn_tcrLog (u : RawPos → Digest) (P : PublicParameter) :
    TcrIn TcrTwIn (tcrLog u P) := by
  intro e he
  rw [tcrTargets_tcrLog] at he
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp he
  split_ifs at hpe with hg
  obtain rfl := Option.some.inj hpe
  exact tcrTwIn_keySlot p (tcrIsTgt_iff.mp hg)

/-- Every target of the reduction's EncTCR+C transcript is at an encoding slot. -/
theorem encIn_enc (Tb : List EncEnt) (hTb : ∀ e ∈ Tb, EncEvalOk e) (tg : List EncTgt)
    (P : PublicParameter) :
    EncIn EncTwIn (Tb ++ tg.map encEntry ++ [encRev P] : QueryLog EncCtrPorts) := by
  intro e he
  rw [ctrTargets_enc Tb hTb tg P] at he
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
  trivial

variable (W : OracleWorld) (tab : W.Tab) (A : SAdv W)

/-! ## SM-TCR-C -/

/-- The restricted SM-TCR challenger. -/
noncomputable abbrev tcrGameIn : Props.Experiment W TcrPorts Unit TcrOut :=
  Props.smTcrIn W tcrColl slotColl TcrTwIn

/-- The output and the restricted challenger's decision at a fixed table. -/
theorem tcrPost_judgeIn (P : PublicParameter) (a : TcrData) (f : Forgery) (st : TcrSt)
    (log : QueryLog TcrPorts) :
    ((simulateQ (logImpl tab ((tcrGameIn W).answer P)) (tcrPost W a f st)).run log >>= fun r ↦
      simulateQ (W.eager tab) ((tcrGameIn W).judge P r.2 r.1)) =
      pure (holds (TcrIn TcrTwIn log) && tcrJudgeDec W tab P a (f, (st, log))) := by
  simp only [tcrPost, simulateQ_bind,
    simulateQ_recVerify (logImpl tab ((tcrGameIn W).answer P)) (tcrHash W) (W.hashOf tab)
      (simulateQ_logImpl_tcrHash W tab _),
    simulateQ_tcrHashAll, StateT.run_pure, pure_bind, simulateQ_pure, tcrLook_map]
  simp only [tcrGameIn, Props.smTcrIn, Props.smTcr, simulateQ_bind, simulateQ_eval, pure_bind,
    simulateQ_pure]
  rfl

/-- **`tcrRed` wins the restricted SM-TCR game exactly when it wins SM-TCR**: all its targets
are at target positions' slots. -/
theorem smTcrSucc_tcrRed_eq (hW : W.CoinsFair) :
    Props.smTcrSucc W tcrColl slotColl tab (tcrRed W A) =
      Props.smTcrInSucc W tcrColl slotColl TcrTwIn tab (tcrRed W A) := by
  have e1 := tcr_succAt_slRed W tab (tcrGame W) (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, []))
    (tcrSigner W) (tcrPost W) (fun P a ↦ tcrJudgeDec W tab P a)
    (fun P a f st log ↦ tcrPost_judge W tab P a f st log)
  have e2 := tcr_succAt_slRed W tab (tcrGameIn W) (tcrPre W) (fun a ↦ A a.pk)
    (fun a ↦ (a, [])) (tcrSigner W) (tcrPost W)
    (fun P a x ↦ holds (TcrIn TcrTwIn x.2.2) && tcrJudgeDec W tab P a x)
    (fun P a f st log ↦ tcrPost_judgeIn W tab P a f st log)
  have hset : (tcrGameIn W).setup = (tcrGame W).setup := rfl
  have hans : (tcrGameIn W).answer = (tcrGame W).answer := rfl
  rw [hset, hans] at e2
  change (tcrGame W).succAt tab (fun _ ↦ slRed W (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, []))
      (tcrSigner W) (tcrPost W)) =
    (tcrGameIn W).succAt tab (fun _ ↦ slRed W (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, []))
      (tcrSigner W) (tcrPost W))
  rw [e1, e2]
  refine tsum_congr fun P ↦ congrArg (_ * ·) ?_
  rw [run_tcrPre W tab hW]
  simp only [tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine congrArg (unifAvg _) (funext fun s ↦ congrArg (unifAvg _) (funext fun r ↦ ?_))
  obtain ⟨tf, -, hrun⟩ := run_tcrRest W tab P s r
  rw [hrun, tsum_prEvent_pure_mul, tsum_prEvent_pure_mul]
  refine (probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (hKernel tab ((tcrGame W).answer P) (tcrSigner W))
    (hKernel tab ((tcrGame W).answer P) (tcrSigner W))
    (tcrInv ⟨P, s, r, tf, (digTable (W.hashOf tab) P s r).publicKey⟩
      (tcrLog (digTable (W.hashOf tab) P s r).dig P)) id
    (fun st _ M ↦ by rw [Prod.map_id, id_map]; rfl)
    (fun st hst M ↦ tcr_hInv W tab _ _ _ st hst M)
    (A (digTable (W.hashOf tab) P s r).publicKey)
    ((⟨P, s, r, tf, (digTable (W.hashOf tab) P s r).publicKey⟩, []),
      tcrLog (digTable (W.hashOf tab) P s r).dig P) ⟨rfl, rfl⟩
    (tcrJudgeDec W tab P ⟨P, s, r, tf, (digTable (W.hashOf tab) P s r).publicKey⟩)
    (fun x ↦ holds (TcrIn TcrTwIn x.2.2) &&
      tcrJudgeDec W tab P ⟨P, s, r, tf, (digTable (W.hashOf tab) P s r).publicKey⟩ x)
    fun f st hst ↦ ?_)).symm
  rw [show st.2 = _ from hst.2, holds_eq_true.mpr (tcrIn_tcrLog _ P), Bool.true_and]
  rfl

/-! ## EncTCR+C -/

/-- The restricted EncTCR+C challenger. -/
noncomputable abbrev encGameIn :
    Props.Experiment W EncCtrPorts Unit (Slot × Digest × ℕ) :=
  Props.encTcrCtrIn W encCtr slotColl EncTwIn

/-- The restricted EncTCR+C challenger's decision at a fixed table. -/
theorem simulateQ_encJudgeIn (P : PublicParameter) (log : QueryLog EncCtrPorts)
    (out : Slot × Digest × ℕ) :
    simulateQ (W.eager tab) ((encGameIn W).judge P log out) =
      pure (holds (EncIn EncTwIn log) && encJ (W.hashOf tab) P log out) := by
  simp only [encGameIn, Props.encTcrCtrIn, Props.encTcrCtr, simulateQ_bind, simulateQ_eval,
    pure_bind, simulateQ_pure]
  rfl

/-- **`encRed` wins the restricted EncTCR+C game exactly when it wins EncTCR+C**: all its
targets are at encoding slots. -/
theorem encTcrCtrSucc_encRed_eq (hW : W.CoinsFair) :
    Props.encTcrCtrSucc W encCtr slotColl tab (encRed W A) =
      Props.encTcrCtrInSucc W encCtr slotColl EncTwIn tab (encRed W A) := by
  have e1 := tcr_succAt_slRed W tab (Props.encTcrCtr W encCtr slotColl) (encRedPre W)
    (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W) (encRedPost W)
    (fun P a x ↦ encD (W.hashOf tab) P x.2.2 a a.pk x.1)
    (fun P a f st log ↦ by
      rw [run_encRedPost, pure_bind]
      exact simulateQ_encJudge W tab P _ _)
  have e2 := tcr_succAt_slRed W tab (encGameIn W) (encRedPre W)
    (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W) (encRedPost W)
    (fun P a x ↦ holds (EncIn EncTwIn x.2.2) && encD (W.hashOf tab) P x.2.2 a a.pk x.1)
    (fun P a f st log ↦ by
      rw [run_encRedPost, pure_bind]
      exact simulateQ_encJudgeIn W tab P _ _)
  have hset : (encGameIn W).setup = (Props.encTcrCtr W encCtr slotColl).setup := rfl
  have hans : (encGameIn W).answer = (Props.encTcrCtr W encCtr slotColl).answer := rfl
  rw [hset, hans] at e2
  change (Props.encTcrCtr W encCtr slotColl).succAt tab (fun _ ↦ slRed W (encRedPre W)
      (fun a ↦ A a.pk) (fun a ↦ (a, [])) (encRedSign W) (encRedPost W)) =
    (encGameIn W).succAt tab (fun _ ↦ slRed W (encRedPre W) (fun a ↦ A a.pk)
      (fun a ↦ (a, [])) (encRedSign W) (encRedPost W))
  rw [e1, e2]
  refine tsum_congr fun P ↦ congrArg (_ * ·) ?_
  rw [run_encRedPre W tab P hW]
  simp only [tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine congrArg (unifAvg _) (funext fun s ↦ congrArg (unifAvg _) (funext fun r ↦ ?_))
  obtain ⟨Tb, hTb, hrun⟩ := run_encCore W tab P s r
  rw [hrun, tsum_prEvent_pure_mul, tsum_prEvent_pure_mul]
  refine (probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P) (encRedSign W))
    (hKernel tab ((Props.encTcrCtr W encCtr slotColl).answer P) (encRedSign W))
    (fun st ↦ st.1.1 = encDataAt (W.hashOf tab) P s r ∧
      st.2 = Tb ++ (encTgAt (W.hashOf tab) P s r).map encEntry ++ [encRev P]) id
    (fun st _ M ↦ by rw [Prod.map_id, id_map]; rfl)
    (fun st hst M ↦ encKernel_inv W tab P _ _ st hst M)
    (A (encDataAt (W.hashOf tab) P s r).pk)
    ((encDataAt (W.hashOf tab) P s r, []),
      Tb ++ (encTgAt (W.hashOf tab) P s r).map encEntry ++ [encRev P]) ⟨rfl, rfl⟩
    (fun x ↦ encD (W.hashOf tab) P x.2.2 (encDataAt (W.hashOf tab) P s r)
      (encDataAt (W.hashOf tab) P s r).pk x.1)
    (fun x ↦ holds (EncIn EncTwIn x.2.2) && encD (W.hashOf tab) P x.2.2
      (encDataAt (W.hashOf tab) P s r) (encDataAt (W.hashOf tab) P s r).pk x.1)
    fun f st hst ↦ ?_)).symm
  dsimp only [id_eq]
  rw [hst.2, holds_eq_true.mpr (encIn_enc Tb hTb _ P), Bool.true_and]

/-! ## Theorem 2 with the restricted games -/

/-- **Theorem 2 at a fixed table with the restricted games**: SM-TCR-C with targets at the
in-range slots of the target functions and EncTCR+C with targets at the encoding slots. -/
theorem sphincs_suf_le_propsIn (hW : W.CoinsFair) :
    (winProbAt W (sphincsOver W.hash) tab A).toReal ≤
      kimPrfAdv W (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc tab (B1 W A) +
        prfMsgAdv W (Key := HashOutput) msgBytes (littleEndianBytes 32) truncateHash tab
          (B2 W A) +
        (itsrSucc W itsrMap tab (itsrRed W A)).toReal +
        (encTcrCtrInSucc W encCtr slotColl EncTwIn tab (encRed W A)).toReal +
        (cpreSucc W cpreChains slotColl tab (cpreRed W A)).toReal +
        (smTcrInSucc W tcrColl slotColl TcrTwIn tab (tcrRed W A)).toReal := by
  rw [← smTcrSucc_tcrRed_eq W tab A hW, ← encTcrCtrSucc_encRed_eq W tab A hW]
  exact sphincs_suf_le_props W hW tab A

/-- **Theorem 2 in the standard model with the restricted games**, at `keccakWorld`. -/
theorem sphincs_suf_le_propsIn_keccak (A : SAdv keccakWorld) :
    (winProbAt keccakWorld (sphincsOver keccakWorld.hash) () A).toReal ≤
      kimPrfAdv keccakWorld (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc ()
          (B1 keccakWorld A) +
        prfMsgAdv keccakWorld (Key := HashOutput) msgBytes (littleEndianBytes 32) truncateHash
          () (B2 keccakWorld A) +
        (itsrSucc keccakWorld itsrMap () (itsrRed keccakWorld A)).toReal +
        (encTcrCtrInSucc keccakWorld encCtr slotColl EncTwIn () (encRed keccakWorld A)).toReal +
        (cpreSucc keccakWorld cpreChains slotColl () (cpreRed keccakWorld A)).toReal +
        (smTcrInSucc keccakWorld tcrColl slotColl TcrTwIn () (tcrRed keccakWorld A)).toReal :=
  sphincs_suf_le_propsIn keccakWorld () A keccakWorld_coinsFair

end Quantum.StdModel.Sphincs

end
