module

public import Quantum.StdModel.Qrom.EncTcr
public import Quantum.StdModel.Qrom.SphincsInst

@[expose] public section

/-!
# EncTCR+C at leanSPHINCS B4: the cells of the classes and the live invariant

* **The cells of the classes** (`EncTcr.Gc encCtr EncTwIn`): the encoding trials below the limit
  at an encoding slot, under any `PK.seed`. They are honest inputs of encoding slots
  (`gc_kindCell`), so B4's setup reads none of them (`encRedPre_gc`) and its output at most six
  (`encRedPost_gc`), as for the encoding cells of the keys in use.
* **The live invariant** (`EncJu`): the handler's setup is the setup's; `PK.seed` is the game's;
  the secrets' digests are the sampled ones (`SecOk`); the targets are the keys in use on their
  messages (`TgOk`); the transcript is the build's evaluations, the targets and the reveal
  (`LogOk`); and on a live memory every public key position's cell was read by the challenger and
  logged with a value truncating to its digest (`KeyLogged`), with no charged read.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Qrom.SphEnc

open Quantum.StdModel Props Quantum.StdModel.Sphincs
open Quantum.Qrom.Sphincs (RawPos Pos slotInput)
open Quantum.StdModel.Qrom.EncTcr (Mem Gc)

/-! ## The cells of the classes -/

/-- **A cell of a class is the cell of an honest encoding input.** -/
theorem gc_kindCell {x : Quantum.Qrom.HashDomain} (h : Gc encCtr EncTwIn x) :
    KindCell encTwKinds x := by
  unfold Gc EncTcr.encTw at h
  split_ifs at h with hx
  · obtain ⟨t, ht, P, m, c, -, hc⟩ := hx
    cases t <;> simp only [EncTwIn] at ht
    rename_i a b d
    exact ⟨pubKey P, 0, .enc a b d, (m, BitVec.ofNat counterBits c), le_rfl, hc⟩
  · exact absurd rfl h

theorem gc_le (key : _root_.Sphincs.KeyGenerationAndSigning.ExpandedKey) (root : Digest)
    (s : Quantum.Sphincs.Slot) (p : Quantum.Qrom.Sphincs.SlotPayload s) :
    twInputCost (Gc encCtr EncTwIn) (slotInput key root s p) ≤ encTwKinds.of s :=
  twInputCost_le (fun _ ↦ gc_kindCell) key root s p

attribute [local instance] secretsSampleable encRndSampleable in
/-- **B4's setup reads no cell of a class.** -/
theorem encRedPre_gc :
    Common.QueryCostAtMost (encRedPre romWorld)
      (gCostR (Gc encCtr EncTwIn) (R' := EncCtrPorts)) 0 := by
  rw [SphInst.gCostR_eq_hcallCostOn]
  unfold encRedPre encCore
  exact ((liftW_sample_on _).bind fun s ↦ (liftW_sample_on _).bind fun _ ↦
    (buildDig_zero (encAsk_on s)).bind fun _ ↦ (encTargets_on _ _).bind fun _ ↦
      (portQ_on _).bind fun _ ↦ Common.isWeightBound_pure _ _ 0).mono le_rfl

/-- **B4's output reads at most six cells of the classes.** -/
theorem encRedPost_gc (a : EncData) (f : Forgery) (st : EncData × SignLog) :
    Common.QueryCostAtMost (encRedPost romWorld a f st)
      (gCostR (Gc encCtr EncTwIn) (R' := EncCtrPorts)) 6 := by
  rw [SphInst.gCostR_eq_hcallCostOn]
  unfold encRedPost
  exact (recVerify_mapM_tw (fun l ↦ liftW_hash_on (P := Gc encCtr EncTwIn) l)
    (hashKinds_hashQuery_on gc_le)
    (fun rv os ↦ encPick a.P a.tg (rv.2.zip os)) a.pk f.message f.signature).mono
      (by simp [verifyW_encTwKinds])

/-! ## The live invariant -/

/-- The charged reads B4 is allowed: the output's six and the judge's. -/
abbrev nB : ℕ := 7

/-- The input of a public key position, its payload read from the digests `tf`. -/
def keyInput (P : PublicParameter) (tf : RawPos → Digest) (p : RawPos) : HashInput :=
  slotInput (pubKey P) 0 (keySlot p) (keyPayload p tf)

/-- **Every public key position's cell is read by the challenger and logged** with a value
truncating to its digest. -/
def KeyLogged (P : PublicParameter) (tf : RawPos → Digest) (m : Mem nB) : Prop :=
  ∀ p : Pos, KeyPart p.1 → ¬IsSecret p.1 → ∃ x o,
    Quantum.Qrom.encodeInput (keyInput P tf p.1) = some x ∧ m.ax x = true ∧
      m.log x = some o ∧ truncateHash o = tf p.1

/-- The digests of the secret positions are the sampled secrets. -/
def SecOk (a : EncData) : Prop :=
  ∀ p : Pos, KeyPart p.1 → IsSecret p.1 → ∃ d, encSecDom p.1 = some d ∧ a.tf p.1 = a.s d

/-- The targets are the keys in use, in order, on their messages. -/
def TgOk (a : EncData) : Prop :=
  a.tg.map (fun x ↦ (x.1, x.2.1)) = encKeys.map fun K ↦ (K, keyMessage (ofDig a.tf) K)

/-- The transcript: the build's evaluations, the targets with their answers, the reveal. -/
def LogOk (a : EncData) (log : QueryLog EncCtrPorts) : Prop :=
  ∃ Tb, (∀ e ∈ Tb, EncEvalOk e) ∧ log = Tb ++ a.tg.map encEntry ++ [encRev a.P]

/-- **B4's live invariant** at the setup `a`, for the handler's state and transcript `x`. -/
def EncJu (P : PublicParameter) (a : EncData) (x : (EncData × SignLog) × QueryLog EncCtrPorts)
    (μ : Option (Mem nB)) : Prop :=
  x.1.1 = a ∧ a.P = P ∧ SecOk a ∧ TgOk a ∧ LogOk a x.2 ∧
    ∀ m, μ = some m → KeyLogged P a.tf m ∧ m.cnt.val = 0

end Quantum.StdModel.Qrom.SphEnc

end
