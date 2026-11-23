module

public import Quantum.Qrom.Sphincs.Multi.Runtime1

@[expose] public section

/-!
# leanSPHINCS's multi-user template game against runtime 1

The `n`-user analog of `Quantum.Qrom.Sphincs.GameT`. Runtime 1 with record ports, with the cells
of the table `tabOfN θ` at the master seeds `seedsOf θ` hardwired (`hwTN θ`), running the template
game realized at the hidden values `θ` at the hybrid side's digest policy (`msgPolN n`, any inner
memory and trial updates), has the law of the lifted multi-user game in runtime 1 when the table
is good (`runtime1R_muGameT_eqS`). Hence the win probability is at most the average over the hidden
values of the bad table fraction plus runtime 1 on the realized template
(`muWinProb_le_uavg_goodSN`).

* **Records** (`dropRec_muGameT`): the realized game is `muGameDN θ valid A` (over `hwSpec`,
  memory `Unit`) with record calls inserted and reads updating the memory.
* **Program calls** (`dropsTo_muGameD`): every program call of `muGameDN θ` hardwires a cell of
  `hwTN θ` with its value on good tables (`progsOfQN_hwTN`), so `muGameDN θ` is the read game
  `muGameReadsTN θ` with program calls inserted.
* **The grind-only signer** (`readsTo_signRN`, `signsSN_signRN`): user `i`'s signer `signRN`
  reads only the counter searches' trials of the keys it does not find in user `i`'s memo and
  takes every other value from `θ`; from a memo agreeing with the function it returns user `i`'s
  signature and memo answer, so `runtime1_muGame_eq_readsSN` applies.
-/

open Matrix
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open OracleComp OracleSpec

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime
open Quantum.Sponge (Hw hwSpec hwReadSpec hwReadCmdSpec keepMem readCall spongeHardwiredReadRuntime
  overwrite ReadsTo readsTo_pure ReadsTo.bind ReadsTo.map readsTo_readCall readAnswer)
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Xmss.Assembly (runtime1R realizeT realizeT_bind₂ revealThen progThen readLiftQ
  RevealVals DropRec ReadsRel readsRel_pure readsRel_readH_bind readsRel_act_bind liftReadC
  liftReadProg dropRec_realizeT_substitute dropRec_realizeT_act_bind dropRec_realizeT_bind
  dropRec_readLift_liftOrdinary evalDistMap_runtime1R_eq DropsTo ProgOf progCall
  dropsTo_liftReadProg dropsTo_substitute evalDistMap_runtime1_eq_spongeHardwiredReadRuntime)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge muGame muWinProb
  muWinProb_eq_uniform withMuSignLog)

attribute [local irreducible] sphincsRom

variable {n : ℕ}

-- The adversary's commands with the memo, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MemoPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpecS n)

/-! ## The realized game without reveals, and its read program -/

section programs

variable (θ : TValsN n)

/-- User `i`'s program calls of the positions `ps`, realized at `θ`. -/
noncomputable def progPosDN (i : Fin n) (B : QReg) :
    List Pos → QComp (hwSpec PairOut HashDomain Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall ((progTN i p).realize θ) B).bind fun _ ↦ progPosDN i B ps

/-- The value user `i`'s key `K` signs, revealed at `msgPos K`. -/
noncomputable def keyMsgDN (i : Fin n) (K : Key) : Digest :=
  (tabRN (restrictTo (atU i {vcoord (msgPos K)}) θ) i).valuePos (msgPos K)

/-- User `i`'s layer signature by `K` with counter `c` and codeword `x`, from the values revealed
on user `i`'s `layerReveal K x`. -/
noncomputable def layerSigDN (i : Fin n) (K : Key) (c : EncodingCounter) (x : Encoding) :
    LayerSignature K.1 :=
  ⟨c, fun j ↦ (tabRN (restrictTo (atU i (layerReveal K x)) θ) i).chainValue K.1 K.2.1 K.2.2 j
      (x j).val,
    (tabRN (restrictTo (atU i (layerReveal K x)) θ) i).authPath K.1 K.2.1 K.2.2⟩

/-- User `i`'s FORS opening of instance `idx` at the leaves `lv`, from the values revealed on
user `i`'s `forsReveal idx lv`. -/
noncomputable def forsDN (i : Fin n) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ForsTreeIndex → ForsTreeOpening :=
  (tabRN (restrictTo (atU i (forsReveal idx lv)) θ) i).forsOpening idx lv

/-- User `i`'s table revealed with `PK.seed`, `PK.root` and `R(M)`. -/
noncomputable def sigTabDN (i : Fin n) (msg : Message) : QTable :=
  tabRN (restrictTo (atU i {seedC, rootC, rndC msg}) θ) i

/-- User `i`'s digest of `M` at `msgPol`, from its revealed digest cell. -/
noncomputable def dgDN (i : Fin n) (msg : Message) : MessageDigest :=
  digestTN msgPol i ∅ msg (restrictTo (atU i (msgNeed msg)) θ)

/-- The users' public keys the game reveals. -/
noncomputable def pkDN : Fin n → PublicKey :=
  pksT (restrictTo pkRevealN θ)

/-- **User `i`'s counter search, realized with its reveal dropped**: the trials through read
ports keeping the memory. -/
noncomputable def selectDN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (hwSpec PairOut HashDomain Unit) B B SelS :=
  liftReadC (grindT Unit (keepUpd Unit) seed B K (keyMsgDN θ i K) encodingAttemptLimit 0)

/-- User `i`'s selection of `K` or its memo, realized with its reveal dropped. -/
noncomputable def selOrMemoDN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    Option SelS → QComp (hwSpec PairOut HashDomain Unit) B B SelS
  | some o => QuantumComp₂.pure o
  | none => selectDN θ i seed B K

/-- **User `i`'s layer publication, realized with its reveal dropped**: the program calls of the
positions it makes public, then the layer signature from the revealed values. -/
noncomputable def publishDN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) : QComp (hwSpec PairOut HashDomain Unit) B B (LayerSignature K.1) :=
  (progPosDN θ i B (layerPos K x)).bind fun _ ↦ QuantumComp₂.pure (layerSigDN θ i K c x)

/-- User `i`'s FORS opening, realized with its reveal dropped. -/
noncomputable def forsOpenDN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (hwSpec PairOut HashDomain Unit) B B (ForsTreeIndex → ForsTreeOpening) :=
  (progPosDN θ i B (forsPos idx lv)).bind fun _ ↦ QuantumComp₂.pure (forsDN θ i idx lv)

/-- The publication of user `i`'s signature, realized with its reveals dropped. -/
noncomputable def publishAllDN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) :
    SelS → SelS → SelS → QComp (hwSpec PairOut HashDomain Unit) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (forsOpenDN θ i B idx lv).bind fun fo ↦
    (publishDN θ i B (keyOf 0 idx) c₀ x₀).bind fun bottom ↦
    (publishDN θ i B (keyOf 1 idx) c₁ x₁).bind fun middle ↦
    (publishDN θ i B (keyOf 2 idx) c₂ x₂).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

/-- **User `i`'s signature at `msgPol` with memo `h`, realized with its reveals dropped.** -/
noncomputable def signDN (i : Fin n) (B : QReg) (msg : Message) (h : KeyMemo) :
    QComp (hwSpec PairOut HashDomain Unit) B B (Option Signature × MemoAns) :=
  (progCall ((digPortN msgPol i ∅ msg).realize θ) B).bind fun _ ↦
  (selOrMemoDN θ i (sigTabDN θ i msg).publicSeed B (keyOf 0 (digestIndex (dgDN θ i msg)))
      (h (keyOf 0 (digestIndex (dgDN θ i msg))))).bind fun g₀ ↦
  (selOrMemoDN θ i (sigTabDN θ i msg).publicSeed B (keyOf 1 (digestIndex (dgDN θ i msg)))
      (h (keyOf 1 (digestIndex (dgDN θ i msg))))).bind fun g₁ ↦
  (selOrMemoDN θ i (sigTabDN θ i msg).publicSeed B (keyOf 2 (digestIndex (dgDN θ i msg)))
      (h (keyOf 2 (digestIndex (dgDN θ i msg))))).bind fun g₂ ↦
  (publishAllDN θ i B (digestIndex (dgDN θ i msg)) (digestForsLeaves (dgDN θ i msg))
      ((sigTabDN θ i msg).randomizer msg) g₀ g₁ g₂).map fun s ↦
    (s, (digestIndex (dgDN θ i msg), layerSels g₀ g₁ g₂))

/-- **The challenger of the realized game with its reveals dropped.** -/
noncomputable def challengeDN :
    IPFunctor.CommandSubstitution (MemoPS n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec PairOut HashDomain Unit))
  | A, .prim o => liftReadProg ((liftH (regroupCalls hmsgRoute
      (muChallenge sphincsRom (noKeysS (n := n)) A (.prim o)))).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain Unit))
  | A, .query .hash E ℓ => liftReadProg ((liftH (regroupCalls hmsgRoute
      (muChallenge sphincsRom (noKeysS (n := n)) A (.query .hash E ℓ)))).liftOrdinary
        (t := hwReadCmdSpec PairOut HashDomain Unit))
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtSN i q E ℓ fun B ↦ signDN θ i B q.1 q.2) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The realized template game at `msgPolN n` with its reveals dropped** (over `hwSpec`, memory
`Unit`). -/
noncomputable def muGameDN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) :
    QComp (hwSpec PairOut HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeDN θ)
    (memoFromS (fun _ _ ↦ none) (withMuSignLog (A (pkDN θ))))) fun run ↦
    (liftReadC ((readsProgram Unit _ (sphincsRom.verify (pkDN θ run.1.1) run.1.2)).map
      Prod.fst)).bind fun b ↦
      QuantumComp₂.pure (pdOK (pkDN θ) && sphincsRom.winningCondition (run.2.user run.1.1)
        run.1.2 && run.2.allValid valid && b)

end programs

section reads

variable (M : Type) (θ : TValsN n)

/-- **User `i`'s counter search as reads**, on the value revealed from `θ`. -/
noncomputable def selectRN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (hwReadSpec PairOut HashDomain M) B B SelS :=
  grindT M (keepUpd M) seed B K (keyMsgDN θ i K) encodingAttemptLimit 0

/-- User `i`'s selection of `K` or its memo, as reads. -/
noncomputable def selOrMemoRN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    Option SelS → QComp (hwReadSpec PairOut HashDomain M) B B SelS
  | some o => QuantumComp₂.pure o
  | none => selectRN M θ i seed B K

/-- The publication of user `i`'s signature as reads: every value from the revealed values. -/
noncomputable def publishAllRN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) :
    SelS → SelS → SelS → QComp (hwReadSpec PairOut HashDomain M) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (QuantumComp₂.pure (forsDN θ i idx lv) :
        QComp (hwReadSpec PairOut HashDomain M) B B _).bind fun fo ↦
    (QuantumComp₂.pure (layerSigDN θ i (keyOf 0 idx) c₀ x₀) :
        QComp (hwReadSpec PairOut HashDomain M) B B _).bind fun bottom ↦
    (QuantumComp₂.pure (layerSigDN θ i (keyOf 1 idx) c₁ x₁) :
        QComp (hwReadSpec PairOut HashDomain M) B B _).bind fun middle ↦
    (QuantumComp₂.pure (layerSigDN θ i (keyOf 2 idx) c₂ x₂) :
        QComp (hwReadSpec PairOut HashDomain M) B B _).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

variable [Fintype M] [DecidableEq M]

/-- **The grind-only signer**: user `i`'s counter searches of the keys missing from user `i`'s
memo through read ports, every other value of the signature from the revealed values. -/
noncomputable def signRN : SignerSN M n :=
  fun i msg h B ↦
  (selOrMemoRN M θ i (sigTabDN θ i msg).publicSeed B (keyOf 0 (digestIndex (dgDN θ i msg)))
      (h (keyOf 0 (digestIndex (dgDN θ i msg))))).bind fun g₀ ↦
  (selOrMemoRN M θ i (sigTabDN θ i msg).publicSeed B (keyOf 1 (digestIndex (dgDN θ i msg)))
      (h (keyOf 1 (digestIndex (dgDN θ i msg))))).bind fun g₁ ↦
  (selOrMemoRN M θ i (sigTabDN θ i msg).publicSeed B (keyOf 2 (digestIndex (dgDN θ i msg)))
      (h (keyOf 2 (digestIndex (dgDN θ i msg))))).bind fun g₂ ↦
  (publishAllRN M θ i B (digestIndex (dgDN θ i msg)) (digestForsLeaves (dgDN θ i msg))
      ((sigTabDN θ i msg).randomizer msg) g₀ g₁ g₂).map fun s ↦
    (s, (digestIndex (dgDN θ i msg), layerSels g₀ g₁ g₂))

/-- **The game's reads with the grind-only signer.** -/
noncomputable def muGameReadsTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) :
    QComp (hwReadSpec PairOut HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsWithSN M (signRN M θ) (pkDN θ) valid A

end reads

/-! ## Dropping the reveals and the record calls -/

section records

variable {M : Type} (θ : TValsN n) {B : QReg}

theorem readsRel_romReadImplN (x : RomOracles.Domain) (log : List HashDomain) :
    ReadsRel (goodQN (n := n)) θ ((romReadImpl M B x).run log)
      ((romReadImpl Unit B x).run log) := by
  rcases x with k | y
  · change ReadsRel goodQN θ
      ((QComp.coinImpl (hwReadSpec PairOut HashDomain M) B k).bind fun a ↦
        QuantumComp₂.pure (a, log))
      ((QComp.coinImpl (hwReadSpec PairOut HashDomain Unit) B k).bind fun a ↦
        QuantumComp₂.pure (a, log))
    exact readsRel_act_bind (good := goodQN) θ _ fun a ↦ readsRel_pure θ (a, log)
  · change ReadsRel goodQN θ
      ((readCall (.readH (hmsgRoute (y, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (y, false)).2 (r.1.getD 0), log ++ [y]))
      ((readCall (.readH (hmsgRoute (y, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (y, false)).2 (r.1.getD 0), log ++ [y]))
    exact readsRel_readH_bind θ _ keepMem keepMem fun _ _ ↦ readsRel_pure θ _

theorem readsRel_simulateQN {α : Type} (x : OracleComp RomOracles α) (log : List HashDomain) :
    ReadsRel (goodQN (n := n)) θ ((simulateQ (romReadImpl M B) x).run log)
      ((simulateQ (romReadImpl Unit B) x).run log) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [simulateQ_pure, simulateQ_pure]
    exact readsRel_pure θ (a, log)
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    exact (readsRel_romReadImplN θ q log).bind fun p ↦ ih p.1 p.2

/-- **The read program of a computation at memories `M` and `Unit`.** -/
theorem readsRel_readsProgramN {α : Type} (x : OracleComp RomOracles α) :
    ReadsRel (goodQN (n := n)) θ (readsProgram M B x) (readsProgram Unit B x) :=
  readsRel_simulateQN θ x []

/-- **The counter search at memories `M` and `Unit`.** -/
theorem readsRel_grindTN (upd : TrialUpd M) (seed : PublicParameter) (K : Key) (m : Digest) :
    ∀ k c, ReadsRel (goodQN (n := n)) θ (grindT M upd seed B K m k c)
      (grindT Unit (keepUpd Unit) seed B K m k c)
  | 0, _ => readsRel_pure θ _
  | k + 1, c => by
    rw [grindT, grindT]
    refine readsRel_readH_bind θ _ _ _ fun o _ ↦ ?_
    dsimp only
    generalize TargetSum.decodeDigest (truncateHash (o.getD 0).1) = d
    cases d with
    | none => exact readsRel_grindTN upd seed K m k (c + 1)
    | some x => exact readsRel_pure θ _

theorem dropRec_revealThenN {C : QReg} {α : Type} (T : Finset (TPosN n))
    (k : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B C α)
    {y : QComp (hwSpec PairOut HashDomain Unit) B C α}
    (h : ∀ r, DropRec (TPosN n) (realizeT θ (k (restrictTo T θ, r))) y) :
    DropRec (TPosN n) (realizeT θ (revealThen goodQN T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThenN {C : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) {k : QComp (XSpecSN M n) B C α}
    {y : QComp (hwSpec PairOut HashDomain Unit) B C α} (h : DropRec (TPosN n) (realizeT θ k) y) :
    DropRec (TPosN n) (realizeT θ (progThen p trivial k))
      ((progCall (p.realize θ) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize θ) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT θ k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPosN (i : Fin n) (B : QReg) :
    ∀ ps : List Pos, DropRec (TPosN n) (realizeT θ (progPosN M i B ps)) (progPosDN θ i B ps)
  | [] => .pure _
  | _ :: ps => dropRec_progThenN θ _ (dropRec_progPosN i B ps)

variable (upd : Fin n → TrialUpd M)

theorem dropRec_selectTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    DropRec (TPosN n) (realizeT θ (selectTN M upd i seed B K)) (selectDN θ i seed B K) := by
  unfold selectTN
  exact dropRec_revealThenN θ _ _ fun _ ↦ readsRel_grindTN θ (upd i) seed K _ _ _

theorem dropRec_selOrMemoTN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    ∀ o : Option SelS, DropRec (TPosN n) (realizeT θ (selOrMemoTN M upd i seed B K o))
      (selOrMemoDN θ i seed B K o)
  | some _ => .pure _
  | none => dropRec_selectTN θ upd i seed B K

theorem dropRec_publishTN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) :
    DropRec (TPosN n) (realizeT θ (publishTN M i B K c x)) (publishDN θ i B K c x) := by
  unfold publishTN
  refine dropRec_revealThenN θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPosN θ i B _) fun _ ↦ .pure _

theorem dropRec_forsOpenTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    DropRec (TPosN n) (realizeT θ (forsOpenTN M i B idx lv)) (forsOpenDN θ i B idx lv) := by
  unfold forsOpenTN
  refine dropRec_revealThenN θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPosN θ i B _) fun _ ↦ .pure _

theorem dropRec_publishAllTN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    DropRec (TPosN n) (realizeT θ (publishAllTN M i B idx lv R g₀ g₁ g₂))
      (publishAllDN θ i B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact .pure _
  simp only [publishAllTN, publishAllDN, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_forsOpenTN θ i B _ _) fun _ ↦
    DropRec.bind₂ (dropRec_publishTN θ i B _ _ _) fun _ ↦
      DropRec.bind₂ (dropRec_publishTN θ i B _ _ _) fun _ ↦
        DropRec.bind₂ (dropRec_publishTN θ i B _ _ _) fun _ ↦ .pure _

theorem dropRec_signTN (i : Fin n) (B : QReg) (msg : Message) (h : KeyMemo) :
    DropRec (TPosN n) (realizeT θ (signTN M upd (msgPolN n) i B msg h)) (signDN θ i B msg h) := by
  unfold signTN signDN
  refine dropRec_revealThenN θ _ _ fun _ ↦ dropRec_revealThenN θ _ _ fun _ ↦ ?_
  refine dropRec_progThenN θ _ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selOrMemoTN θ upd i _ B _ _) fun _ ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_publishAllTN θ i B _ _ _ _ _ _) fun _ ↦ .pure _

theorem dropRec_challengeTN (A : QReg) (c : (MemoPS n).A A) :
    DropRec (TPosN n) (realizeT θ (challengeTN M upd (msgPolN n) A c)) (challengeDN θ A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_readLift_liftOrdinary θ _
  · refine dropRec_realizeT_bind θ ?_ fun _ _ ↦ .pure _
    exact dropRec_realizeT_act_bind θ _ fun _ ↦ dropRec_signTN θ upd i _ q.1 q.2

/-- **The realized game drops to `muGameDN`**: with its record calls removed and its reads keeping
the memory `Unit`, the realized template game at `msgPolN n` is `muGameDN θ valid A`. -/
theorem dropRec_muGameT (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) :
    DropRec (TPosN n) (realizeT θ (muGameT M upd (msgPolN n) valid A)) (muGameDN θ valid A) := by
  unfold muGameT
  refine dropRec_revealThenN θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂, muGameDN]
  refine DropRec.bind₂ (dropRec_realizeT_substitute θ (dropRec_challengeTN θ upd) _) fun _ ↦ ?_
  rw [verifyTN, readsThenTN_eq, realizeT_bind₂]
  exact DropRec.bind₂ ((readsRel_readsProgramN θ _).map Prod.fst) fun _ ↦ .pure _

end records

/-! ## Dropping the program calls -/

section drops

variable (W : Hw PairOut HashDomain) (θ : TValsN n)

/-- **Every program call of `muGameDN θ` hardwires a cell of `W` with its `W` value**: the
realized ports of the users' structural positions and digest cells. -/
def ProgsOfQN : Prop :=
  (∀ (i : Fin n) (p : Pos), p.1.IsStruct → ProgOf W ((progTN i p).realize θ)) ∧
    ∀ (i : Fin n) (msg : Message), ProgOf W ((digPortN msgPol i ∅ msg).realize θ)

variable {W θ}

theorem dropsTo_progPosDN (i : Fin n) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec PairOut HashDomain Unit) B C α}
    {y : QComp (hwReadSpec PairOut HashDomain Unit) B C α} (hx : DropsTo W x y) :
    ∀ ps : List Pos, (∀ p ∈ ps, ProgOf W ((progTN i p).realize θ)) →
      DropsTo W ((progPosDN θ i B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPosDN, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPosDN i B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

variable (h : ProgsOfQN W θ)
include h

theorem dropsTo_publishDN (i : Fin n) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) :
    DropsTo W (publishDN θ i B K c x) (QuantumComp₂.pure (layerSigDN θ i K c x)) :=
  dropsTo_progPosDN i B (DropsTo.pure _) _ fun p hp ↦ h.1 i p (isStruct_of_mem_layerPos hp)

theorem dropsTo_forsOpenDN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    DropsTo W (forsOpenDN θ i B idx lv) (QuantumComp₂.pure (forsDN θ i idx lv)) :=
  dropsTo_progPosDN i B (DropsTo.pure _) _ fun p hp ↦ h.1 i p (isStruct_of_mem_forsPos hp)

theorem dropsTo_publishAllDN (i : Fin n) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) :
    DropsTo W (publishAllDN θ i B idx lv R g₀ g₁ g₂)
      (publishAllRN Unit θ i B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact DropsTo.pure _
  exact DropsTo.bind₂ (dropsTo_forsOpenDN h i B _ _) fun _ ↦
    DropsTo.bind₂ (dropsTo_publishDN h i B _ _ _) fun _ ↦
      DropsTo.bind₂ (dropsTo_publishDN h i B _ _ _) fun _ ↦
        DropsTo.bind₂ (dropsTo_publishDN h i B _ _ _) fun _ ↦ DropsTo.pure _

omit h in
theorem dropsTo_selOrMemoDN (i : Fin n) (seed : PublicParameter) (B : QReg) (K : Key) :
    ∀ o : Option SelS, DropsTo W (selOrMemoDN θ i seed B K o) (selOrMemoRN Unit θ i seed B K o)
  | some _ => DropsTo.pure _
  | none => dropsTo_liftReadProg W _

theorem dropsTo_signDN (i : Fin n) (B : QReg) (msg : Message) (o : KeyMemo) :
    DropsTo W (signDN θ i B msg o) (signRN Unit θ i msg o B) := by
  unfold signDN signRN
  refine DropsTo.progCall_bind _ (h.2 i msg) ?_
  refine DropsTo.bind₂ (dropsTo_selOrMemoDN i _ B _ _) fun _ ↦ ?_
  refine DropsTo.bind₂ (dropsTo_selOrMemoDN i _ B _ _) fun _ ↦ ?_
  refine DropsTo.bind₂ (dropsTo_selOrMemoDN i _ B _ _) fun _ ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  exact DropsTo.bind₂ (dropsTo_publishAllDN h i B _ _ _ _ _ _) fun _ ↦ DropsTo.pure _

theorem dropsTo_challengeDN (A : QReg) (c : (MemoPS n).A A) :
    DropsTo W (challengeDN θ A c) (challengeWithSN Unit (signRN Unit θ) A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · refine DropsTo.bind ?_ fun _ _ ↦ DropsTo.pure _
    rw [signAtSN, signAtSN, QComp.act_bind, QComp.act_bind]
    exact DropsTo.prim _ fun _ ↦ dropsTo_signDN h i _ q.1 q.2

/-- **The realized game with its reveals dropped is its read program with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_muGameD (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) : DropsTo W (muGameDN θ valid A) (muGameReadsTN Unit θ valid A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeDN h) _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ DropsTo.pure _

end drops

/-! ## At a good table, the game programs the table's cells -/

section table

/-- **The hardwired cells of runtime 1 at the hidden values `θ`**: the cells of the table
`tabOfN θ` at the master seeds `seedsOf θ`, with their values. -/
noncomputable def hwTN (θ : TValsN n) : Hw PairOut HashDomain :=
  (tableN (seedsOf θ)).hwOf (tabOfN θ)

theorem hwTN_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    hwTN (thetaOfN S0 w) = (tableN S0).hwOf w := by
  unfold hwTN
  rw [seedsOf_thetaOfN, tabOfN_thetaOfN]

/-- **At the hidden values `θ` of a good table, the game programs cells of `hwTN θ` with their
values.** -/
theorem progsOfQN_hwTN (θ : TValsN n) (hw : (tableN (seedsOf θ)).good (tabOfN θ)) :
    ProgsOfQN (hwTN θ) θ := by
  refine ⟨fun i p hp ↦ ?_, fun i msg ↦ ?_⟩
  · rw [realize_progTN hp i θ]
    exact (tableN (seedsOf θ)).tableDb_cell hw (tabOfN θ) (i, p)
  · rw [realize_digPortN_msgPol i ∅ msg θ]
    exact (tableN (seedsOf θ)).tableDb_cell hw (tabOfN θ) (i, digPos msg)

end table

/-! ## The grind-only signer against the functions consistent with the table -/

section honest

variable {θ : TValsN n} {M : Type} [Fintype M] [DecidableEq M]
  {t : (HashDomain → PairOut) × (PairOut → HashDomain) × (PairOut → HashDomain)}
  {W : Hw PairOut HashDomain} {m : M} {B : QReg}

/-- **The counter search through read ports returns the table's selection**, at any memory. -/
theorem readsTo_grindTS (v : QTable) (K : Key) (msg : Digest) : ∀ k c,
    ReadsTo t W m (grindT M (keepUpd M) v.publicSeed B K msg k c)
      (v.selectFrom (regroup hmsgRoute (overwrite W t).1) K.1 K.2.1 K.2.2 msg k c)
  | 0, _ => readsTo_pure _
  | k + 1, c => by
    rw [grindT]
    refine (readsTo_readCall (.readH (trialCell v.publicSeed K msg c)
      (keepUpd M K (trialCell v.publicSeed K msg c))) rfl B).bind ?_
    rw [QTable.selectFrom, QTable.encDigest,
      show regroup hmsgRoute (overwrite W t).1
          (encCell v.publicSeed K.1 K.2.1 K.2.2 msg (BitVec.ofNat counterBits c)) =
        ((readAnswer t W m (.readH (trialCell v.publicSeed K msg c)
          (keepUpd M K (trialCell v.publicSeed K msg c)))).1.getD 0).1 from
        regroup_encCell _ _ _ _ _ _ _]
    generalize TargetSum.decodeDigest (truncateHash ((readAnswer t W m
      (.readH (trialCell v.publicSeed K msg c)
        (keepUpd M K (trialCell v.publicSeed K msg c)))).1.getD 0).1) = d
    cases d with
    | none => exact readsTo_grindTS v K msg k (c + 1)
    | some x => exact readsTo_pure _

theorem readsTo_map_pairS {α β : Type} {x : QComp (hwReadSpec PairOut HashDomain M) B B α}
    {a : α} (b : β) (hx : ReadsTo t W m x a) : ReadsTo t W m (x.map fun s ↦ (s, b)) (a, b) :=
  hx.map _

/-- User `i`'s values revealed on `atU i U` agree with `θ` on `U`. -/
theorem pairAt_atU_restrictTo {i : Fin n} {U : Finset TPos} {s : TPos} (hs : s ∈ U)
    (θ : TValsN n) :
    pairAt (SValsN.user (extWN (restrictTo (atU i U) θ)) i) s = pairAt (userOf θ i) s :=
  pairRN_restrictTo (mk_mem_atU i hs) θ

theorem keyMsgDN_keyOf (i : Fin n) (l : Layer) (idx : Index) :
    keyMsgDN θ i (keyOf l idx) = (tabOf (userOf θ i)).layerMessage idx l :=
  (valuePos_tabOf_congr _ (pairAt_atU_restrictTo (Finset.mem_singleton_self _) θ)).trans
    ((tabOf (userOf θ i)).msgPos_eq l idx)

theorem layerSigDN_eq (i : Fin n) (K : Key) (c : EncodingCounter) (x : Encoding) :
    layerSigDN θ i K c x =
      ⟨c, fun j ↦ (tabOf (userOf θ i)).chainValue K.1 K.2.1 K.2.2 j (x j).val,
        (tabOf (userOf θ i)).authPath K.1 K.2.1 K.2.2⟩ := by
  have hc : ∀ j, (tabRN (restrictTo (atU i (layerReveal K x)) θ) i).chainValue K.1 K.2.1 K.2.2 j
      (x j).val = (tabOf (userOf θ i)).chainValue K.1 K.2.1 K.2.2 j (x j).val := fun j ↦
    chainValue_tabOf_congr (pairAt_atU_restrictTo (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))) θ)
  have hp : (tabRN (restrictTo (atU i (layerReveal K x)) θ) i).authPath K.1 K.2.1 K.2.2 =
      (tabOf (userOf θ i)).authPath K.1 K.2.1 K.2.2 := funext fun z ↦
    treeValue_tabOf_congr (pairAt_atU_restrictTo (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun z : Fin (layerHeight K.1) ↦
        treeC K.1 K.2.1 z.val ((K.2.2.val >>> z.val) ^^^ 1)) (Finset.mem_univ z))) θ)
  unfold layerSigDN
  simp only [hc, hp]

theorem forsDN_eq (i : Fin n) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsDN θ i idx lv = (tabOf (userOf θ i)).forsOpening idx lv := by
  funext κ
  have h1 : (tabRN (restrictTo (atU i (forsReveal idx lv)) θ) i).forsSecret idx κ (lv κ) =
      (tabOf (userOf θ i)).forsSecret idx κ (lv κ) :=
    dig_tabOf_congr (pairAt_atU_restrictTo (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ κ)))) θ)
  have h2 : ∀ z : Fin forsTreeHeight,
      (tabRN (restrictTo (atU i (forsReveal idx lv)) θ) i).forsValue idx κ z.val
        (((lv κ).val >>> z.val) ^^^ 1) =
      (tabOf (userOf θ i)).forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1) := fun z ↦
    forsValue_tabOf_congr (pairAt_atU_restrictTo (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun q : ForsTreeIndex × Fin forsTreeHeight ↦
        forsC idx q.1 q.2.val (((lv q.1).val >>> q.2.val) ^^^ 1)) (Finset.mem_univ (κ, z)))) θ)
  exact congrArg₂ ForsTreeOpening.mk h1 (funext h2)

theorem dgDN_eq (i : Fin n) (msg : Message) :
    dgDN θ i msg = (tabOf (userOf θ i)).messageDigest msg := by
  unfold dgDN digestTN
  rw [messageDigest_eq_digestOfPair, tabOf_digPos]
  exact congrArg digestOfPair (pairRN_restrictTo (mk_mem_atU i (Finset.mem_singleton_self _)) θ)

theorem sigTabDN_publicSeed (i : Fin n) (msg : Message) :
    (sigTabDN θ i msg).publicSeed = (tabOf (userOf θ i)).publicSeed :=
  publicSeed_tabOf_congr (pairAt_atU_restrictTo (by simp) θ)

theorem sigTabDN_randomizer (i : Fin n) (msg : Message) :
    (sigTabDN θ i msg).randomizer msg = (tabOf (userOf θ i)).randomizer msg :=
  randomizer_tabOf_congr (pairAt_atU_restrictTo (by simp) θ)

theorem pkDN_eq (θ : TValsN n) (i : Fin n) : pkDN θ i = (tabOf (userOf θ i)).publicKey :=
  congrArg₂ Sphincs.PublicKey.mk
    (publicSeed_tabOf_congr (pairRN_restrictTo
      (Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩) θ))
    (root_tabOf_congr (pairRN_restrictTo
      (Finset.mem_product.2 ⟨Finset.mem_univ _,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) θ))

theorem layerSels_self (g : Layer → SelS) : layerSels (g 0) (g 1) (g 2) = g := by
  funext l
  fin_cases l <;> rfl

/-- **User `i`'s selection of `K_l(idx)` or its memo returns the table's selection**, from a memo
of user `i` agreeing with the function. -/
theorem readsTo_selOrMemoRN (i : Fin n) (l : Layer) (idx : Index) (h : KeyMemo)
    (hh : ∀ K o, h K = some o →
      o = keySel (tabOf (userOf θ i)) (regroup hmsgRoute (overwrite W t).1) K) :
    ReadsTo t W m
      (selOrMemoRN M θ i (tabOf (userOf θ i)).publicSeed B (keyOf l idx) (h (keyOf l idx)))
      ((tabOf (userOf θ i)).select (regroup hmsgRoute (overwrite W t).1) l (treeOfIndex l idx)
        (leafOfIndex l idx) ((tabOf (userOf θ i)).layerMessage idx l)) := by
  rcases hK : h (keyOf l idx) with _ | g
  · rw [selOrMemoRN, selectRN, keyMsgDN_keyOf]
    exact readsTo_grindTS (tabOf (userOf θ i)) _ _ _ _
  · rw [hh _ g hK, keySel_keyOf]
    exact readsTo_pure _

/-- **The grind-only signer returns user `i`'s signature and memo answer** against the functions
consistent with the table, from a memo of user `i` agreeing with the function. -/
theorem readsTo_signRN (θ : TValsN n) (i : Fin n) (msg : Message) (h : KeyMemo)
    (hh : ∀ K o, h K = some o →
      o = keySel (tabOf (userOf θ i)) (regroup hmsgRoute (overwrite W t).1) K) :
    ReadsTo t W m (signRN M θ i msg h B)
      ((tabOf (userOf θ i)).signature (regroup hmsgRoute (overwrite W t).1) msg,
        memoAnsOf (tabOf (userOf θ i)) (regroup hmsgRoute (overwrite W t).1) msg) := by
  have hi : (tabOf (userOf θ i)).index msg = digestIndex (dgDN θ i msg) := by
    rw [dgDN_eq]
    rfl
  have hv : (tabOf (userOf θ i)).leaves msg = digestForsLeaves (dgDN θ i msg) := by
    rw [dgDN_eq]
    rfl
  have hm : memoAnsOf (tabOf (userOf θ i)) (regroup hmsgRoute (overwrite W t).1) msg =
      ((tabOf (userOf θ i)).index msg, layerSels
        ((tabOf (userOf θ i)).layerSelect (regroup hmsgRoute (overwrite W t).1)
          ((tabOf (userOf θ i)).index msg) 0)
        ((tabOf (userOf θ i)).layerSelect (regroup hmsgRoute (overwrite W t).1)
          ((tabOf (userOf θ i)).index msg) 1)
        ((tabOf (userOf θ i)).layerSelect (regroup hmsgRoute (overwrite W t).1)
          ((tabOf (userOf θ i)).index msg) 2)) :=
    congrArg (Prod.mk _) (layerSels_self fun l ↦ (tabOf (userOf θ i)).layerSelect
      (regroup hmsgRoute (overwrite W t).1) ((tabOf (userOf θ i)).index msg) l).symm
  rw [hm]
  unfold signRN
  rw [sigTabDN_publicSeed, sigTabDN_randomizer, ← hi, ← hv]
  unfold QTable.signature QTable.layerSig QTable.layerSignature QTable.layerSelect
  refine (readsTo_selOrMemoRN i 0 _ h hh).bind ?_
  refine (readsTo_selOrMemoRN i 1 _ h hh).bind ?_
  refine (readsTo_selOrMemoRN i 2 _ h hh).bind ?_
  rcases (tabOf (userOf θ i)).select (regroup hmsgRoute (overwrite W t).1) 0
      (treeOfIndex 0 ((tabOf (userOf θ i)).index msg))
      (leafOfIndex 0 ((tabOf (userOf θ i)).index msg))
      ((tabOf (userOf θ i)).layerMessage ((tabOf (userOf θ i)).index msg) 0) with _ | ⟨c₀, x₀⟩ <;>
    rcases (tabOf (userOf θ i)).select (regroup hmsgRoute (overwrite W t).1) 1
      (treeOfIndex 1 ((tabOf (userOf θ i)).index msg))
      (leafOfIndex 1 ((tabOf (userOf θ i)).index msg))
      ((tabOf (userOf θ i)).layerMessage ((tabOf (userOf θ i)).index msg) 1) with _ | ⟨c₁, x₁⟩ <;>
    rcases (tabOf (userOf θ i)).select (regroup hmsgRoute (overwrite W t).1) 2
      (treeOfIndex 2 ((tabOf (userOf θ i)).index msg))
      (leafOfIndex 2 ((tabOf (userOf θ i)).index msg))
      ((tabOf (userOf θ i)).layerMessage ((tabOf (userOf θ i)).index msg) 2) with _ | ⟨c₂, x₂⟩ <;>
    try exact readsTo_map_pairS _ (readsTo_pure (none : Option Signature))
  refine readsTo_map_pairS _ ?_
  rw [publishAllRN, forsDN_eq, layerSigDN_eq, layerSigDN_eq, layerSigDN_eq]
  exact (readsTo_pure _).bind ((readsTo_pure _).bind ((readsTo_pure _).bind
    ((readsTo_pure _).bind (readsTo_pure _))))

variable (M) in
/-- **The grind-only signer satisfies `SignsSN`** at the table of the hidden values. -/
theorem signsSN_signRN (θ : TValsN n)
    (t : (HashDomain → PairOut) × (PairOut → HashDomain) × (PairOut → HashDomain))
    (W : Hw PairOut HashDomain) (m : M) : SignsSN t W m (tabOfN θ) (signRN M θ) :=
  fun i r h _ hh ↦ readsTo_signRN θ i r h hh

variable (M) in
theorem muGameReadsTN_eq (θ : TValsN n)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    muGameReadsTN M θ valid A =
      gameReadsWithSN M (signRN M θ) (fun i ↦ ((tabOfN θ).user i).publicKey) valid A := by
  rw [muGameReadsTN, show pkDN θ = fun i ↦ ((tabOfN θ).user i).publicKey from
    funext (pkDN_eq θ)]

end honest

/-! ## Runtime 1 on the realized template -/

section main

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **Runtime 1 runs the realized template as the lifted game** at a good table: runtime 1 with
record ports, the cells of `tabOfN θ` at `seedsOf θ` hardwired from the start, from any memory and
for any trial updates, running the template game at `msgPolN n` realized at `θ`, has the law of the
lifted multi-user game in runtime 1 with the same cells hardwired. -/
theorem runtime1R_muGameT_eqS (upd : Fin n → TrialUpd M) (θ : TValsN n)
    (hw : (tableN (seedsOf θ)).good (tabOfN θ))
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (m₀ : Finset (TPosN n) × M) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (runtime1R PairOut HashDomain (hwTN θ) m₀).evalDistMap .instruments
        (realizeT θ (muGameT M upd (msgPolN n) valid A)) ρ f =
      (spongeHardwiredReadRuntime PairOut HashDomain (hwTN θ) ()).evalDistMap .instruments
        (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid (seedsOf θ) A))).liftOrdinary
        ρ f := by
  rw [evalDistMap_runtime1R_eq _ m₀ (dropRec_muGameT θ upd valid A),
    evalDistMap_runtime1_eq_spongeHardwiredReadRuntime _ ()
      (dropsTo_muGameD (progsOfQN_hwTN θ hw) valid A), muGameReadsTN_eq]
  exact runtime1_muGame_eq_readsSN (seedsOf θ) hw () (fun t ↦ signsSN_signRN Unit θ t _ ())
    valid A ρ f

/-- The lifted game's win at the master seeds `S0` in runtime 1 with the cells of `w`
hardwired on good tables, plus the indicator of a bad table. -/
noncomputable def winGoodSN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) (S0 : Fin n → MasterSeed) (w : QTableN n) : ℝ≥0∞ :=
  (if (tableN S0).good w then 0 else 1) +
    if (tableN S0).good w then
      (spongeHardwiredReadRuntime PairOut HashDomain ((tableN S0).hwOf w) ()).evalDistMap
        .instruments (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A))).liftOrdinary
        (SubState.basis ()) winObsQ {true}
    else 0

theorem good_runtime1R_eq_winGoodSN (upd : Fin n → TrialUpd M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (m₀ : Finset (TPosN n) × M) (θ : TValsN n) :
    ((if (tableN (seedsOf θ)).good (tabOfN θ) then (0 : ℝ≥0∞) else 1) +
      if (tableN (seedsOf θ)).good (tabOfN θ) then
        (runtime1R PairOut HashDomain (hwTN θ) m₀).evalDistMap .instruments
          (realizeT θ (muGameT M upd (msgPolN n) valid A)) (SubState.basis ()) winObsQ {true}
      else 0) = winGoodSN valid A (seedsOf θ) (tabOfN θ) := by
  unfold winGoodSN
  by_cases hg : (tableN (seedsOf θ)).good (tabOfN θ)
  · simp only [hg, ↓reduceIte]
    rw [runtime1R_muGameT_eqS upd θ hg valid A m₀]
    rfl
  · simp only [hg, ↓reduceIte]

/-- **The win probability is at most the average over the hidden values of the bad table
indicator plus runtime 1 with record ports on the realized template game at good tables** (the
hybrid side, `msgPolN n`), from any memory and for any trial updates. -/
theorem muWinProb_le_uavg_goodSN (upd : Fin n → TrialUpd M)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (m₀ : Finset (TPosN n) × M) :
    muWinProb sphincsRom valid n A ≤ uavg (fun θ : TValsN n ↦
      (if (tableN (seedsOf θ)).good (tabOfN θ) then (0 : ℝ≥0∞) else 1) +
        if (tableN (seedsOf θ)).good (tabOfN θ) then
          (runtime1R PairOut HashDomain (hwTN θ) m₀).evalDistMap .instruments
            (realizeT θ (muGameT M upd (msgPolN n) valid A)) (SubState.basis ()) winObsQ {true}
        else 0) := by
  have hcard : (Fintype.card MasterSeed : ℝ≥0∞) = 2 ^ 256 := by
    rw [Fintype.card_congr (Quantum.Xmss.bitsEquiv 256)]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  simp only [good_runtime1R_eq_winGoodSN upd valid A m₀]
  rw [uavg_seedsOf_tabOfN (winGoodSN valid A), Quantum.Qrom.Sphincs.uavg_prod_eq,
    muWinProb_eq_uniform sphincsRom valid prEvent_sampleSeed_rom A,
    Fintype.card_fun (α := Fin n) (β := MasterSeed), Fintype.card_fin, Nat.cast_pow, hcard]
  refine mul_le_mul' (le_of_eq ENNReal.inv_pow.symm) (Finset.sum_le_sum fun S0 _ ↦ ?_)
  refine (qromEvalDistMap_muGame_le_tableS S0 () valid A
    (fun _ ↦ (liftH (regroupCalls hmsgRoute (muGame sphincsRom valid S0 A))).liftOrdinary)
    (SubState.basis ()) winObsQ (fun _ _ ↦ rfl) {true}).trans (le_of_eq ?_)
  simp only [winGoodSN]
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [Finset.card_filter, Nat.cast_sum]
    exact congrArg _ (Finset.sum_congr rfl fun w _ ↦ by
      by_cases hg : (tableN S0).good w <;> simp [hg])
  · rw [Finset.mul_sum]

end main

end Quantum.Qrom.Sphincs.Multi

end
