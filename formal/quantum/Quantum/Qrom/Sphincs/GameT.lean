module

public import Quantum.Qrom.Sphincs.Template
public import Quantum.Qrom.Sphincs.Runtime1
public import Quantum.Xmss.Assembly.RecordDrop
public import Quantum.Qrom.Sphincs.Events

@[expose] public section

/-!
# leanSPHINCS's QROM template game against runtime 1

Runtime 1 with record ports (`Quantum.Xmss.Assembly.runtime1R`), with the cells of the table
`tabOf θ` at the master seed `seedOf θ` hardwired (`hwT θ`), running the realized template game at
the hybrid side's digest policy (`realizeT θ (gameT M upd msgPol A)`, any inner memory and trial
update), has the law of runtime 1 of `Quantum.Qrom.Sphincs.Runtime1` running the game's read
program `gameReads Unit A ((tabOf θ).publicKey, seedOf θ)` (`evalDistMap_runtime1R_gameT`).
Hence the QROM game's law is the average over the table values of the realized template's law in
runtime 1 with record ports (`qrom_game_eq_runtime1R`).

* **Records** (`dropRec_gameT`): the realized game is `gameD θ A` (over `hwSpec`, memory `Unit`)
  with record calls inserted and reads updating the memory (`Quantum.Xmss.Assembly.DropRec`;
  `evalDistMap_runtime1R_eq` forgets the memory).
* **Program calls** (`dropsTo_gameD`): every program call of `gameD θ A` hardwires a cell of
  `hwT θ` with its value (`progsOf_hwT`: the realized ports of structural positions and the digest
  cells are the table's cells, `realize_progT`, `realize_digPort_msgPol`), so `gameD θ A` is the
  grind-only read game `gameReadsT θ A` with program calls inserted
  (`Quantum.Xmss.Assembly.DropsTo`).
* **The grind-only signer** (`readsTo_signR`): against the functions consistent with the table,
  every read is deterministic and the signer that reads only the counter searches' trials returns
  the table's signature; the game intertwines with `gameReadsT θ A`
  (`evalDistMap_game_eq_gameReadsT`), as it does with `gameReads` (`Runtime1`), so the two read
  programs have the same law in runtime 1 (`evalDistMap_gameReads_eq_gameReadsT`).
-/

open Matrix
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open OracleComp OracleSpec

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime
open Quantum.Sponge (Hw hwSpec hwReadSpec hwReadCmdSpec keepMem readCall spongeFnReadRuntime
  spongeHardwiredReadRuntime overwrite ReadsTo readsTo_pure ReadsTo.bind ReadsTo.map
  readsTo_readCall readAnswer hwAt hwCol hwAt_basis conjTranspose_hwCol_mul_self
  intertwines_run_pure
  intertwines_run₂_pure intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂
  intertwines_run₂_of_run intertwines_run_bind intertwines_substitute run₂_bind_of_classicalOn_pure
  evalDistMap_eq_of_intertwines read_port_eq_classical_read)
open Quantum.Sphincs (Key keyOf msgPos uavg_comp_equiv)
open Quantum.Xmss.Hybrid (LazyProg restrictTo uavg)
open Quantum.Xmss.Assembly (recHwSpec runtime1R realizeT realizeT_bind₂ revealThen progThen
  readLift readLiftQ readLift_bind₂ RevealVals DropRec ReadsRel readsRel_pure readsRel_readH_bind
  readsRel_act_bind liftReadC liftReadProg dropRec_realizeT_substitute dropRec_realizeT_act_bind
  dropRec_realizeT_bind dropRec_readLift_liftOrdinary evalDistMap_runtime1R_eq DropsTo ProgOf
  progCall dropsTo_liftReadProg dropsTo_substitute
  evalDistMap_runtime1_eq_spongeHardwiredReadRuntime)
open Quantum.Qrom.Xmss (romAnswers not_isHash_inl)

/-! ## Read programs with a pure step -/

section reads

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **A computation's read program, then a pure step**, over runtime 1's ports. Irreducible, as
`readsThenT`. -/
@[irreducible]
noncomputable def readsThenR {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) (QReg.of Unit) (QReg.of Unit) β :=
  ((readsProgram M _ oa).map Prod.fst).bind fun a ↦ QuantumComp₂.pure (f a)

omit [Fintype M] [DecidableEq M] in
theorem readsThenR_eq {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    readsThenR M oa f = ((readsProgram M _ oa).map Prod.fst).bind fun a ↦
      QuantumComp₂.pure (f a) := by
  unfold readsThenR
  rfl

omit [Fintype M] [DecidableEq M] in
/-- The template's read step is runtime 1's, lifted. -/
theorem readsThenT_eq_readLiftQ {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    readsThenT M oa f = readLiftQ goodQ (readsThenR M oa f) := by
  rw [readsThenT_eq, readsThenR_eq, readLift_bind₂]
  rfl

variable {M} (θ : TVals) {B : QReg}

omit [Fintype M] [DecidableEq M] in
theorem readsRel_romReadImpl (x : RomOracles.Domain) (log : List Qrom.HashDomain) :
    ReadsRel goodQ θ ((romReadImpl M B x).run log) ((romReadImpl Unit B x).run log) := by
  rcases x with n | y
  · change ReadsRel goodQ θ
      ((QComp.coinImpl (hwReadSpec PairOut Qrom.HashDomain M) B n).bind fun a ↦
        QuantumComp₂.pure (a, log))
      ((QComp.coinImpl (hwReadSpec PairOut Qrom.HashDomain Unit) B n).bind fun a ↦
        QuantumComp₂.pure (a, log))
    exact readsRel_act_bind θ _ fun a ↦ readsRel_pure θ (a, log)
  · change ReadsRel goodQ θ
      ((readCall (.readH (hmsgRoute (y, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (y, false)).2 (r.1.getD 0), log ++ [y]))
      ((readCall (.readH (hmsgRoute (y, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (y, false)).2 (r.1.getD 0), log ++ [y]))
    exact readsRel_readH_bind θ _ keepMem keepMem fun _ _ ↦ readsRel_pure θ _

omit [Fintype M] [DecidableEq M] in
theorem readsRel_simulateQ {α : Type} (x : OracleComp RomOracles α) (log : List Qrom.HashDomain) :
    ReadsRel goodQ θ ((simulateQ (romReadImpl M B) x).run log)
      ((simulateQ (romReadImpl Unit B) x).run log) := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a =>
    rw [simulateQ_pure, simulateQ_pure]
    exact readsRel_pure θ (a, log)
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    exact (readsRel_romReadImpl θ q log).bind fun p ↦ ih p.1 p.2

omit [Fintype M] [DecidableEq M] in
/-- **The read program of a computation at memories `M` and `Unit`.** -/
theorem readsRel_readsProgram {α : Type} (x : OracleComp RomOracles α) :
    ReadsRel goodQ θ (readsProgram M B x) (readsProgram Unit B x) :=
  readsRel_simulateQ θ x []

omit [Fintype M] [DecidableEq M] in
theorem readsRel_readsThenR {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    ReadsRel goodQ θ (readsThenR M oa f) (readsThenR Unit oa f) := by
  rw [readsThenR_eq, readsThenR_eq]
  exact ((readsRel_readsProgram θ oa).map Prod.fst).bind fun a ↦ readsRel_pure θ (f a)

omit [Fintype M] [DecidableEq M] in
/-- The realized read step drops to runtime 1's read step at memory `Unit`. -/
theorem dropRec_readsThenT {α β : Type} (oa : OracleComp RomOracles α) (f : α → β) :
    DropRec TPos (realizeT θ (readsThenT M oa f)) (liftReadC (readsThenR Unit oa f)) := by
  rw [readsThenT_eq_readLiftQ]
  exact readsRel_readsThenR θ oa f

end reads

/-! ## The realized game without reveals, and its read program -/

section programs

variable (θ : TVals)

/-- The program calls of the positions `ps` realized at `θ`. -/
noncomputable def progPosD (B : QReg) :
    List Pos → QComp (hwSpec PairOut Qrom.HashDomain Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall ((progT p).realize θ) B).bind fun _ ↦ progPosD B ps

/-- The value the key `K` signs, revealed at `msgPos K`. -/
noncomputable def keyMsgD (K : Key) : Digest :=
  (tabR (restrictTo {vcoord (msgPos K)} θ)).valuePos (msgPos K)

/-- The layer signature by `K` with counter `c` and codeword `x`, from the values revealed on
`layerReveal K x`. -/
noncomputable def layerSigD (K : Key) (c : EncodingCounter) (x : Encoding) : LayerSignature K.1 :=
  ⟨c, fun i ↦ (tabR (restrictTo (layerReveal K x) θ)).chainValue K.1 K.2.1 K.2.2 i (x i).val,
    (tabR (restrictTo (layerReveal K x) θ)).authPath K.1 K.2.1 K.2.2⟩

/-- The FORS opening of instance `idx` at the leaves `lv`, from the values revealed on
`forsReveal idx lv`. -/
noncomputable def forsD (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ForsTreeIndex → ForsTreeOpening :=
  (tabR (restrictTo (forsReveal idx lv) θ)).forsOpening idx lv

/-- The table revealed with `PK.seed`, `PK.root` and `R(M)`. -/
noncomputable def sigTabD (msg : Message) : QTable :=
  tabR (restrictTo {seedC, rootC, rndC msg} θ)

/-- The digest of `M` at `msgPol`, from its revealed digest cell. -/
noncomputable def dgD (msg : Message) : MessageDigest :=
  digestT msgPol ∅ msg (restrictTo (msgNeed msg) θ)

/-- The public key the game reveals. -/
noncomputable def pkD : PublicKey :=
  (tabR (restrictTo pkReveal θ)).publicKey

/-- **A counter search, realized with its reveal dropped**: the trials through read ports keeping
the memory. -/
noncomputable def selectD (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (Option (EncodingCounter × Encoding)) :=
  liftReadC (grindT Unit (keepUpd Unit) seed B K (keyMsgD θ K) encodingAttemptLimit 0)

/-- **A counter search as reads.** -/
noncomputable def selectR (seed : PublicParameter) (B : QReg) (K : Key) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B (Option (EncodingCounter × Encoding)) :=
  grindT Unit (keepUpd Unit) seed B K (keyMsgD θ K) encodingAttemptLimit 0

/-- **A layer publication, realized with its reveal dropped**: the program calls of the positions
it makes public, then the layer signature from the revealed values. -/
noncomputable def publishD (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (LayerSignature K.1) :=
  (progPosD θ B (layerPos K x)).bind fun _ ↦ QuantumComp₂.pure (layerSigD θ K c x)

/-- The FORS opening, realized with its reveal dropped. -/
noncomputable def forsOpenD (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (ForsTreeIndex → ForsTreeOpening) :=
  (progPosD θ B (forsPos idx lv)).bind fun _ ↦ QuantumComp₂.pure (forsD θ idx lv)

/-- The publication of a signature, realized with its reveals dropped. -/
noncomputable def publishAllD (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) :
    Option (EncodingCounter × Encoding) → Option (EncodingCounter × Encoding) →
      Option (EncodingCounter × Encoding) →
        QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (forsOpenD θ B idx lv).bind fun fo ↦
    (publishD θ B (keyOf 0 idx) c₀ x₀).bind fun bottom ↦
    (publishD θ B (keyOf 1 idx) c₁ x₁).bind fun middle ↦
    (publishD θ B (keyOf 2 idx) c₂ x₂).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

/-- The publication of a signature as reads: every value from the revealed values. -/
noncomputable def publishAllR (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) :
    Option (EncodingCounter × Encoding) → Option (EncodingCounter × Encoding) →
      Option (EncodingCounter × Encoding) →
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B (Option Signature)
  | some (c₀, x₀), some (c₁, x₁), some (c₂, x₂) =>
    (QuantumComp₂.pure (forsD θ idx lv) :
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B _).bind fun fo ↦
    (QuantumComp₂.pure (layerSigD θ (keyOf 0 idx) c₀ x₀) :
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B _).bind fun bottom ↦
    (QuantumComp₂.pure (layerSigD θ (keyOf 1 idx) c₁ x₁) :
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B _).bind fun middle ↦
    (QuantumComp₂.pure (layerSigD θ (keyOf 2 idx) c₂ x₂) :
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B _).bind fun top ↦
      QuantumComp₂.pure (some ⟨R, fo, KeyGenerationAndSigning.layerSignatures bottom middle top⟩)
  | _, _, _ => QuantumComp₂.pure none

/-- **A signature at `msgPol`, realized with its reveals dropped.** -/
noncomputable def signD (B : QReg) (msg : Message) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (Option Signature) :=
  (progCall ((digPort msgPol ∅ msg).realize θ) B).bind fun _ ↦
  (selectD θ (sigTabD θ msg).publicSeed B (keyOf 0 (digestIndex (dgD θ msg)))).bind fun g₀ ↦
  (selectD θ (sigTabD θ msg).publicSeed B (keyOf 1 (digestIndex (dgD θ msg)))).bind fun g₁ ↦
  (selectD θ (sigTabD θ msg).publicSeed B (keyOf 2 (digestIndex (dgD θ msg)))).bind fun g₂ ↦
  publishAllD θ B (digestIndex (dgD θ msg)) (digestForsLeaves (dgD θ msg))
    ((sigTabD θ msg).randomizer msg) g₀ g₁ g₂

/-- **The grind-only signer**: the counter searches through read ports, every other value of the
signature from the revealed values. -/
noncomputable def signR (B : QReg) (msg : Message) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B (Option Signature) :=
  (selectR θ (sigTabD θ msg).publicSeed B (keyOf 0 (digestIndex (dgD θ msg)))).bind fun g₀ ↦
  (selectR θ (sigTabD θ msg).publicSeed B (keyOf 1 (digestIndex (dgD θ msg)))).bind fun g₁ ↦
  (selectR θ (sigTabD θ msg).publicSeed B (keyOf 2 (digestIndex (dgD θ msg)))).bind fun g₂ ↦
  publishAllR θ B (digestIndex (dgD θ msg)) (digestForsLeaves (dgD θ msg))
    ((sigTabD θ msg).randomizer msg) g₀ g₁ g₂

/-- The signing answer of the realized game with its reveals dropped. -/
noncomputable def signAtD (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E))
      (Option Signature) :=
  (QComp.act (spec := hwSpec PairOut Qrom.HashDomain Unit)
    (B := QReg.of (sAdvSpec.Out (.sign msg) × E)) (SubInstrument.relabel ℓ)).bind fun _ ↦
      signD θ _ msg

/-- The signing answer as reads. -/
noncomputable def signAtR (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E))
      (Option Signature) :=
  (QComp.act (spec := hwReadSpec PairOut Qrom.HashDomain Unit)
    (B := QReg.of (sAdvSpec.Out (.sign msg) × E)) (SubInstrument.relabel ℓ)).bind fun _ ↦
      signR θ _ msg

/-- **The challenger of the realized game with its reveals dropped.** -/
noncomputable def challengeD :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec PairOut Qrom.HashDomain Unit))
  | A, .prim o => liftReadProg ((liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.prim o)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain Unit))
  | A, .query .hash E ℓ => liftReadProg ((liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.query .hash E ℓ)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain Unit))
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (signAtD θ msg E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The challenger with the grind-only signer.** -/
noncomputable def challengeR :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec PairOut Qrom.HashDomain Unit))
  | A, .prim o => (liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.prim o)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain Unit)
  | A, .query .hash E ℓ => (liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A (.query .hash E ℓ)))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain Unit)
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (signAtR θ msg E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The realized template game at `msgPol` with its reveals dropped** (over `hwSpec`). -/
noncomputable def gameD (A : SAdversary) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeD θ) (SufCma.withSignLog (A (pkD θ))))
    fun run ↦ liftReadC (readsThenR Unit (sphincsRom.verify (pkD θ) run.1) fun verified ↦
      sphincsRom.winningCondition run.2 run.1 && verified)

/-- **The grind-only read game** (over `hwReadSpec`): the adversary against `challengeR`, the
verification through read ports, the winning condition. -/
noncomputable def gameReadsT (A : SAdversary) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeR θ) (SufCma.withSignLog (A (pkD θ))))
    fun run ↦ readsThenR Unit (sphincsRom.verify (pkD θ) run.1) fun verified ↦
      sphincsRom.winningCondition run.2 run.1 && verified

end programs

/-! ## Dropping the reveals and the record calls -/

section records

variable {M : Type} (upd : TrialUpd M) (θ : TVals)

theorem dropRec_revealThen {B C : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × M) → QComp (SSpecQ M) B C α)
    {y : QComp (hwSpec PairOut Qrom.HashDomain Unit) B C α}
    (h : ∀ r, DropRec TPos (realizeT θ (k (restrictTo T θ, r))) y) :
    DropRec TPos (realizeT θ (revealThen goodQ T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThen {B C : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    {k : QComp (SSpecQ M) B C α} {y : QComp (hwSpec PairOut Qrom.HashDomain Unit) B C α}
    (h : DropRec TPos (realizeT θ k) y) :
    DropRec TPos (realizeT θ (progThen p trivial k))
      ((progCall (p.realize θ) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize θ) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT θ k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPos (B : QReg) :
    ∀ ps : List Pos, DropRec TPos (realizeT θ (progPos M B ps)) (progPosD θ B ps)
  | [] => .pure _
  | _ :: ps => dropRec_progThen θ _ (dropRec_progPos B ps)

/-- **The counter search at memories `M` and `Unit`.** -/
theorem readsRel_grindT (seed : PublicParameter) (B : QReg) (K : Key) (m : Digest) :
    ∀ n c, ReadsRel goodQ θ (grindT M upd seed B K m n c)
      (grindT Unit (keepUpd Unit) seed B K m n c)
  | 0, _ => readsRel_pure θ _
  | n + 1, c => by
    rw [grindT, grindT]
    refine readsRel_readH_bind θ _ _ _ fun o _ ↦ ?_
    dsimp only
    generalize TargetSum.decodeDigest (truncateHash (o.getD 0).1) = d
    cases d with
    | none => exact readsRel_grindT seed B K m n (c + 1)
    | some x => exact readsRel_pure θ _

theorem dropRec_selectT (seed : PublicParameter) (B : QReg) (K : Key) :
    DropRec TPos (realizeT θ (selectT M upd seed B K)) (selectD θ seed B K) := by
  unfold selectT
  exact dropRec_revealThen θ _ _ fun _ ↦ readsRel_grindT upd θ seed B K _ _ _

theorem dropRec_publishT (B : QReg) (K : Key) (c : EncodingCounter) (x : Encoding) :
    DropRec TPos (realizeT θ (publishT M B K c x)) (publishD θ B K c x) := by
  unfold publishT
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPos θ B _) fun _ ↦ .pure _

theorem dropRec_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    DropRec TPos (realizeT θ (forsOpenT M B idx lv)) (forsOpenD θ B idx lv) := by
  unfold forsOpenT
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPos θ B _) fun _ ↦ .pure _

theorem dropRec_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    DropRec TPos (realizeT θ (publishAllT M B idx lv R g₀ g₁ g₂))
      (publishAllD θ B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact .pure _
  simp only [publishAllT, publishAllD, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_forsOpenT θ B _ _) fun _ ↦
    DropRec.bind₂ (dropRec_publishT θ B _ _ _) fun _ ↦
      DropRec.bind₂ (dropRec_publishT θ B _ _ _) fun _ ↦
        DropRec.bind₂ (dropRec_publishT θ B _ _ _) fun _ ↦ .pure _

theorem dropRec_signT (B : QReg) (msg : Message) :
    DropRec TPos (realizeT θ (signT M upd msgPol B msg)) (signD θ B msg) := by
  unfold signT
  refine dropRec_revealThen θ _ _ fun _ ↦ dropRec_revealThen θ _ _ fun _ ↦ ?_
  refine dropRec_progThen θ _ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selectT upd θ _ B _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selectT upd θ _ B _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_selectT upd θ _ B _) fun _ ↦ dropRec_publishAllT θ B _ _ _ _ _ _

theorem dropRec_signAt (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    DropRec TPos (realizeT θ (signAt M upd msgPol msg E ℓ)) (signAtD θ msg E ℓ) :=
  dropRec_realizeT_act_bind θ _ fun _ ↦ dropRec_signT upd θ _ msg

theorem dropRec_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    DropRec TPos (realizeT θ (challengeT M upd msgPol A c)) (challengeD θ A c) := by
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_realizeT_bind θ (dropRec_signAt upd θ msg E ℓ) fun _ _ ↦ .pure _

/-- **The realized game drops to `gameD`**: with its record calls removed and its reads keeping
the memory `Unit`, the realized template game at `msgPol` is `gameD θ A`. -/
theorem dropRec_gameT (A : SAdversary) :
    DropRec TPos (realizeT θ (gameT M upd msgPol A)) (gameD θ A) := by
  unfold gameT
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_realizeT_substitute θ (dropRec_challengeT upd θ) _) fun _ ↦
    dropRec_readsThenT θ _ _

end records

/-! ## Dropping the program calls -/

section drops

variable (W : Hw PairOut Qrom.HashDomain) (θ : TVals)

/-- **Every program call of `gameD θ` hardwires a cell of `W` with its `W` value**: the realized
ports of the structural positions and of the digest cells. -/
def ProgsOfQ : Prop :=
  (∀ p : Pos, p.1.IsStruct → ProgOf W ((progT p).realize θ)) ∧
    ∀ msg, ProgOf W ((digPort msgPol ∅ msg).realize θ)

variable {W θ}

theorem dropsTo_progPosD (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec PairOut Qrom.HashDomain Unit) B C α}
    {y : QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B C α} (hx : DropsTo W x y) :
    ∀ ps : List Pos, (∀ p ∈ ps, ProgOf W ((progT p).realize θ)) →
      DropsTo W ((progPosD θ B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPosD, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPosD B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

theorem dropsTo_publishD (h : ProgsOfQ W θ) (B : QReg) (K : Key) (c : EncodingCounter)
    (x : Encoding) : DropsTo W (publishD θ B K c x) (QuantumComp₂.pure (layerSigD θ K c x)) :=
  dropsTo_progPosD B (DropsTo.pure _) _ fun p hp ↦ h.1 p (isStruct_of_mem_layerPos hp)

theorem dropsTo_forsOpenD (h : ProgsOfQ W θ) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    DropsTo W (forsOpenD θ B idx lv) (QuantumComp₂.pure (forsD θ idx lv)) :=
  dropsTo_progPosD B (DropsTo.pure _) _ fun p hp ↦ h.1 p (isStruct_of_mem_forsPos hp)

theorem dropsTo_publishAllD (h : ProgsOfQ W θ) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer)
    (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    DropsTo W (publishAllD θ B idx lv R g₀ g₁ g₂) (publishAllR θ B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact DropsTo.pure _
  exact DropsTo.bind₂ (dropsTo_forsOpenD h B _ _) fun _ ↦
    DropsTo.bind₂ (dropsTo_publishD h B _ _ _) fun _ ↦
      DropsTo.bind₂ (dropsTo_publishD h B _ _ _) fun _ ↦
        DropsTo.bind₂ (dropsTo_publishD h B _ _ _) fun _ ↦ DropsTo.pure _

theorem dropsTo_signD (h : ProgsOfQ W θ) (B : QReg) (msg : Message) :
    DropsTo W (signD θ B msg) (signR θ B msg) := by
  unfold signD signR
  refine DropsTo.progCall_bind _ (h.2 msg) ?_
  exact DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦
      DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ dropsTo_publishAllD h B _ _ _ _ _ _

theorem dropsTo_challengeD (h : ProgsOfQ W θ) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DropsTo W (challengeD θ A c) (challengeR θ A c) := by
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · refine DropsTo.bind ?_ fun _ _ ↦ DropsTo.pure _
    rw [signAtD, signAtR, QComp.act_bind, QComp.act_bind]
    exact DropsTo.prim _ fun _ ↦ dropsTo_signD h _ msg

/-- **The realized game with its reveals dropped is the grind-only read game with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_gameD (h : ProgsOfQ W θ) (A : SAdversary) :
    DropsTo W (gameD θ A) (gameReadsT θ A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeD h) _) fun _ ↦
    dropsTo_liftReadProg W _

end drops

/-! ## At a table, the game programs the table's cells -/

section table

/-- **The hardwired cells of runtime 1 at the hidden values `θ`**: the cells of the table
`tabOf θ` at the master seed `seedOf θ`, with their values. -/
noncomputable def hwT (θ : TVals) : Hw PairOut Qrom.HashDomain :=
  (table (seedOf θ)).hwOf (tabOf θ)

theorem hwT_thetaOf (S0 : MasterSeed) (v : QTable) : hwT (thetaOf S0 v) = (table S0).hwOf v := by
  unfold hwT
  rw [seedOf_thetaOf, tabOf_thetaOf]

theorem progOf_hwOf (S0 : MasterSeed) (v : QTable) (p : Pos) :
    ProgOf ((table S0).hwOf v) (.programH (cellOf S0 p v) (v p)) :=
  (table S0).tableDb_cell v v p

/-- **At the hidden values `θ`, the game programs cells of `hwT θ` with their values.** -/
theorem progsOf_hwT (θ : TVals) : ProgsOfQ (hwT θ) θ := by
  refine ⟨fun p hp ↦ ?_, fun msg ↦ ?_⟩
  · rw [realize_progT hp (seedOf θ) θ]
    exact progOf_hwOf _ _ p
  · rw [realize_digPort_msgPol ∅ msg (seedOf θ) θ]
    exact progOf_hwOf _ _ _

end table

/-! ## The grind-only signer against the functions consistent with the table -/

section honest

variable {θ : TVals} {t : (Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
  (PairOut → Qrom.HashDomain)} {W : Hw PairOut Qrom.HashDomain} {m : Unit} {B : QReg}

/-- An encoding cell is not a call 1 of `H_msg`. -/
theorem hmsgCall_encCell_ne (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (msg : Digest) (c : EncodingCounter) :
    hmsgCall (encCell seed l τ e msg c) ≠ some 1 := fun h ↦ by
  obtain ⟨R, M, c', hs⟩ := exists_hmsg_of_hmsgCall (s := .enc l τ e) trivial h
  cases hs

/-- **The regrouped function at an encoding cell** is the first component of its cell. -/
theorem regroup_encCell (F : Qrom.HashDomain → PairOut) (seed : PublicParameter) (l : Layer)
    (τ : TreeIndex) (e : TreeLeafIndex) (msg : Digest) (c : EncodingCounter) :
    regroup hmsgRoute F (encCell seed l τ e msg c) = (F (encCell seed l τ e msg c)).1 :=
  regroup_apply_of_fixed (hmsgRoute_of_ne (hmsgCall_encCell_ne seed l τ e msg c)) F

/-- **The counter search through read ports returns the table's selection.** -/
theorem readsTo_grindT (v : QTable) (K : Key) (msg : Digest) : ∀ n c,
    ReadsTo t W m (grindT Unit (keepUpd Unit) v.publicSeed B K msg n c)
      (v.selectFrom (regroup hmsgRoute (overwrite W t).1) K.1 K.2.1 K.2.2 msg n c)
  | 0, _ => readsTo_pure _
  | n + 1, c => by
    rw [grindT]
    refine (readsTo_readCall (.readH (trialCell v.publicSeed K msg c)
      (keepUpd Unit K (trialCell v.publicSeed K msg c))) rfl B).bind ?_
    rw [QTable.selectFrom, QTable.encDigest,
      show regroup hmsgRoute (overwrite W t).1
          (encCell v.publicSeed K.1 K.2.1 K.2.2 msg (BitVec.ofNat counterBits c)) =
        ((readAnswer t W m (.readH (trialCell v.publicSeed K msg c)
          (keepUpd Unit K (trialCell v.publicSeed K msg c)))).1.getD 0).1 from
        regroup_encCell _ _ _ _ _ _ _]
    generalize TargetSum.decodeDigest (truncateHash ((readAnswer t W m
      (.readH (trialCell v.publicSeed K msg c)
        (keepUpd Unit K (trialCell v.publicSeed K msg c)))).1.getD 0).1) = d
    cases d with
    | none => exact readsTo_grindT v K msg n (c + 1)
    | some x => exact readsTo_pure _

theorem tabR_restrictTo_congr {T : Finset TPos} {s : TPos} (h : s ∈ T) :
    pairAt (extW (restrictTo T θ)) s = pairAt θ s :=
  pairAt_extW_restrictTo h θ

theorem keyMsgD_keyOf (l : Layer) (idx : Index) :
    keyMsgD θ (keyOf l idx) = (tabOf θ).layerMessage idx l :=
  (valuePos_tabOf_congr _ (tabR_restrictTo_congr (Finset.mem_singleton_self _))).trans
    ((tabOf θ).msgPos_eq l idx)

theorem layerSigD_eq (K : Key) (c : EncodingCounter) (x : Encoding) :
    layerSigD θ K c x =
      ⟨c, fun i ↦ (tabOf θ).chainValue K.1 K.2.1 K.2.2 i (x i).val,
        (tabOf θ).authPath K.1 K.2.1 K.2.2⟩ := by
  have hc : ∀ i, (tabR (restrictTo (layerReveal K x) θ)).chainValue K.1 K.2.1 K.2.2 i (x i).val =
      (tabOf θ).chainValue K.1 K.2.1 K.2.2 i (x i).val := fun i ↦
    chainValue_tabOf_congr (tabR_restrictTo_congr (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))
  have hp : (tabR (restrictTo (layerReveal K x) θ)).authPath K.1 K.2.1 K.2.2 =
      (tabOf θ).authPath K.1 K.2.1 K.2.2 := funext fun z ↦
    treeValue_tabOf_congr (tabR_restrictTo_congr (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun z : Fin (layerHeight K.1) ↦
        treeC K.1 K.2.1 z.val ((K.2.2.val >>> z.val) ^^^ 1)) (Finset.mem_univ z))))
  unfold layerSigD
  simp only [hc, hp]

theorem forsD_eq (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsD θ idx lv = (tabOf θ).forsOpening idx lv := by
  funext κ
  have h1 : (tabR (restrictTo (forsReveal idx lv) θ)).forsSecret idx κ (lv κ) =
      (tabOf θ).forsSecret idx κ (lv κ) :=
    dig_tabOf_congr (tabR_restrictTo_congr (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ κ)))))
  have h2 : ∀ z : Fin forsTreeHeight,
      (tabR (restrictTo (forsReveal idx lv) θ)).forsValue idx κ z.val
        (((lv κ).val >>> z.val) ^^^ 1) =
      (tabOf θ).forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1) := fun z ↦
    forsValue_tabOf_congr (tabR_restrictTo_congr (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun q : ForsTreeIndex × Fin forsTreeHeight ↦
        forsC idx q.1 q.2.val (((lv q.1).val >>> q.2.val) ^^^ 1)) (Finset.mem_univ (κ, z)))))
  exact congrArg₂ ForsTreeOpening.mk h1 (funext h2)

theorem dgD_eq (msg : Message) : dgD θ msg = (tabOf θ).messageDigest msg := by
  unfold dgD digestT
  rw [messageDigest_eq_digestOfPair, tabOf_digPos]
  exact congrArg digestOfPair (pairR_restrictTo (Finset.mem_singleton_self _) θ)

theorem sigTabD_publicSeed (msg : Message) :
    (sigTabD θ msg).publicSeed = (tabOf θ).publicSeed :=
  publicSeed_tabOf_congr (tabR_restrictTo_congr (by simp))

theorem sigTabD_randomizer (msg : Message) :
    (sigTabD θ msg).randomizer msg = (tabOf θ).randomizer msg :=
  randomizer_tabOf_congr (tabR_restrictTo_congr (by simp))

theorem pkD_eq : pkD θ = (tabOf θ).publicKey :=
  congrArg₂ Sphincs.PublicKey.mk
    (publicSeed_tabOf_congr (tabR_restrictTo_congr (Finset.mem_insert_self _ _)))
    (root_tabOf_congr (tabR_restrictTo_congr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))

/-- **The counter search of `K_l(idx)` returns the table's selection.** -/
theorem readsTo_selectR (l : Layer) (idx : Index) :
    ReadsTo t W m (selectR θ (tabOf θ).publicSeed B (keyOf l idx))
      ((tabOf θ).select (regroup hmsgRoute (overwrite W t).1) l (treeOfIndex l idx)
        (leafOfIndex l idx) ((tabOf θ).layerMessage idx l)) := by
  rw [selectR, keyMsgD_keyOf]
  exact readsTo_grindT (tabOf θ) _ _ _ _

/-- **The grind-only signer returns the table's signature** against the functions consistent
with the table. -/
theorem readsTo_signR (msg : Message) :
    ReadsTo t W m (signR θ B msg)
      ((tabOf θ).signature (regroup hmsgRoute (overwrite W t).1) msg) := by
  have hi : (tabOf θ).index msg = digestIndex (dgD θ msg) := by
    rw [dgD_eq]
    rfl
  have hv : (tabOf θ).leaves msg = digestForsLeaves (dgD θ msg) := by
    rw [dgD_eq]
    rfl
  unfold signR
  rw [sigTabD_publicSeed, sigTabD_randomizer, ← hi, ← hv]
  unfold QTable.signature QTable.layerSig QTable.layerSignature
  refine (readsTo_selectR 0 _).bind ?_
  refine (readsTo_selectR 1 _).bind ?_
  refine (readsTo_selectR 2 _).bind ?_
  rcases (tabOf θ).select (regroup hmsgRoute (overwrite W t).1) 0
      (treeOfIndex 0 ((tabOf θ).index msg)) (leafOfIndex 0 ((tabOf θ).index msg))
      ((tabOf θ).layerMessage ((tabOf θ).index msg) 0) with _ | ⟨c₀, x₀⟩ <;>
    rcases (tabOf θ).select (regroup hmsgRoute (overwrite W t).1) 1
      (treeOfIndex 1 ((tabOf θ).index msg)) (leafOfIndex 1 ((tabOf θ).index msg))
      ((tabOf θ).layerMessage ((tabOf θ).index msg) 1) with _ | ⟨c₁, x₁⟩ <;>
    rcases (tabOf θ).select (regroup hmsgRoute (overwrite W t).1) 2
      (treeOfIndex 2 ((tabOf θ).index msg)) (leafOfIndex 2 ((tabOf θ).index msg))
      ((tabOf θ).layerMessage ((tabOf θ).index msg) 2) with _ | ⟨c₂, x₂⟩ <;>
    try exact readsTo_pure (none : Option Signature)
  rw [publishAllR, forsD_eq, layerSigD_eq, layerSigD_eq, layerSigD_eq]
  exact (readsTo_pure _).bind ((readsTo_pure _).bind ((readsTo_pure _).bind
    ((readsTo_pure _).bind (readsTo_pure _))))

variable (t W m)

/-- **The challenger with the grind-only signer intertwines with the challenger** against the
regrouped function consistent with the table. -/
theorem intertwines_challengeR (hv : Consistent (seedOf θ) (tabOf θ) (overwrite W t).1)
    (A : QReg) (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).src A c b = u} ↦
          (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (SufCma.challenge sphincsRom (seedOf θ) A c))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
        (challengeR θ A c)) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact intertwines_liftH t W m _
  · exact intertwines_liftH t W m _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (QuantumComp.bind (SufCma.signTree sphincsRom (seedOf θ) r E ℓ) _))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run .instruments
        (QuantumComp.bind (signAtR θ r E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) ?_) fun p ↦ ?_
    · rw [SufCma.signTree, signAtR]
      refine intertwines_run₂_act_bind
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) (A := A)
        (B := QReg.of (sAdvSpec.Out (.sign r) × E)) _ fun _ ↦ ?_
      exact intertwines_of_classicalOn_readsTo t W m
        ((Quantum.Qrom.Xmss.classicalOn_toQuantumAt_romImpl_pure (not_romRead_inl _) _
          (signReads_sign (agrees_regroup hv) r)).congr
          (congrArg pure (eval_sign (agrees_regroup hv) r)) rfl) (readsTo_signR r)
    · exact intertwines_run_pure
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m) _

/-- **The game and its grind-only reads intertwine** on the block `(W, m)`, against the regrouped
function consistent with the table `tabOf θ` at `seedOf θ`. -/
theorem intertwines_game_gameReadsT (hv : Consistent (seedOf θ) (tabOf θ) (overwrite W t).1)
    (A : SAdversary) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (SufCma.game sphincsRom (seedOf θ) A))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W m).run₂ .instruments
        (gameReadsT θ A)) := by
  rw [SufCma.game, run₂_bind_of_classicalOn_pure
    ((Quantum.Qrom.Xmss.classicalOn_toQuantumAt_romImpl_pure (not_romRead_inl _) _
      (cellReads_generateKeys (agrees_regroup hv))).congr
      (congrArg pure (eval_generateKeys (agrees_regroup hv))) rfl)]
  dsimp only
  rw [gameReadsT, pkD_eq]
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
    (intertwines_run₂_of_run (intertwines_substitute (spec₀ := sAdvSpec)
      (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_challengeR t W m hv A c) _))
    fun run ↦ ?_
  rw [readsThenR_eq]
  exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (V := hwAt W m)
    (intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _))
    fun _ ↦ intertwines_run₂_pure _

/-- **The game is its grind-only reads at a fixed function**, consistent with the table. -/
theorem evalDistMap_game_eq_gameReadsT (hv : Consistent (seedOf θ) (tabOf θ) (overwrite W t).1)
    (A : SAdversary) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).evalDistMap .instruments
        (SufCma.game sphincsRom (seedOf θ) A) ρ f =
      (spongeFnReadRuntime PairOut Qrom.HashDomain t W m).evalDistMap .instruments
        (gameReadsT θ A) ρ f :=
  evalDistMap_eq_of_intertwines
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_game_gameReadsT t W m hv A)) ρ f

end honest

/-! ## Runtime 1 runs the realized template game -/

/-- **The two read programs have the same law in runtime 1**: `gameReads` after the honest key
generation and the grind-only `gameReadsT θ`, with the cells of `tabOf θ` at `seedOf θ`
hardwired. -/
theorem evalDistMap_gameReads_eq_gameReadsT (θ : TVals) (A : SAdversary)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime PairOut Qrom.HashDomain (hwT θ) ()).evalDistMap .instruments
        (gameReads Unit A ((tabOf θ).publicKey, seedOf θ)) ρ f =
      (spongeHardwiredReadRuntime PairOut Qrom.HashDomain (hwT θ) ()).evalDistMap .instruments
        (gameReadsT θ A) ρ f := by
  refine (read_port_eq_classical_read _ _ _ _ _ _).trans ((Finset.sum_congr rfl fun t _ ↦
    congrArg _ ?_).trans (read_port_eq_classical_read _ _ _ _ _ _).symm)
  exact (evalDistMap_game_eq_reads (consistent_fill (seedOf θ) (tabOf θ) t.1) A ρ f).symm.trans
    (evalDistMap_game_eq_gameReadsT t (hwT θ) () (consistent_fill (seedOf θ) (tabOf θ) t.1) A ρ f)

/-- **Runtime 1 with record ports runs the realized template game as the game's reads** (the
hybrid side, `msgPol`): with the cells of `tabOf θ` at `seedOf θ` hardwired, from any memory and
for any trial update, the realized template game has the law of `gameReads` in runtime 1. -/
theorem evalDistMap_runtime1R_gameT {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)
    (θ : TVals) (m₀ : Finset TPos × M) (A : SAdversary) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (runtime1R PairOut Qrom.HashDomain (hwT θ) m₀).evalDistMap .instruments
        (realizeT θ (gameT M upd msgPol A)) ρ f =
      (spongeHardwiredReadRuntime PairOut Qrom.HashDomain (hwT θ) ()).evalDistMap .instruments
        (gameReads Unit A ((tabOf θ).publicKey, seedOf θ)) ρ f :=
  (evalDistMap_runtime1R_eq (hwT θ) m₀ (dropRec_gameT upd θ A) ρ f).trans
    ((evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (hwT θ) ()
      (dropsTo_gameD (progsOf_hwT θ) A) ρ f).trans
      (evalDistMap_gameReads_eq_gameReadsT θ A ρ f).symm)

/-- **The game in the QROM is runtime 1 with record ports on the realized template game**: at the
seed `S_0`, its law is the uniform average over the table values `v` of the law of the template
game at `msgPol` realized at `thetaOf S0 v`, in runtime 1 with record ports started with the cells
of `v` hardwired, from any memory and for any trial update. -/
theorem qrom_game_eq_runtime1R {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)
    (S0 : MasterSeed) (m₀ : Finset TPos × M) (A : SAdversary) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qromEvalDistMap .instruments (SufCma.game sphincsRom S0 A) ρ (fun _ ↦ f) =
      ∑ v : QTable, (Fintype.card QTable : ℝ≥0∞)⁻¹ •
        (runtime1R PairOut Qrom.HashDomain (hwT (thetaOf S0 v)) m₀).evalDistMap .instruments
          (realizeT (thetaOf S0 v) (gameT M upd msgPol A)) ρ f := by
  rw [qrom_game_eq_runtime1 S0 () A ρ f]
  refine Finset.sum_congr rfl fun v _ ↦ congrArg _ ?_
  have h := evalDistMap_runtime1R_gameT upd (thetaOf S0 v) m₀ A ρ f
  rw [hwT_thetaOf, tabOf_thetaOf, seedOf_thetaOf] at h
  rw [hwT_thetaOf]
  exact h.symm

/-! ## The hidden values as the master seed, the table and pads -/

/-- **The pads**: the coordinates the table does not read (the second component of the seed's,
the digest cells' position coordinates, the stream, the marks). -/
abbrev TPads : Type :=
  HashOutput × (Message → PairOut) × (Fin signatureLimit → PairOut) ×
    (Message × Fin signatureLimit → Unit)

/-- The hidden values of a master seed, a table and pads. -/
def thetaOfPads (S0 : MasterSeed) (v : QTable) (r : TPads) : TVals
  | .val none => ((S0, r.1) : PairOut)
  | .val (some ⟨.hmsg m, _⟩) => r.2.1 m
  | .val (some p) => v p
  | .dig m => v (digPos m)
  | .str j => r.2.2.1 j
  | .asg _ _ => ()

/-- **The hidden values are the master seed, the table and the pads.** -/
def tvalsEquiv : TVals ≃ (MasterSeed × QTable) × TPads where
  toFun θ := ((seedOf θ, tabOf θ), ((θ (.val none) : PairOut).2,
    fun m ↦ (θ (.val (some (digPos m))) : PairOut), fun j ↦ (θ (.str j) : PairOut), fun _ ↦ ()))
  invFun x := thetaOfPads x.1.1 x.1.2 x.2
  left_inv θ := by
    funext s
    cases s with
    | val o =>
      rcases o with _ | ⟨q, hq⟩
      · rfl
      · cases q <;> rfl
    | dig m => rfl
    | str j => rfl
    | asg m j => rfl
  right_inv x := by
    obtain ⟨⟨S0, v⟩, h, d, s, a⟩ := x
    refine Prod.ext (Prod.ext rfl (funext fun p ↦ ?_)) rfl
    obtain ⟨q, hq⟩ := p
    cases q <;> rfl

/-- **Averaging over the hidden values a function of the seed and the table** averages over the
seed and the table. -/
theorem uavg_seedOf_tabOf (F : MasterSeed → QTable → ℝ≥0∞) :
    uavg (fun θ : TVals ↦ F (seedOf θ) (tabOf θ)) =
      uavg (fun x : MasterSeed × QTable ↦ F x.1 x.2) :=
  (uavg_comp_equiv tvalsEquiv fun y : (MasterSeed × QTable) × TPads ↦ F y.1.1 y.1.2).trans
    (uavg_comp_fst fun x : MasterSeed × QTable ↦ F x.1 x.2)

theorem uavg_prod_eq {K V : Type*} [Fintype K] [Fintype V] (g : K × V → ℝ≥0∞) :
    uavg g = (Fintype.card K : ℝ≥0∞)⁻¹ * ∑ k, (Fintype.card V : ℝ≥0∞)⁻¹ * ∑ v, g (k, v) := by
  unfold uavg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_assoc, Finset.mul_sum]

/-- The seed is uniform over the `2^256` master seeds. -/
theorem prEvent_sampleSeed_rom (S0 : MasterSeed) :
    Pr{let s ← sphincsRom.sampleSeed}[s = S0] = (2 ^ 256)⁻¹ :=
  Quantum.Sphincs.Assembly.prEvent_sampleSeed S0

/-- **The win probability is runtime 1 with record ports on the realized template game,
averaged over uniform hidden values** (the hybrid side, `msgPol`), from any memory and for any
trial update. -/
theorem winProb_eq_uavg_runtime1R {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)
    (m₀ : Finset TPos × M) (A : SAdversary) :
    SufCma.winProb sphincsRom A =
      uavg (fun θ : TVals ↦ (runtime1R PairOut Qrom.HashDomain (hwT θ) m₀).evalDistMap
        .instruments (realizeT θ (gameT M upd msgPol A)) (SubState.basis ())
          (fun p ↦ p.2.2) {true}) := by
  have h : ∀ θ : TVals, (runtime1R PairOut Qrom.HashDomain (hwT θ) m₀).evalDistMap
      .instruments (realizeT θ (gameT M upd msgPol A)) (SubState.basis ()) (fun p ↦ p.2.2)
        {true} =
      (spongeHardwiredReadRuntime PairOut Qrom.HashDomain ((table (seedOf θ)).hwOf (tabOf θ))
        ()).evalDistMap .instruments (gameReads Unit A ((tabOf θ).publicKey, seedOf θ))
          (SubState.basis ()) (fun p ↦ p.2.2) {true} := fun θ ↦
    congrArg (· {true}) (evalDistMap_runtime1R_gameT upd θ m₀ A _ _)
  rw [show (fun θ : TVals ↦ (runtime1R PairOut Qrom.HashDomain (hwT θ) m₀).evalDistMap
      .instruments (realizeT θ (gameT M upd msgPol A)) (SubState.basis ()) (fun p ↦ p.2.2)
        {true}) = _ from funext h,
    uavg_seedOf_tabOf (fun S0 v ↦ (spongeHardwiredReadRuntime PairOut Qrom.HashDomain
      ((table S0).hwOf v) ()).evalDistMap .instruments (gameReads Unit A (v.publicKey, S0))
        (SubState.basis ()) (fun p ↦ p.2.2) {true}), uavg_prod_eq,
    SufCma.winProb_eq_uniform sphincsRom prEvent_sampleSeed_rom A,
    show (Fintype.card MasterSeed : ℝ≥0∞) = 2 ^ 256 by
      rw [Fintype.card_congr (Quantum.Xmss.bitsEquiv 256)]
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num]
  refine congrArg _ (Finset.sum_congr rfl fun S0 _ ↦ ?_)
  rw [qrom_game_eq_runtime1 S0 () A (SubState.basis ()) (fun p ↦ p.2.2),
    MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ ↦ by
    rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]

/-! ## The canonical game -/

/-- **The canonical runtime-2 game** at the digest policy `pol` and the hidden values `θ`: the
counter searches' reads record codeword selections in `SelMem` (`cwUpd`). -/
noncomputable def gameQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT θ (gameT SelMem cwUpd pol A)

/-- The canonical challenge prefix at `pol` and `θ`. -/
noncomputable def prefixQ (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :=
  realizeT θ (prefixT SelMem cwUpd pol A)

end Quantum.Qrom.Sphincs

end
