module

public import Quantum.Qrom.Xmss.Multi.Template

@[expose] public section

/-!
# Runtime 1 runs the multi-user runtime-2 template realized at the table

The `n`-user analog of `Quantum.Qrom.Xmss.GameT`. For the master seeds `S0` and a good table `w`
of `n` users, runtime 1 with record ports (`runtime1R`, every cell of `(tableN S0).hwOf w`
hardwired from the start, any initial memory) runs the template game realized at the hidden values
`thetaOfN S0 w` with the law of the lifted multi-user game (`runtime1R_muGameT_eq`). With the
table law on the good set, the QROM game is the average over good tables of runtime 1 on the
realized template plus the bad fraction (`qromEvalDistMap_muGame_le_runtime1R`).

* **Records** (`dropRec_muGameT`): the realized template drops to `muGameD θ valid A` over
  `hwSpec` with memory `Unit`.
* **Programs** (`dropsTo_muGameD`): every program call of `muGameD (thetaOfN S0 w)` hardwires a
  cell of the good table with its value, so it is the read program `muGameReadsT` with program
  calls inserted.
* **Signer** (`signsN_signRN`): the grind-only signer `signRN` reads only the randomizer trials and
  takes the bases, chain values, paths and bottom roots from `θ`; from a memoized selection that
  agrees with the function it returns the user's signature and top selection, so
  `runtime1_muGame_eq_readsN` applies.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen progThen readLift readLiftQ RevealVals
  DropRec DropRec.bind₂ realizeT_bind₂ dropRec_realizeT_substitute dropRec_realizeT_act_bind
  dropRec_realizeT_bind dropRec_readLift_liftOrdinary ReadsRel readsRel_pure ReadsRel.bind
  ReadsRel.map liftReadC liftReadProg DropsTo DropsTo.bind₂ DropsTo.bind DropsTo.progCall_bind
  dropsTo_liftReadProg dropsTo_substitute progCall ProgOf runtime1R evalDistMap_runtime1R_eq
  evalDistMap_runtime1_eq_spongeHardwiredReadRuntime)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge muGame withMuSignLog)

attribute [local irreducible] xmssRom

variable {n : ℕ}

-- The adversary's commands with the memo, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MemoP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpec n)

/-! ## The realized game without reveals, and its read program -/

section programs

/-- User `i`'s layer signature with randomizer `ρ` and codeword `x`, read from `θ` on the
coordinates the signature reveals. -/
def layerOutN (θ : HPosN n → Digest) (i : Fin n) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : LayerSignature :=
  layerSigOf (tabRN (restrictTo (atU i (layerReveal l e x)) θ) i) l e ρ x

/-- User `i`'s randomizer base read from `θ` at the base's coordinate. -/
def baseOfN (θ : HPosN n → Digest) (i : Fin n) (rnd : Pos) : Randomizer :=
  truncateHash (tabRN (restrictTo (atU i {loC rnd}) θ) i rnd)

/-- User `i`'s bottom root under a request's top key, read from `θ` at its coordinate. -/
def rootOfN (θ : HPosN n → Digest) (i : Fin n) (r : SigningRequest) : Digest :=
  (tabRN (restrictTo (atU i (rootReveal r)) θ) i).bottomRoot r.leafIndex

/-- User `i`'s program calls of the positions `ps`, realized at `θ`. -/
noncomputable def progPosDN (θ : HPosN n → Digest) (i : Fin n) (B : QReg) :
    List Pos → QComp (hwSpec HashOutput HashDomain Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall ((progTN i p).realize θ) B).bind fun _ ↦ progPosDN θ i B ps

/-- **User `i`'s search, realized with its reveal dropped**: read ports keeping the memory. -/
noncomputable def selectDN (θ : HPosN n → Digest) (i : Fin n) (P : PublicParameter) (B : QReg)
    (l : Layer) (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    QComp (hwSpec HashOutput HashDomain Unit) B B TopSel :=
  liftReadC (grindT Unit (keepUpd Unit) P B l e message (baseOfN θ i rnd) randomizerAttemptLimit 0)

/-- **Publishing user `i`'s layer signature, realized with its reveal dropped.** -/
noncomputable def publishDN (θ : HPosN n → Digest) (i : Fin n) (B : QReg) (l : Layer)
    (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    QComp (hwSpec HashOutput HashDomain Unit) B B LayerSignature :=
  (progPosDN θ i B (layerPos l e x)).bind fun _ ↦ QuantumComp₂.pure (layerOutN θ i l e ρ x)

/-- User `i`'s signature of the realized game with its reveals dropped. -/
noncomputable def signDN (θ : HPosN n → Digest) (i : Fin n) (P : PublicParameter) (B : QReg)
    (r : SigningRequest) (h : Option TopSel) :
    QComp (hwSpec HashOutput HashDomain Unit) B B (Option Signature × TopSel) :=
  signWithN B (selectDN θ i P B) (publishDN θ i B)
    (topWithN (selectDN θ i P B) (rootOfN θ i r) r h) r

/-- **The challenger of the realized game with its reveals dropped.** -/
noncomputable def challengeDN (θ : HPosN n → Digest) (P : Fin n → PublicParameter) :
    IPFunctor.CommandSubstitution (MemoP n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit))
  | A, .prim o => liftReadProg ((liftH (muChallenge xmssRom (noKeys (n := n)) A
      (.prim o))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain Unit))
  | A, .query .hash E ℓ => liftReadProg ((liftH (muChallenge xmssRom (noKeys (n := n)) A
      (.query .hash E ℓ))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain Unit))
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtN i q E ℓ fun B ↦ signDN θ i (P i) B q.1 q.2) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The users' public keys revealed at `θ`. -/
def pkDN (θ : HPosN n → Digest) : Fin n → PublicKey :=
  pksT (restrictTo pkRevealN θ)

/-- **The realized template game with its reveals dropped** (over `hwSpec`, memory `Unit`). -/
noncomputable def muGameD (θ : HPosN n → Digest) (valid : SignLog → Bool) (A : MuAdversary n) :
    QComp (hwSpec HashOutput HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute
    (challengeDN θ fun i ↦ (pkDN θ i).parameter)
    (memoFrom (fun _ _ ↦ none) (withMuSignLog (A (pkDN θ))))) fun run ↦
    (liftReadC ((readsProgram Unit _ (xmssRom.verify (pkDN θ run.1.1) run.1.2)).map
      Prod.fst)).bind fun verified ↦
      QuantumComp₂.pure (xmssRom.winningCondition (run.2.user run.1.1) run.1.2 &&
        run.2.allValid valid && verified)

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **User `i`'s search as reads**, from the base of `θ`. -/
noncomputable def selectRN (θ : HPosN n → Digest) (i : Fin n) (P : PublicParameter) (B : QReg)
    (l : Layer) (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    QComp (hwReadSpec HashOutput HashDomain M) B B TopSel :=
  grindT M (keepUpd M) P B l e message (baseOfN θ i rnd) randomizerAttemptLimit 0

/-- **The grind-only signer**: the searches through read ports, the layer signatures, bottom
roots and bases from `θ`. -/
noncomputable def signRN (θ : HPosN n → Digest) (P : Fin n → PublicParameter) : SignerN M n :=
  fun i r h B ↦ signWithN B (selectRN M θ i (P i) B)
    (fun l e ρ x ↦ QuantumComp₂.pure (layerOutN θ i l e ρ x))
    (topWithN (selectRN M θ i (P i) B) (rootOfN θ i r) r h) r

/-- **The game's reads with the grind-only signer.** -/
noncomputable def muGameReadsT (θ : HPosN n → Digest) (valid : SignLog → Bool)
    (A : MuAdversary n) :
    QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsWithN M (signRN M θ fun i ↦ (pkDN θ i).parameter) (pkDN θ) valid A

end programs

/-! ## Dropping the reveals and records -/

section records

variable {M : Type} (θ : HPosN n → Digest)

theorem dropRec_revealThenN {B C : QReg} {α : Type} (T : Finset (HPosN n))
    (k : RevealVals (HDN n) T × (Finset (HPosN n) × M) → QComp (XSpecN M n) B C α)
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    (h : ∀ r, DropRec (HPosN n) (realizeT θ (k (restrictTo T θ, r))) y) :
    DropRec (HPosN n) (realizeT θ (revealThen goodQN T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThenN {B C : QReg} {α : Type}
    (p : LazyProg HashOutput HashDomain (HPosN n) (HDN n)) {k : QComp (XSpecN M n) B C α}
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α} (h : DropRec (HPosN n) (realizeT θ k) y) :
    DropRec (HPosN n) (realizeT θ (progThen p trivial k))
      ((progCall (p.realize θ) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize θ) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT θ k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPosN (i : Fin n) (B : QReg) :
    ∀ ps : List Pos, DropRec (HPosN n) (realizeT θ (progPosN M i B ps)) (progPosDN θ i B ps)
  | [] => DropRec.pure _
  | _ :: ps => dropRec_progThenN θ _ (dropRec_progPosN i B ps)

/-- The randomizer search at memories `M` and `Unit`. -/
theorem readsRel_grindTN (upd : TrialUpd M) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ∀ k trial, ReadsRel (goodQN (n := n)) θ (grindT M upd P B l e message base k trial)
      (grindT Unit (keepUpd Unit) P B l e message base k trial)
  | 0, _ => readsRel_pure θ _
  | k + 1, trial => by
    rw [grindT, grindT]
    refine Quantum.Xmss.Assembly.readsRel_readH_bind θ _ _ _ fun o _ ↦ ?_
    dsimp only
    generalize Codeword.decode (truncateHash (o.getD 0)) = d
    cases d with
    | none => exact readsRel_grindTN upd P B l e message base k (trial + 1)
    | some x => exact readsRel_pure θ _

/-- Stateful read programs at memories `M` and `Unit` that read alike from every log. -/
def ReadsRelLN {B : QReg} {α : Type}
    (x : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain M) B B) α)
    (y : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain Unit) B B) α) :
    Prop :=
  ∀ s, ReadsRel (goodQN (n := n)) θ (x.run s) (y.run s)

theorem readsRelLN_romReadImpl [Fintype M] [DecidableEq M] (B : QReg) (q : RomOracles.Domain) :
    ReadsRelLN θ (romReadImpl M B q) (romReadImpl Unit B q) := fun s ↦ by
  rcases q with k | x
  · exact Quantum.Xmss.Assembly.readsRel_act_bind (good := goodQN) θ
      (SubInstrument.uniform (Fin (k + 1)) B) fun a ↦ readsRel_pure θ (a, s)
  · exact Quantum.Xmss.Assembly.readsRel_readH_bind θ x keepMem keepMem
      (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [x]))
      (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [x])) fun _ _ ↦ readsRel_pure θ _

theorem readsRelLN_simulateQ [Fintype M] [DecidableEq M] (B : QReg) {α : Type}
    (x : OracleComp RomOracles α) :
    ReadsRelLN θ (simulateQ (romReadImpl M B) x) (simulateQ (romReadImpl Unit B) x) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro s
    rw [simulateQ_pure, simulateQ_pure]
    exact readsRel_pure θ (a, s)
  | query_bind q k ih =>
    intro s
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    exact (readsRelLN_romReadImpl θ B q s).bind fun p ↦ ih p.1 p.2

/-- The read program of a computation at memories `M` and `Unit`. -/
theorem readsRel_readsProgramN [Fintype M] [DecidableEq M] (B : QReg) {α : Type}
    (x : OracleComp RomOracles α) :
    ReadsRel (goodQN (n := n)) θ (readsProgram M B x) (readsProgram Unit B x) :=
  readsRelLN_simulateQ θ B x []

variable (upd : Fin n → TrialUpd M)

theorem dropRec_selectTN (i : Fin n) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    DropRec (HPosN n) (realizeT θ (selectTN M upd i P B l e message rnd))
      (selectDN θ i P B l e message rnd) := by
  rw [selectTN]
  exact dropRec_revealThenN θ _ _ fun _ ↦ readsRel_grindTN θ (upd i) P B l e message _ _ _

theorem dropRec_publishTN (i : Fin n) (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) :
    DropRec (HPosN n) (realizeT θ (publishTN M i B l e ρ x)) (publishDN θ i B l e ρ x) := by
  rw [publishTN]
  refine dropRec_revealThenN θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPosN θ i B _) fun _ ↦ DropRec.pure _

theorem dropRec_topTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) :
    DropRec (HPosN n) (realizeT θ (topTN M upd i P B r h))
      (topWithN (selectDN θ i P B) (rootOfN θ i r) r h) := by
  rcases h with _ | o
  · exact dropRec_revealThenN θ _ _ fun _ ↦ dropRec_selectTN θ upd i P B _ _ _ _
  · exact DropRec.pure _

theorem dropRec_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    DropRec (HPosN n) (realizeT θ (pubBothN (publishTN M i B) r gb gt))
      (pubBothN (publishDN θ i B) r gb gt) := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact DropRec.pure _
  · exact DropRec.pure _
  · exact DropRec.pure _
  · rw [pubBothN, pubBothN, realizeT_bind₂]
    refine DropRec.bind₂ (dropRec_publishTN θ i B _ _ _ _) fun _ ↦ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_publishTN θ i B _ _ _ _) fun _ ↦ DropRec.pure _

theorem dropRec_signTN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (h : Option TopSel) :
    DropRec (HPosN n) (realizeT θ (signTN M upd i P B r h)) (signDN θ i P B r h) := by
  rw [signTN, signDN, signWithN, signWithN, realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selectTN θ upd i P B _ _ _ _) fun gb ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_topTN θ upd i P B r h) fun gt ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_pubBothN θ i B r gb gt) fun _ ↦ DropRec.pure _

theorem dropRec_challengeTN (P : Fin n → PublicParameter) (A : QReg) (c : (MemoP n).A A) :
    DropRec (HPosN n) (realizeT θ (challengeTN M upd P A c)) (challengeDN θ P A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_readLift_liftOrdinary θ _
  · refine dropRec_realizeT_bind θ ?_ fun _ _ ↦ DropRec.pure _
    exact dropRec_realizeT_act_bind θ _ fun _ ↦ dropRec_signTN θ upd i (P i) _ q.1 q.2

/-- **The realized game drops to `muGameD`**: with its record calls removed and its reads keeping
the memory `Unit`, the realized template game is `muGameD θ valid A`. -/
theorem dropRec_muGameT [Fintype M] [DecidableEq M] (valid : SignLog → Bool)
    (A : MuAdversary n) :
    DropRec (HPosN n) (realizeT θ (muGameT M upd valid A)) (muGameD θ valid A) := by
  refine dropRec_revealThenN θ _ _ fun _ ↦ ?_
  dsimp only
  rw [realizeT_bind₂, muGameD]
  refine DropRec.bind₂ (dropRec_realizeT_substitute θ (dropRec_challengeTN θ upd _) _)
    fun run ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ ((readsRel_readsProgramN θ _ _).map Prod.fst) fun _ ↦ DropRec.pure _

end records

/-! ## Dropping the program calls -/

section drops

variable {W : Hw HashOutput HashDomain}

/-- Every program port of a position the game may program hardwires a cell of `W` with its `W`
value. -/
def ProgsOfN (W : Hw HashOutput HashDomain) (θ : HPosN n → Digest) : Prop :=
  ∀ (i : Fin n) (l : Layer) (e : KeyIndex) (x : Encoding), ∀ p ∈ layerPos l e x,
    ProgOf W ((progTN i p).realize θ)

theorem dropsTo_progPosDN (θ : HPosN n → Digest) (i : Fin n) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    {y : QComp (hwReadSpec HashOutput HashDomain Unit) B C α} (hx : DropsTo W x y) :
    ∀ ps : List Pos, (∀ p ∈ ps, ProgOf W ((progTN i p).realize θ)) →
      DropsTo W ((progPosDN θ i B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPosDN, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPosDN θ i B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

variable {θ : HPosN n → Digest} (h : ProgsOfN W θ)
include h

theorem dropsTo_pubBothN (i : Fin n) (B : QReg) (r : SigningRequest) (gb gt : TopSel) :
    DropsTo W (pubBothN (publishDN θ i B) r gb gt)
      (pubBothN (fun l e ρ x ↦ QuantumComp₂.pure (layerOutN θ i l e ρ x)) r gb gt) := by
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact DropsTo.pure _
  · exact DropsTo.pure _
  · exact DropsTo.pure _
  · simp only [pubBothN, publishDN, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
    exact dropsTo_progPosDN θ i _ (dropsTo_progPosDN θ i _ (DropsTo.pure _) _ (h i _ _ _)) _
      (h i _ _ _)

omit h in
theorem dropsTo_topWithN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (o : Option TopSel) :
    DropsTo W (topWithN (selectDN θ i P B) (rootOfN θ i r) r o)
      (topWithN (selectRN Unit θ i P B) (rootOfN θ i r) r o) := by
  rcases o with _ | o
  · exact dropsTo_liftReadProg W _
  · exact DropsTo.pure _

theorem dropsTo_signDN (i : Fin n) (P : PublicParameter) (B : QReg) (r : SigningRequest)
    (o : Option TopSel) :
    DropsTo W (signDN θ i P B r o) (signRN Unit θ (fun _ ↦ P) i r o B) := by
  rw [signDN, signRN, signWithN, signWithN]
  refine DropsTo.bind₂ (dropsTo_liftReadProg W _) fun gb ↦ ?_
  refine DropsTo.bind₂ (dropsTo_topWithN i P B r o) fun gt ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  exact DropsTo.bind₂ (dropsTo_pubBothN h i B r gb gt) fun _ ↦ DropsTo.pure _

theorem dropsTo_challengeDN (P : Fin n → PublicParameter) (A : QReg) (c : (MemoP n).A A) :
    DropsTo W (challengeDN θ P A c) (challengeWithN Unit (signRN Unit θ P) A c) := by
  rcases c with o | ⟨_ | ⟨i, q⟩, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · refine DropsTo.bind ?_ fun _ _ ↦ DropsTo.pure _
    rw [signAtN, signAtN, QComp.act_bind, QComp.act_bind]
    exact DropsTo.prim _ fun _ ↦ dropsTo_signDN h i (P i) _ q.1 q.2

/-- **The realized game with its reveals dropped is its read program with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_muGameD (valid : SignLog → Bool) (A : MuAdversary n) :
    DropsTo W (muGameD θ valid A) (muGameReadsT Unit θ valid A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeDN h _) _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ DropsTo.pure _

omit h in
/-- **At a good table, the game programs cells of the table with their values.** -/
theorem progsOfN_hwOf (S0 : Fin n → MasterSeed) {w : QTableN n} (hw : (tableN S0).good w) :
    ProgsOfN ((tableN S0).hwOf w) (thetaOfN S0 w) := fun i l e x p hp ↦ by
  rw [realize_progTN (isStruct_of_mem_layerPos hp) i (S0 i), userOf_thetaOfN, tabOf_thetaOf]
  exact (tableN S0).tableDb_cell hw w (i, p)

end drops

/-! ## The grind-only signer against functions consistent with the table -/

section honest

attribute [local irreducible] QTable.select

variable {M : Type} [Fintype M] [DecidableEq M]
  {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain)}
  {W : Hw HashOutput HashDomain} {m : M} {B : QReg}

theorem baseOfN_eq (θ : HPosN n → Digest) (i : Fin n) (rnd : Pos) :
    baseOfN θ i rnd = truncateHash (tabOf (userOf θ i) rnd) := by
  rw [baseOfN, tabRN, tabOf, tabOf, truncateHash_joinHalves, truncateHash_joinHalves]
  exact userOf_extendTN_restrictTo (mk_mem_atU i (Finset.mem_singleton_self _)) θ

theorem rootOfN_eq (θ : HPosN n → Digest) (i : Fin n) (r : SigningRequest) :
    rootOfN θ i r = (tabOf (userOf θ i)).bottomRoot r.leafIndex :=
  value_tabOf_congr (.tree bottomLayer layerHeight (keyIndexOnLayer r.leafIndex topLayer).val)
    (userOf_extendTN_restrictTo (mk_mem_atU i (Finset.mem_singleton_self _)) θ)

theorem layerOutN_eq (θ : HPosN n → Digest) (i : Fin n) (l : Layer) (e : KeyIndex)
    (ρ : Randomizer) (x : Encoding) :
    layerOutN θ i l e ρ x = layerSigOf (tabOf (userOf θ i)) l e ρ x := by
  have hv : ∀ q, vcoord q ∈ layerReveal l e x →
      (tabRN (restrictTo (atU i (layerReveal l e x)) θ) i).value q =
        (tabOf (userOf θ i)).value q := fun q hq ↦
    value_tabOf_congr q (userOf_extendTN_restrictTo (mk_mem_atU i hq) θ)
  simp only [layerOutN, layerSigOf, LayerSignature.mk.injEq, true_and]
  constructor
  · funext k
    exact hv (.chain l e k (x k).val) (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  · funext level
    exact hv (siblingQ l e level) (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ level)))

/-- **User `i`'s search through read ports returns the table's selection.** -/
theorem readsTo_selectRN (θ : HPosN n → Digest) (i : Fin n) {P : PublicParameter}
    (hP : P = (tabOf (userOf θ i)).param) (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (rnd : Pos) :
    ReadsTo t W m (selectRN M θ i P B l e message rnd)
      ((tabOf (userOf θ i)).select (overwrite W t).1 l e message
        (truncateHash (tabOf (userOf θ i) rnd))) := by
  subst hP
  rw [selectRN, baseOfN_eq, QTable.select]
  exact readsTo_grindT (M := M) (t := t) (W := W) (m := m) (B := B) (tabOf (userOf θ i)) l e
    message _ _ _

theorem topSelOf_eq (u : QTable) (H : HashDomain → HashOutput) (r : SigningRequest) :
    topSelOf u H (topKeyOf r) =
      u.select H topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (rootBytes (u.bottomRoot r.leafIndex))
        (truncateHash (u (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
          (u.bottomRoot r.leafIndex)))) :=
  rfl

/-- **The two layers' publications of the grind-only signer give the table's signature.** -/
theorem readsTo_pubBothN (θ : HPosN n → Digest) (i : Fin n) (r : SigningRequest) :
    ReadsTo t W m ((pubBothN (B := B) (fun l e ρ x ↦ QuantumComp₂.pure (layerOutN θ i l e ρ x)) r
      ((tabOf (userOf θ i)).select (overwrite W t).1 bottomLayer
        (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
        (truncateHash (tabOf (userOf θ i) (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer)
          r.message))))
      (topSelOf (tabOf (userOf θ i)) (overwrite W t).1 (topKeyOf r))))
      ((tabOf (userOf θ i)).signature (overwrite W t).1 r) := by
  rw [topSelOf_eq]
  simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
    QTable.layerSignature, QTable.bottomBase, QTable.topBase]
  rcases (tabOf (userOf θ i)).select (overwrite W t).1 bottomLayer
    (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
    (truncateHash (tabOf (userOf θ i) (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer)
      r.message))) with _ | ⟨ρ, x⟩ <;>
  rcases (tabOf (userOf θ i)).select (overwrite W t).1 topLayer
    (keyIndexOnLayer r.leafIndex topLayer)
    (rootBytes ((tabOf (userOf θ i)).bottomRoot r.leafIndex))
    (truncateHash (tabOf (userOf θ i) (.rndTop (keyIndexOnLayer r.leafIndex topLayer)
      ((tabOf (userOf θ i)).bottomRoot r.leafIndex)))) with _ | ⟨ρ', x'⟩
  · exact readsTo_pure _
  · exact readsTo_pure _
  · exact readsTo_pure _
  · simp only [pubBothN, Option.map_some, Option.bind_some, QuantumComp₂.pure_bind, layerOutN_eq]
    exact readsTo_pure _

/-- **The grind-only signer returns the table's signature and top selection** against
`(overwrite W t).1`, from a memoized selection that agrees with it. -/
theorem readsTo_signRN (θ : HPosN n → Digest) (P : Fin n → PublicParameter) (i : Fin n)
    (hP : P i = (tabOf (userOf θ i)).param) (r : SigningRequest) (h : Option TopSel)
    (hh : ∀ o, h = some o → o = topSelOf (tabOf (userOf θ i)) (overwrite W t).1 (topKeyOf r)) :
    ReadsTo t W m (signRN M θ P i r h B)
      ((tabOf (userOf θ i)).signature (overwrite W t).1 r,
        topSelOf (tabOf (userOf θ i)) (overwrite W t).1 (topKeyOf r)) := by
  have htop : ReadsTo t W m (topWithN (selectRN M θ i (P i) B) (rootOfN θ i r) r h)
      (topSelOf (tabOf (userOf θ i)) (overwrite W t).1 (topKeyOf r)) := by
    rcases h with _ | o
    · rw [topWithN, topSelOf_eq, ← rootOfN_eq]
      exact readsTo_selectRN θ i hP _ _ _ _
    · rw [topWithN, ← hh o rfl]
      exact readsTo_pure _
  rw [signRN, signWithN]
  refine (readsTo_selectRN θ i hP _ _ _ _).bind (htop.bind ?_)
  exact (readsTo_pubBothN θ i r).map fun s ↦ (s, _)

/-- The users' public keys revealed at `θ` are the table's. -/
theorem pkDN_eq (θ : HPosN n → Digest) (i : Fin n) : pkDN θ i = (tabOf (userOf θ i)).publicKey := by
  have hr : vcoord (.tree topLayer layerHeight 0) = loC rootPos := by
    change vcoord (.tree topLayer (15 + 1) 0) = _
    exact vcoord_tree_succ _ _ _ ⟨by decide, by decide⟩
  have hroot : (i, loC rootPos) ∈ pkRevealN (n := n) :=
    Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have hparam : (i, paramC) ∈ pkRevealN (n := n) :=
    Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩
  have h1 : (tabRN (restrictTo pkRevealN θ) i).treeValue topLayer layerHeight 0 =
      (tabOf (userOf θ i)).treeValue topLayer layerHeight 0 :=
    value_tabOf_congr (.tree topLayer layerHeight 0)
      (userOf_extendTN_restrictTo (hr ▸ hroot) θ)
  have h2 : (tabRN (restrictTo pkRevealN θ) i).param = (tabOf (userOf θ i)).param := by
    rw [tabRN, param_tabOf, param_tabOf]
    exact userOf_extendTN_restrictTo hparam θ
  unfold pkDN pksT QTable.publicKey
  rw [h1, h2]

/-- **The grind-only signer satisfies `SignsN`** at the hidden values of a table. -/
theorem signsN_signRN (S0 : Fin n → MasterSeed) (w : QTableN n) :
    SignsN t W m w (signRN M (thetaOfN S0 w) fun i ↦ (w.user i).publicKey.parameter) := by
  intro i r h B hh
  have e := readsTo_signRN (t := t) (W := W) (m := m) (B := B) (M := M) (thetaOfN S0 w)
    (fun i ↦ (w.user i).publicKey.parameter) i
    (by rw [userOf_thetaOfN, tabOf_thetaOf]; rfl) r h
    (by rw [userOf_thetaOfN, tabOf_thetaOf]; exact hh)
  rw [userOf_thetaOfN, tabOf_thetaOf] at e
  exact e

theorem muGameReadsT_thetaOfN (S0 : Fin n → MasterSeed) (w : QTableN n)
    (valid : SignLog → Bool) (A : MuAdversary n) :
    muGameReadsT M (thetaOfN S0 w) valid A =
      gameReadsWithN M (signRN M (thetaOfN S0 w) fun i ↦ (w.user i).publicKey.parameter)
        (fun i ↦ (w.user i).publicKey) valid A := by
  have hpk : pkDN (thetaOfN S0 w) = fun i ↦ (w.user i).publicKey := funext fun i ↦ by
    rw [pkDN_eq, userOf_thetaOfN, tabOf_thetaOf]
  rw [muGameReadsT, hpk]

end honest

/-! ## Runtime 1 on the realized template -/

section main

variable (M : Type) [Fintype M] [DecidableEq M] (upd : Fin n → TrialUpd M)

/-- **Runtime 1 runs the realized template as the lifted game** at a good table: runtime 1 with
record ports, the table's cells hardwired from the start, from any memory, running the template
game realized at `thetaOfN S0 w`, has the law of the lifted multi-user game in runtime 1 with the
table's cells hardwired. -/
theorem runtime1R_muGameT_eq (S0 : Fin n → MasterSeed) {w : QTableN n}
    (hw : (tableN S0).good w) (valid : SignLog → Bool) (A : MuAdversary n)
    (m₀ : Finset (HPosN n) × M) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (runtime1R HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap .instruments
        (realizeT (thetaOfN S0 w) (muGameT M upd valid A)) ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((tableN S0).hwOf w) ()).evalDistMap
        .instruments (liftH (muGame xmssRom valid S0 A)).liftOrdinary ρ f := by
  rw [evalDistMap_runtime1R_eq _ m₀ (dropRec_muGameT (thetaOfN S0 w) upd valid A),
    evalDistMap_runtime1_eq_spongeHardwiredReadRuntime _ ()
      (dropsTo_muGameD (progsOfN_hwOf S0 hw) valid A), muGameReadsT_thetaOfN]
  exact runtime1_muGame_eq_readsN S0 hw () (fun _ ↦ signsN_signRN S0 w) valid A ρ f

/-- **The QROM game on good tables is runtime 1 on the realized template** (G0 → G3 for `n`
users, the hybrid's left side): for any inner memory `M`, trial updates `upd` and initial memory
`m₀`, the uniform average over functions with a good table of the game's law is the uniform
average over good tables `w` of runtime 1 with record ports running `muGameT M upd valid A`
realized at `thetaOfN S0 w`. -/
theorem tableAvg_muGame_runtime1R (S0 : Fin n → MasterSeed) (valid : SignLog → Bool)
    (A : MuAdversary n) (m₀ : Finset (HPosN n) × M) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    ∑ H : HashDomain → HashOutput, (Fintype.card (HashDomain → HashOutput) : ℝ≥0∞)⁻¹ •
        (if (tableN S0).good ((tableN S0).tab H) then
          (additiveOracleRuntime H).evalDistMap .instruments (muGame xmssRom valid S0 A) ρ f
          else 0) =
      ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ •
        (if (tableN S0).good w then
          (runtime1R HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap .instruments
            (realizeT (thetaOfN S0 w) (muGameT M upd valid A)) ρ f
          else 0) :=
  (tableAvg_good (tableN S0) () .instruments (muGame xmssRom valid S0 A) ρ fun _ ↦ f).trans
    (Finset.sum_congr rfl fun w _ ↦ congrArg _ (by
      by_cases h : (tableN S0).good w
      · rw [ite_eq_left h, ite_eq_left h, runtime1R_muGameT_eq M upd S0 h valid A m₀ ρ f]
      · rw [ite_eq_right h, ite_eq_right h]))

/-- **The QROM law of an event of the multi-user game**: at most the bad fraction of tables plus
the average over good tables `w` of runtime 1 with record ports on the realized template. -/
theorem qromEvalDistMap_muGame_le_runtime1R (S0 : Fin n → MasterSeed) (valid : SignLog → Bool)
    (A : MuAdversary n) (m₀ : Finset (HPosN n) × M) (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) (s : Set γ) :
    qromEvalDistMap .instruments (muGame xmssRom valid S0 A) ρ (fun _ ↦ f) s ≤
      (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card +
        ∑ w : QTableN n, (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (if (tableN S0).good w then
            (runtime1R HashOutput HashDomain ((tableN S0).hwOf w) m₀).evalDistMap .instruments
              (realizeT (thetaOfN S0 w) (muGameT M upd valid A)) ρ f s
            else 0) :=
  (qromEvalDistMap_apply_le_tableAvg_good (tableN S0) () .instruments
    (muGame xmssRom valid S0 A) ρ (fun _ ↦ f) s).trans_eq
    (congrArg _ (Finset.sum_congr rfl fun w _ ↦ congrArg _ (by
      by_cases h : (tableN S0).good w
      · rw [ite_eq_left h, ite_eq_left h, runtime1R_muGameT_eq M upd S0 h valid A m₀ ρ f]
      · rw [ite_eq_right h, ite_eq_right h])))

end main

end Quantum.Qrom.Xmss.Multi

end
