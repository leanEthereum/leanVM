module

public import Quantum.Qrom.Xmss.Template
public import Quantum.Qrom.Xmss.Runtime1
public import Quantum.Xmss.Assembly.RecordDrop

@[expose] public section

/-!
# Runtime 1 runs the runtime-2 template realized at the table

For the master seed `S_0` and the table `v`, runtime 1 of the hybrid with record ports
(`runtime1R`, every cell of `(table S0).hwOf v` hardwired from the start, any initial memory) runs
the template game realized at the hidden values `thetaOf S0 v` with the law of the honest read
program `gameReads Unit A (v.publicKey, v.secretKey S0)` in runtime 1 (`runtime1R_gameT_eq`).
With `qrom_game_eq_runtime1`, the QROM game is the table average of runtime 1 on the realized
template (`qrom_game_eq_runtime1R`), the left side of the hybrid against `runtimeR`.

The three steps (the QRPM's, `Quantum.Xmss.Assembly.{GameT, RecordDrop}`, generic parts reused):

* **Records** (`dropRec_gameT`): the realized template drops to `gameD θ A` over `hwSpec` with
  memory `Unit`: reveals become their values `restrictTo T θ`, record calls disappear, reads keep
  the memory (`DropRec`); `evalDistMap_runtime1R_eq` forgets the memory register.
* **Programs** (`dropsTo_gameD`): every program call of `gameD (thetaOf S0 v) A` hardwires a cell
  `cellOf S0 p v` of the table with its value `v p` (`realize_progT`, `tableDb_cell`), so `gameD`
  is the read program `gameReadsT θ A` with program calls inserted (`DropsTo`), and
  `evalDistMap_runtime1_eq_spongeHardwiredReadRuntime` removes them.
* **Signer** (`evalDistMap_gameReads_eq_gameReadsT`): `gameReadsT` reads only the randomizer
  trials and takes the bases, chain values, paths and the bottom root from `tabOf θ`; against
  every function consistent with `v` both signers return `v.signature H r`
  (`readsTo_signR`), so both read programs have the game's law
  (`evalDistMap_game_eq_readsT`, `evalDistMap_game_eq_reads`), and runtime 1 averages over these
  functions (`read_port_eq_classical_read`).
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss (leafKey leafKey_val)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen progThen readLift readLiftQ RevealVals
  DropRec DropRec.bind₂ realizeT_bind₂ dropRec_realizeT_substitute dropRec_realizeT_act_bind
  dropRec_realizeT_bind dropRec_readLift_liftOrdinary ReadsRel readsRel_pure ReadsRel.bind
  ReadsRel.map readsRel_act_bind readsRel_readH_bind liftReadC liftReadProg DropsTo DropsTo.bind₂
  DropsTo.bind DropsTo.progCall_bind dropsTo_liftReadProg dropsTo_substitute progCall ProgOf
  runtime1R evalDistMap_runtime1R_eq evalDistMap_runtime1_eq_spongeHardwiredReadRuntime)
open Quantum.Sponge (read_port_eq_classical_read evalDistMap_hardwired_eq_avg)

attribute [local irreducible] xmssRom

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpec SigningRequest (Option Signature))

/-! ## The realized game without reveals, and its read program -/

section programs

/-- The layer signature with randomizer `ρ` and codeword `x` read from `θ` on the coordinates the
signature reveals. -/
def layerOut (θ : HPos → Digest) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    LayerSignature :=
  layerSigOf (tabR (restrictTo (layerReveal l e x) θ)) l e ρ x

/-- The randomizer base read from `θ` at the base's coordinate. -/
def baseOf (θ : HPos → Digest) (rnd : Pos) : Randomizer :=
  truncateHash (tabR (restrictTo {loC rnd} θ) rnd)

/-- The bottom root under a request's top key, read from `θ` at its coordinate. -/
def rootOf (θ : HPos → Digest) (r : SigningRequest) : Digest :=
  (tabR (restrictTo (rootReveal r) θ)).bottomRoot r.leafIndex

/-- The program calls of the positions `ps`, realized at `θ`. -/
noncomputable def progPosD (θ : HPos → Digest) (B : QReg) :
    List Pos → QComp (hwSpec HashOutput HashDomain Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall ((progT p).realize θ) B).bind fun _ ↦ progPosD θ B ps

/-- **A layer's search, realized with its reveal dropped**: read ports keeping the memory. -/
noncomputable def selectD (θ : HPos → Digest) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    QComp (hwSpec HashOutput HashDomain Unit) B B (Option (Randomizer × Encoding)) :=
  liftReadC (grindT Unit (keepUpd Unit) P B l e message (baseOf θ rnd) randomizerAttemptLimit 0)

/-- **Publishing a layer signature, realized with its reveal dropped**: the program calls of the
positions it makes public, then the signature read from `θ`. -/
noncomputable def publishD (θ : HPos → Digest) (B : QReg) (l : Layer) (e : KeyIndex)
    (ρ : Randomizer) (x : Encoding) :
    QComp (hwSpec HashOutput HashDomain Unit) B B LayerSignature :=
  (progPosD θ B (layerPos l e x)).bind fun _ ↦ QuantumComp₂.pure (layerOut θ l e ρ x)

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **A layer's search as reads**, from the base of `θ`. -/
noncomputable def selectR (θ : HPos → Digest) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (rnd : Pos) :
    QComp (hwReadSpec HashOutput HashDomain M) B B (Option (Randomizer × Encoding)) :=
  grindT M (keepUpd M) P B l e message (baseOf θ rnd) randomizerAttemptLimit 0

/-- Two layers' searches and publications as `signT` combines them, the top layer signing the
bottom root `root`. -/
noncomputable def signWith {spec : QuantumOracleSpec.{0, 0}} (B : QReg)
    (sel : Layer → KeyIndex → MsgBytes → Pos →
      QComp spec B B (Option (Randomizer × Encoding)))
    (pub : Layer → KeyIndex → Randomizer → Encoding → QComp spec B B LayerSignature)
    (root : Digest) (r : SigningRequest) : QComp spec B B (Option Signature) :=
  (sel bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
    (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message)).bind fun gb ↦
    (sel topLayer (keyIndexOnLayer r.leafIndex topLayer) (rootBytes root)
      (.rndTop (keyIndexOnLayer r.leafIndex topLayer) root)).bind fun gt ↦
      match gb, gt with
      | some (ρb, xb), some (ρt, xt) =>
        (pub bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) ρb xb).bind fun bottom ↦
          (pub topLayer (keyIndexOnLayer r.leafIndex topLayer) ρt xt).bind fun top ↦
            QuantumComp₂.pure
              (some ⟨r.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩)
      | _, _ => QuantumComp₂.pure none

/-- The answer to a signing request with the adversary's register held, from a signer. -/
noncomputable def signAtWith {spec : QuantumOracleSpec.{0, 0}}
    (sgn : ∀ B : QReg, SigningRequest → QComp spec B B (Option Signature)) (r : SigningRequest)
    (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp spec A (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  (QComp.act (spec := spec)
    (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ sgn _ r

/-- The signing answer as reads, the values from `θ`. -/
noncomputable def signAtR (θ : HPos → Digest) (P : PublicParameter) (r : SigningRequest)
    (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp (hwReadSpec HashOutput HashDomain M) A
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  signAtWith (fun B r ↦ signWith B (selectR M θ P B)
    (fun l e ρ x ↦ QuantumComp₂.pure (layerOut θ l e ρ x)) (rootOf θ r) r) r E ℓ

/-- **The challenger with honest reads, from a signer**: as `challengeReads`, a signing request
answered by `sgn`. -/
noncomputable def challengeWith (sk : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) →
        QComp (hwReadSpec HashOutput HashDomain M) A
          (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
          (Option Signature)) :
    IPFunctor.CommandSubstitution AdvP
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain M))
  | A, .prim o => (liftH (SufCma.challenge xmssRom sk A (.prim o))).liftOrdinary
  | A, .query .hash E ℓ => (liftH (SufCma.challenge xmssRom sk A (.query .hash E ℓ))).liftOrdinary
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (sgn r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The game's reads from a signer** (`gameReads` has the signer `signReads`). -/
noncomputable def gameReadsWith (sk : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) →
        QComp (hwReadSpec HashOutput HashDomain M) A
          (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
          (Option Signature))
    (pk : PublicKey) (A : Adversary) :
    QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeWith M sk sgn)
    (SufCma.withSignLog (A pk))) fun run ↦
    ((readsProgram M _ (xmssRom.verify pk run.1)).map Prod.fst).bind fun verified ↦
      QuantumComp₂.pure (xmssRom.winningCondition run.2 run.1 && verified)

/-- The public key revealed at `θ`. -/
def pkD (θ : HPos → Digest) : PublicKey :=
  pkT (restrictTo pkReveal θ)

/-- **The game's reads with the grind-only signer**: `gameReadsWith` with the signer `signAtR`,
which reads only the randomizer trials and takes the other values from `θ`. -/
noncomputable def gameReadsT (θ : HPos → Digest) (A : Adversary) :
    QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsWith M noKey (signAtR M θ (pkD θ).parameter) (pkD θ) A

/-- The signing answer of the realized game with its reveals dropped. -/
noncomputable def signAtD (θ : HPos → Digest) (P : PublicParameter) (r : SigningRequest)
    (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp (hwSpec HashOutput HashDomain Unit) A
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
      (Option Signature) :=
  signAtWith (fun B r ↦ signWith B (selectD θ P B) (publishD θ B) (rootOf θ r) r) r E ℓ

/-- **The challenger of the realized game with its reveals dropped**. -/
noncomputable def challengeD (θ : HPos → Digest) (P : PublicParameter) :
    IPFunctor.CommandSubstitution AdvP
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec HashOutput HashDomain Unit))
  | A, .prim o => liftReadProg ((liftH (SufCma.challenge xmssRom noKey A (.prim o))).liftOrdinary
      (t := hwReadCmdSpec HashOutput HashDomain Unit))
  | A, .query .hash E ℓ => liftReadProg ((liftH (SufCma.challenge xmssRom noKey A
      (.query .hash E ℓ))).liftOrdinary (t := hwReadCmdSpec HashOutput HashDomain Unit))
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signAtD θ P r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The realized template game with its reveals dropped** (over `hwSpec`, memory `Unit`). -/
noncomputable def gameD (θ : HPos → Digest) (A : Adversary) :
    QComp (hwSpec HashOutput HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeD θ (pkD θ).parameter)
    (SufCma.withSignLog (A (pkD θ)))) fun run ↦
    (liftReadC ((readsProgram Unit _ (xmssRom.verify (pkD θ) run.1)).map Prod.fst)).bind
      fun verified ↦
      QuantumComp₂.pure (xmssRom.winningCondition run.2 run.1 && verified)

end programs

/-! ## Dropping the reveals and records -/

section records

variable {M : Type} (θ : HPos → Digest)

theorem dropRec_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × (Finset HPos × M) → QComp (XSpec M) B C α)
    {y : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    (h : ∀ r, DropRec HPos (realizeT θ (k (restrictTo T θ, r))) y) :
    DropRec HPos (realizeT θ (revealThen goodQ T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThen {B C : QReg} {α : Type} (p : LazyProg HashOutput HashDomain HPos HD)
    {k : QComp (XSpec M) B C α} {y : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    (h : DropRec HPos (realizeT θ k) y) :
    DropRec HPos (realizeT θ (progThen p trivial k))
      ((progCall (p.realize θ) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize θ) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT θ k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPos (B : QReg) :
    ∀ ps : List Pos, DropRec HPos (realizeT θ (progPos M B ps)) (progPosD θ B ps)
  | [] => DropRec.pure _
  | _ :: ps => dropRec_progThen θ _ (dropRec_progPos B ps)

/-- **The randomizer search at memories `M` and `Unit`.** -/
theorem readsRel_grindT (upd : TrialUpd M) (P : PublicParameter) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ∀ n trial, ReadsRel goodQ θ (grindT M upd P B l e message base n trial)
      (grindT Unit (keepUpd Unit) P B l e message base n trial)
  | 0, _ => readsRel_pure θ _
  | n + 1, trial => by
    rw [grindT, grindT]
    refine readsRel_readH_bind θ _ _ _ fun o _ ↦ ?_
    dsimp only
    generalize Codeword.decode (truncateHash (o.getD 0)) = d
    cases d with
    | none => exact readsRel_grindT upd P B l e message base n (trial + 1)
    | some x => exact readsRel_pure θ _

/-- Stateful read programs at memories `M` and `Unit` that read alike from every log of hashed
cells. -/
def ReadsRelL {B : QReg} {α : Type}
    (x : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain M) B B) α)
    (y : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain Unit) B B) α) :
    Prop :=
  ∀ s, ReadsRel goodQ θ (x.run s) (y.run s)

theorem readsRelL_romReadImpl (B : QReg) (q : RomOracles.Domain) :
    ReadsRelL θ (romReadImpl M B q) (romReadImpl Unit B q) := fun s ↦ by
  rcases q with n | x
  · exact readsRel_act_bind (good := goodQ) θ (SubInstrument.uniform (Fin (n + 1)) B)
      fun a ↦ readsRel_pure θ (a, s)
  · exact readsRel_readH_bind θ x keepMem keepMem
      (k := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [x]))
      (k' := fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [x])) fun _ _ ↦ readsRel_pure θ _

theorem readsRelL_simulateQ (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ReadsRelL θ (simulateQ (romReadImpl M B) x) (simulateQ (romReadImpl Unit B) x) := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro s
    rw [simulateQ_pure, simulateQ_pure]
    exact readsRel_pure θ (a, s)
  | query_bind q k ih =>
    intro s
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    exact (readsRelL_romReadImpl θ B q s).bind fun p ↦ ih p.1 p.2

/-- **The read program of a computation at memories `M` and `Unit`.** -/
theorem readsRel_readsProgram (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ReadsRel goodQ θ (readsProgram M B x) (readsProgram Unit B x) :=
  readsRelL_simulateQ θ B x []

variable (upd : TrialUpd M)

theorem dropRec_selectT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) :
    DropRec HPos (realizeT θ (selectT M upd P B l e message rnd))
      (selectD θ P B l e message rnd) := by
  rw [selectT]
  exact dropRec_revealThen θ _ _ fun _ ↦ readsRel_grindT θ upd P B l e message _ _ _

theorem dropRec_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    DropRec HPos (realizeT θ (publishT M B l e ρ x)) (publishD θ B l e ρ x) := by
  rw [publishT]
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progPos θ B _) fun _ ↦ DropRec.pure _

theorem dropRec_signT (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    DropRec HPos (realizeT θ (signT M upd P B r))
      (signWith B (selectD θ P B) (publishD θ B) (rootOf θ r) r) := by
  rw [signT, signWith, realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selectT θ upd P B _ _ _ _) fun gb ↦ ?_
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  dsimp only
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_selectT θ upd P B _ _ _ _) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact DropRec.pure _
  · exact DropRec.pure _
  · exact DropRec.pure _
  · rw [realizeT_bind₂]
    refine DropRec.bind₂ (dropRec_publishT θ B _ _ _ _) fun _ ↦ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_publishT θ B _ _ _ _) fun _ ↦ DropRec.pure _

theorem dropRec_signAt (P : PublicParameter) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    DropRec HPos (realizeT θ (signAt M upd P r E ℓ)) (signAtD θ P r E ℓ) := by
  rw [signAt, signAtD, signAtWith]
  exact dropRec_realizeT_act_bind θ _ fun _ ↦ dropRec_signT θ upd P _ r

theorem dropRec_challengeT (P : PublicParameter) (A : QReg) (c : (AdvP).A A) :
    DropRec HPos (realizeT θ (challengeT M upd P A c)) (challengeD θ P A c) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_readLift_liftOrdinary θ _
  · exact dropRec_realizeT_bind θ (dropRec_signAt θ upd P r E ℓ) fun _ _ ↦ DropRec.pure _

/-- **The realized game drops to `gameD`**: with its record calls removed and its reads keeping
the memory `Unit`, the realized template game is `gameD θ A`. -/
theorem dropRec_gameT (A : Adversary) :
    DropRec HPos (realizeT θ (gameT M upd A)) (gameD θ A) := by
  refine dropRec_revealThen θ _ _ fun _ ↦ ?_
  dsimp only
  rw [realizeT_bind₂, gameD]
  refine DropRec.bind₂ (dropRec_realizeT_substitute θ (dropRec_challengeT θ upd _) _)
    fun run ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ ((readsRel_readsProgram θ _ _).map Prod.fst) fun _ ↦ DropRec.pure _

end records

/-! ## Dropping the program calls -/

section drops

variable {W : Hw HashOutput HashDomain}

/-- Every program port of a position the game may program hardwires a cell of `W` with its `W`
value. -/
def ProgsOf (W : Hw HashOutput HashDomain) (θ : HPos → Digest) : Prop :=
  ∀ (l : Layer) (e : KeyIndex) (x : Encoding), ∀ p ∈ layerPos l e x, ProgOf W ((progT p).realize θ)

theorem dropsTo_progPosD (θ : HPos → Digest) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec HashOutput HashDomain Unit) B C α}
    {y : QComp (hwReadSpec HashOutput HashDomain Unit) B C α} (hx : DropsTo W x y) :
    ∀ ps : List Pos, (∀ p ∈ ps, ProgOf W ((progT p).realize θ)) →
      DropsTo W ((progPosD θ B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPosD, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPosD θ B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

variable {θ : HPos → Digest} (h : ProgsOf W θ)
include h

theorem dropsTo_signAtD (P : PublicParameter) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    DropsTo W (signAtD θ P r E ℓ) (signAtR Unit θ P r E ℓ) := by
  rw [signAtD, signAtR, signAtWith, signAtWith, QComp.act_bind, QComp.act_bind]
  refine DropsTo.prim _ fun _ ↦ ?_
  refine DropsTo.bind₂ (dropsTo_liftReadProg W _) fun gb ↦ ?_
  refine DropsTo.bind₂ (dropsTo_liftReadProg W _) fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact DropsTo.pure _
  · exact DropsTo.pure _
  · exact DropsTo.pure _
  · simp only [publishD, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
    exact dropsTo_progPosD θ _ (dropsTo_progPosD θ _ (DropsTo.pure _) _ (h _ _ _)) _
      (h _ _ _)

theorem dropsTo_challengeD (P : PublicParameter) (A : QReg) (c : (AdvP).A A) :
    DropsTo W (challengeD θ P A c) (challengeWith Unit noKey (signAtR Unit θ P) A c) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · exact DropsTo.bind (dropsTo_signAtD h P r E ℓ) fun _ _ ↦ DropsTo.pure _

/-- **The realized game with its reveals dropped is its read program with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_gameD (A : Adversary) : DropsTo W (gameD θ A) (gameReadsT Unit θ A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeD h _) _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ DropsTo.pure _

omit h in
/-- **At the table, the game programs cells of the table with their values.** -/
theorem progsOf_hwOf (S0 : MasterSeed) (v : QTable) :
    ProgsOf ((table S0).hwOf v) (thetaOf S0 v) := fun l e x p hp ↦ by
  rw [realize_progT (isStruct_of_mem_layerPos hp) S0, tabOf_thetaOf]
  exact (table S0).tableDb_cell v v p

end drops

/-! ## The grind-only signer against functions consistent with the table -/

section honest

variable {M : Type} [Fintype M] [DecidableEq M]
  {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain)}
  {W : Hw HashOutput HashDomain} {m : M} {B : QReg}

/-- **The randomizer search through read ports returns the table's selection.** -/
theorem readsTo_grindT (v : QTable) (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (base : Randomizer) : ∀ n trial,
    ReadsTo t W m (grindT M (keepUpd M) v.param B l e message base n trial)
      (v.selectFrom (overwrite W t).1 l e message base n trial)
  | 0, _ => readsTo_pure _
  | n + 1, trial => by
    rw [grindT, QTable.selectFrom]
    refine (readsTo_readCall (.readH (trialCell v.param l e message base trial)
      (keepUpd M l e (trialCell v.param l e message base trial))) rfl B).bind ?_
    change ReadsTo t W m (match Codeword.decode (truncateHash ((overwrite W t).1
      (trialCell v.param l e message base trial))) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindT M (keepUpd M) v.param B l e message base n (trial + 1)) _
    rw [show v.messageDigest (overwrite W t).1 l e message (base + BitVec.ofNat digestBits trial)
      = truncateHash ((overwrite W t).1 (trialCell v.param l e message base trial)) from rfl]
    cases Codeword.decode (truncateHash ((overwrite W t).1
        (trialCell v.param l e message base trial))) with
    | none => exact readsTo_grindT v l e message base n (trial + 1)
    | some x => exact readsTo_pure _

theorem baseOf_eq (θ : HPos → Digest) (rnd : Pos) :
    baseOf θ rnd = truncateHash (tabOf θ rnd) := by
  rw [baseOf, tabR, tabOf, tabOf, truncateHash_joinHalves, truncateHash_joinHalves]
  exact extendT_restrictTo (Finset.mem_singleton_self _) θ

theorem layerSigOf_congr (θ : HPos → Digest) {T : Finset HPos} {l : Layer} {e : KeyIndex}
    {x : Encoding} (hT : layerReveal l e x ⊆ T) (ρ : Randomizer) :
    layerSigOf (tabR (restrictTo T θ)) l e ρ x = layerSigOf (tabOf θ) l e ρ x := by
  have hv : ∀ q, vcoord q ∈ layerReveal l e x →
      (tabR (restrictTo T θ)).value q = (tabOf θ).value q := fun q hq ↦
    value_tabOf_congr q (extendT_restrictTo (hT hq) θ)
  simp only [layerSigOf, LayerSignature.mk.injEq, true_and]
  constructor
  · funext i
    exact hv (.chain l e i (x i).val) (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  · funext level
    exact hv (siblingQ l e level) (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ level)))

theorem rootOf_eq (θ : HPos → Digest) (r : SigningRequest) :
    rootOf θ r = (tabOf θ).bottomRoot r.leafIndex :=
  value_tabOf_congr (.tree bottomLayer layerHeight (keyIndexOnLayer r.leafIndex topLayer).val)
    (extendT_restrictTo (Finset.mem_singleton_self _) θ)

theorem layerOut_eq (θ : HPos → Digest) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : layerOut θ l e ρ x = layerSigOf (tabOf θ) l e ρ x :=
  layerSigOf_congr θ subset_rfl ρ

/-- **A layer's search through read ports returns the table's selection.** -/
theorem readsTo_selectR (θ : HPos → Digest) (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (rnd : Pos) :
    ReadsTo t W m (selectR M θ (tabOf θ).param B l e message rnd)
      ((tabOf θ).select (overwrite W t).1 l e message (truncateHash (tabOf θ rnd))) := by
  rw [selectR, baseOf_eq]
  exact readsTo_grindT (tabOf θ) l e message _ _ _

/-- **The grind-only signer returns the table's signature** against `(overwrite W t).1`. -/
theorem readsTo_signR (θ : HPos → Digest) (r : SigningRequest) :
    ReadsTo t W m (signWith B (selectR M θ (tabOf θ).param B)
      (fun l e ρ x ↦ QuantumComp₂.pure (layerOut θ l e ρ x)) (rootOf θ r) r)
      ((tabOf θ).signature (overwrite W t).1 r) := by
  set H := (overwrite W t).1
  set v := tabOf θ
  rw [signWith, rootOf_eq]
  refine (readsTo_selectR θ _ _ _ _).bind ((readsTo_selectR θ _ _ _ _).bind ?_)
  simp only [QTable.signature, QTable.bottomSignature, QTable.topSignature,
    QTable.layerSignature, QTable.bottomBase, QTable.topBase]
  rcases v.select H bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
    (messageBytes r.message) (truncateHash (v (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer)
      r.message))) with _ | ⟨ρ, x⟩ <;>
  rcases v.select H topLayer (keyIndexOnLayer r.leafIndex topLayer)
    (rootBytes (v.bottomRoot r.leafIndex))
    (truncateHash (v (.rndTop (keyIndexOnLayer r.leafIndex topLayer) (v.bottomRoot r.leafIndex))))
    with _ | ⟨ρ', x'⟩
  · exact readsTo_pure _
  · exact readsTo_pure _
  · exact readsTo_pure _
  · simp only [Option.map_some, Option.bind_some, QuantumComp₂.pure_bind, layerOut_eq]
    exact readsTo_pure _

variable (t W m)

/-- **The challenger with the grind-only signer intertwines with the challenger** against a
function consistent with the table. -/
theorem intertwines_challengeR {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : QReg) (c : (AdvP).A A) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A)
      (fun p : Σ u, {b : (AdvP).B A c // (AdvP).src A c b = u} ↦ (hwAt W m).amplifyLeft p.1)
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (SufCma.challenge xmssRom (v.secretKey S0) A c))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (challengeWith M noKey (signAtR M (thetaOf S0 v) v.param) A c)) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact intertwines_liftH t W m _
  · exact intertwines_liftH t W m _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (overwrite W t).1).run .instruments
        (QuantumComp.bind (SufCma.signTree xmssRom (v.secretKey S0) r E ℓ) _))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run .instruments
        (QuantumComp.bind (signAtR M (thetaOf S0 v) v.param r E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) ?_) fun p ↦ ?_
    · rw [SufCma.signTree, signAtR, signAtWith]
      refine intertwines_run₂_act_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) (A := A)
        (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E)) _
        fun _ ↦ ?_
      have hs := readsTo_signR (t := t) (W := W) (m := m)
        (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
        (M := M) (thetaOf S0 v) r
      rw [tabOf_thetaOf] at hs
      exact intertwines_of_classicalOn_readsTo t W m
        ((classicalOn_toQuantumAt_romImpl_pure QTable.not_signRead_inl _
          (QTable.signReads_sign hv r)).congr (congrArg pure (QTable.eval_sign hv r)) rfl) hs
    · exact intertwines_run_pure (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) _

theorem pkD_eq (θ : HPos → Digest) : pkD θ = (tabOf θ).publicKey := by
  have hr : vcoord (.tree topLayer layerHeight 0) = loC rootPos := by
    change vcoord (.tree topLayer (15 + 1) 0) = _
    exact vcoord_tree_succ _ _ _ ⟨by decide, by decide⟩
  have hroot : loC rootPos ∈ pkReveal := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hparam : paramC ∈ pkReveal := Finset.mem_insert_self _ _
  have h1 : (tabR (restrictTo pkReveal θ)).treeValue topLayer layerHeight 0 =
      (tabOf θ).treeValue topLayer layerHeight 0 :=
    value_tabOf_congr (.tree topLayer layerHeight 0)
      (extendT_restrictTo (hr ▸ hroot) θ)
  have h2 : (tabR (restrictTo pkReveal θ)).param = (tabOf θ).param := by
    rw [tabR, param_tabOf, param_tabOf]
    exact extendT_restrictTo hparam θ
  unfold pkD pkT QTable.publicKey
  rw [h1, h2]

omit [Fintype M] [DecidableEq M] in
/-- The challenger's local operations and hash calls do not read the secret key. -/
theorem challengeWith_sk (sk sk' : SecretKey)
    (sgn : ∀ (r : SigningRequest) (E : QReg) {A : QReg},
      (A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) →
        QComp (hwReadSpec HashOutput HashDomain M) A
          (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
          (Option Signature)) :
    challengeWith M sk sgn = challengeWith M sk' sgn := by
  funext A c
  rcases c with o | ⟨_ | r, E, ℓ⟩ <;> rfl

omit [Fintype M] [DecidableEq M] in
theorem gameReadsT_thetaOf (S0 : MasterSeed) (v : QTable) (A : Adversary) :
    gameReadsT M (thetaOf S0 v) A =
      gameReadsWith M (v.secretKey S0) (signAtR M (thetaOf S0 v) v.param) v.publicKey A := by
  rw [gameReadsT, pkD_eq, tabOf_thetaOf, gameReadsWith, gameReadsWith,
    challengeWith_sk noKey (v.secretKey S0)]
  rfl

/-- **The game and its grind-only reads intertwine** against a function consistent with the
table. -/
theorem intertwines_game_gameReadsT {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : Adversary) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (SufCma.game xmssRom S0 A))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        (gameReadsT M (thetaOf S0 v) A)) := by
  rw [gameReadsT_thetaOf, SufCma.game, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_romImpl_pure QTable.not_tableRead_inl _
      (QTable.cellReads_generateKeys hv)).congr
      (congrArg pure (QTable.eval_generateKeys hv)) rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_run₂_of_run (intertwines_substitute
      (spec₀ := SufCma.advSpec SigningRequest (Option Signature))
      (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (fun A c ↦ intertwines_challengeR t W m hv A c) _))
    fun run ↦ ?_
  exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _))
    fun _ ↦ intertwines_run₂_pure _

/-- **The game is its grind-only reads at a fixed function** consistent with the table. -/
theorem evalDistMap_game_eq_readsT {S0 : MasterSeed} {v : QTable}
    (hv : Consistent S0 v (overwrite W t).1) (A : Adversary) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (overwrite W t).1).evalDistMap .instruments
        (SufCma.game xmssRom S0 A) ρ f =
      (spongeFnReadRuntime HashOutput HashDomain t W m).evalDistMap .instruments
        (gameReadsT M (thetaOf S0 v) A) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_game_gameReadsT t W m hv A)) ρ f

end honest

/-! ## Runtime 1 on the realized template -/

section main

variable (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The two read programs have the same law in runtime 1** started with the table's cells
hardwired: `gameReads` from the table's keys and `gameReadsT` at `thetaOf S0 v`. -/
theorem evalDistMap_gameReads_eq_gameReadsT (S0 : MasterSeed) (v : QTable) (m₀ : M)
    (A : Adversary) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (gameReads M A (v.publicKey, v.secretKey S0)) ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap
        .instruments (gameReadsT M (thetaOf S0 v) A) ρ f := by
  refine (read_port_eq_classical_read _ _ _ _ _ _).trans (Eq.trans
    (Finset.sum_congr rfl fun t _ ↦ congrArg _ ?_) (read_port_eq_classical_read _ _ _ _ _ _).symm)
  exact (evalDistMap_game_eq_reads (t := t) (W := (table S0).hwOf v) (m := m₀)
    (consistent_fill S0 v t.1) A ρ f).symm.trans
    (evalDistMap_game_eq_readsT t ((table S0).hwOf v) m₀ (consistent_fill S0 v t.1) A ρ f)

/-- **Runtime 1 runs the realized template as the honest reads**: runtime 1 with record ports,
the table's cells hardwired from the start, from any memory, running the template game realized
at `thetaOf S0 v`, has the law of `gameReads Unit A (v.publicKey, v.secretKey S0)` in S5's
runtime 1 with the table's cells hardwired. -/
theorem runtime1R_gameT_eq (S0 : MasterSeed) (v : QTable) (A : Adversary)
    (m₀ : Finset HPos × M) (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (runtime1R HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap .instruments
        (realizeT (thetaOf S0 v) (gameT M upd A)) ρ f =
      (spongeHardwiredReadRuntime HashOutput HashDomain ((table S0).hwOf v) ()).evalDistMap
        .instruments (gameReads Unit A (v.publicKey, v.secretKey S0)) ρ f := by
  rw [evalDistMap_runtime1R_eq _ m₀ (dropRec_gameT (thetaOf S0 v) upd A),
    evalDistMap_runtime1_eq_spongeHardwiredReadRuntime _ ()
      (dropsTo_gameD (progsOf_hwOf S0 v) A),
    evalDistMap_gameReads_eq_gameReadsT]

/-- **The QROM game is runtime 1 on the realized template, averaged over the table** (G0 → G3 of
the design, in the form of the hybrid's left side): for any inner memory `M`, trial update `upd`
and initial memory `m₀`, the game's law is the uniform average over the table values `v` of
runtime 1 with record ports (the table's cells hardwired) running `gameT M upd A` realized at
`thetaOf S0 v`. -/
theorem qrom_game_eq_runtime1R (S0 : MasterSeed) (A : Adversary) (m₀ : Finset HPos × M)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    qromEvalDistMap .instruments (SufCma.game xmssRom S0 A) ρ (fun _ ↦ f) =
      ∑ v : QTable, (Fintype.card QTable : ℝ≥0∞)⁻¹ •
        (runtime1R HashOutput HashDomain ((table S0).hwOf v) m₀).evalDistMap .instruments
          (realizeT (thetaOf S0 v) (gameT M upd A)) ρ f :=
  (qrom_game_eq_runtime1 S0 () A ρ f).trans
    (Finset.sum_congr rfl fun v _ ↦ congrArg _ (runtime1R_gameT_eq M upd S0 v A m₀ ρ f).symm)

end main

end Quantum.Qrom.Xmss

end
