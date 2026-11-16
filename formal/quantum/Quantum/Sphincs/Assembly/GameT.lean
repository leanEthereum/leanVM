module

public import Quantum.Sphincs.Assembly.FullTable
public import Quantum.Sphincs.Assembly.Template.Exempt
public import Quantum.Sphincs.Assembly.Reparam
public import Quantum.Xmss.Assembly.RecordDrop
public import Quantum.Xmss.Assembly.MassSources

@[expose] public section

/-!
# leanSPHINCS's template game against runtime 1

The hybrid side of the chain runs the template game (`Quantum.Sphincs.Assembly.Template`) with the
digest policy `msgPol` at a table `L`: public data `pubOf L`, hidden values `valueAt L`.

* **The realized game without reveals and record calls** `gameD pub v A` (over `hwSpec` with
  memory `Unit`): the signer `signD` programs the `H_msg` calls (`digestPorts` at `msgPol`), the
  FORS opening's slots (`forsOpenD`) and each layer's slots (`signLayerD`), its counter searches
  read through read ports keeping the memory. RecordDrop's `dropRec_gameT` relates it to the
  realized template game.
* **The grind-only read game** `gameReadsT pub v A` (over `hwReadSpec`): the same without the
  program calls (`signR`, `signLayerR`); it reads only the counter searches' trials, the other
  values of a signature are taken from `v` (`dgOf`, `rndD`, `forsOf`, `layerSigOf`).
* `dropsTo_gameD`: if every program call hardwires a cell of `W` with its `W` value
  (`ProgsOf W pub v`: the in-table slots and the `H_msg` calls), `gameD` is `gameReadsT` with
  program calls inserted. `progsOf_fullHw`: at `pubOf L`, `valueAt L` this holds for FullTable's
  `fullHw L` (the realized ports are the honest paths' cells, `realize_slotPorts`,
  `realize_hmsgPorts`; the corrections vanish at the honest values, `cor128_honest`,
  `out256_hmsg`).
* **FullTable's contract** `fullReads_gameReadsT : FullReads A (fun pub v ↦ gameReadsT pub v A)`:
  the game does not read the public keys (`gameReadsT_keys`), reads the hidden values only on the
  full coordinates (`gameReadsT_congr`), and against the honest functions of `L` has the law of
  `gameReads` after honest key generation (`evalDistMap_gameReads_eq_gameReadsT`): every read is
  deterministic and the grind-only signer returns `L.signature M` (`readsTo_signR`).
-/

open Matrix
open scoped Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common Common.SufCma
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput truncateHash
  littleEndianBytes)
open Quantum.Xmss (X Z blocks trunc128 out256 keccakStateEquiv)
open Quantum.Xmss.Hybrid (LazyProg restrictTo restrictTo_eq Agree)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec RevealVals revealThen progThen readLift readLiftQ
  realizeT hashTrial DropsTo ProgOf progCall liftReadProg dropsTo_liftReadProg dropsTo_substitute
  rnK rnR rnZ embed128 embed128_xor_self)

namespace Quantum.Sphincs.Assembly

/-! ## The realized game without reveals, and its read program -/

section programs

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The program calls of the template ports `ps` realized at `v`. -/
noncomputable def progPortsD (B : QReg) :
    List (LazyProg X Z HPos XD) → QComp (hwSpec X Z Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | p :: ps => (progCall (p.realize v) B).bind fun _ ↦ progPortsD B ps

/-- The program calls of the honest paths of the slots `ss`, realized at `v`. -/
noncomputable def progSlotsD (B : QReg) : List Slot → QComp (hwSpec X Z Unit) B B Unit
  | [] => QuantumComp₂.pure ()
  | s :: ss => (progPortsD v B (slotPorts pub s)).bind fun _ ↦ progSlotsD B ss

/-- The value the key `K` signs, revealed at `msgPos K`. -/
def keyMsgOf (K : Key) : Digest :=
  extendVals (restrictTo {HPos.val (msgPos K)} v) (msgPos K)

/-- The layer signature by `K` with counter `c` and codeword `x`, its values revealed on
`layerNeed`. -/
def layerSigOf (K : Key) (c : EncodingCounter) (x : Encoding) : LayerSignature K.1 :=
  ⟨c, fun i ↦ extendVals (restrictTo (valSet (layerNeed K.1 K.2.1 K.2.2 x)) v)
      (cpos K.1 K.2.1 K.2.2 i (x i).val),
    fun z ↦ extendVals (restrictTo (valSet (layerNeed K.1 K.2.1 K.2.2 x)) v)
      (siblingPos K.1 K.2.1 K.2.2 z)⟩

/-- The FORS opening of instance `idx` at the leaves `lv`, its values revealed on `forsNeed`. -/
def forsOf (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : ForsTreeIndex → ForsTreeOpening :=
  fun κ ↦ ⟨extendVals (restrictTo (valSet (forsNeed idx lv)) v) (.forsSecret idx κ (lv κ)),
    fun z ↦ extendVals (restrictTo (valSet (forsNeed idx lv)) v) (forsSibPos idx lv κ z)⟩

/-- The digest of `M` at `msgPol`, from the revealed `H_msg` outputs. -/
def dgOf (msg : Message) : MessageDigest :=
  digestOf msgPol ∅ msg (restrictTo (msgPol.need ∅ msg) v)

/-- The randomizer of `M`, revealed with `PK.root`. -/
def rndD (msg : Message) : Randomizer :=
  extendRnd (restrictTo {HPos.val rootPos, HPos.rnd msg} v) msg

/-- The public key the game reveals. -/
def pkD : PublicKey :=
  pkOf pub (restrictTo {HPos.val rootPos} v)

/-- **A layer signature, realized with its reveals dropped**: the counter search through read
ports (keeping the memory) on the value `K` signs, then the program calls of the slots the
signature makes public. -/
noncomputable def signLayerD (B : QReg) (K : Key) :
    QComp (hwSpec X Z Unit) B B (Option (LayerSignature K.1)) :=
  (Quantum.Xmss.Assembly.liftReadQ Unit
      (grindK Unit (keepUpd Unit) pub B K (keyMsgOf v K) encodingAttemptLimit 0)).bind
    fun g ↦ match g with
    | none => QuantumComp₂.pure none
    | some (c, x) => (progSlotsD pub v B (layerSlots K.1 K.2.1 K.2.2 x)).bind fun _ ↦
        QuantumComp₂.pure (some (layerSigOf v K c x))

/-- **A layer signature as reads**: the counter search through read ports; the opened chain values
and the path are the values `v`. -/
noncomputable def signLayerR (B : QReg) (K : Key) :
    QComp (hwReadSpec X Z Unit) B B (Option (LayerSignature K.1)) :=
  (grindK Unit (keepUpd Unit) pub B K (keyMsgOf v K) encodingAttemptLimit 0).bind fun g ↦
    match g with
    | none => QuantumComp₂.pure none
    | some (c, x) => QuantumComp₂.pure (some (layerSigOf v K c x))

/-- The FORS opening, realized with its reveal dropped: the program calls of its slots. -/
noncomputable def forsOpenD (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QComp (hwSpec X Z Unit) B B (ForsTreeIndex → ForsTreeOpening) :=
  (progSlotsD pub v B (forsSlots idx lv)).bind fun _ ↦ QuantumComp₂.pure (forsOf v idx lv)

/-- **A signature at `msgPol`, realized with its reveals dropped.** -/
noncomputable def signD (B : QReg) (msg : Message) :
    QComp (hwSpec X Z Unit) B B (Option Signature) :=
  (progPortsD v B (digestPorts pub msgPol ∅ msg)).bind fun _ ↦
  (forsOpenD pub v B (digestIndex (dgOf v msg)) (digestForsLeaves (dgOf v msg))).bind fun fo ↦
  (signLayerD pub v B (keyOf 0 (digestIndex (dgOf v msg)))).bind fun s₀ ↦
    match s₀ with
    | none => QuantumComp₂.pure none
    | some bottom =>
      (signLayerD pub v B (keyOf 1 (digestIndex (dgOf v msg)))).bind fun s₁ ↦
        match s₁ with
        | none => QuantumComp₂.pure none
        | some middle =>
          (signLayerD pub v B (keyOf 2 (digestIndex (dgOf v msg)))).bind fun s₂ ↦
            match s₂ with
            | none => QuantumComp₂.pure none
            | some top => QuantumComp₂.pure (some ⟨rndD v msg, fo,
                KeyGenerationAndSigning.layerSignatures bottom middle top⟩)

/-- The grind-only signer at the digest's index `idx` and FORS leaves `lv`. -/
noncomputable def signRAt (B : QReg) (msg : Message) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) : QComp (hwReadSpec X Z Unit) B B (Option Signature) :=
  (QuantumComp₂.pure (forsOf v idx lv) : QComp (hwReadSpec X Z Unit) B B _).bind fun fo ↦
  (signLayerR pub v B (keyOf 0 idx)).bind fun s₀ ↦
    match s₀ with
    | none => QuantumComp₂.pure none
    | some bottom =>
      (signLayerR pub v B (keyOf 1 idx)).bind fun s₁ ↦
        match s₁ with
        | none => QuantumComp₂.pure none
        | some middle =>
          (signLayerR pub v B (keyOf 2 idx)).bind fun s₂ ↦
            match s₂ with
            | none => QuantumComp₂.pure none
            | some top => QuantumComp₂.pure (some ⟨rndD v msg, fo,
                KeyGenerationAndSigning.layerSignatures bottom middle top⟩)

/-- **The grind-only signer**: the counter searches through read ports, every other value of the
signature from `v`. -/
noncomputable def signR (B : QReg) (msg : Message) :
    QComp (hwReadSpec X Z Unit) B B (Option Signature) :=
  signRAt pub v B msg (digestIndex (dgOf v msg)) (digestForsLeaves (dgOf v msg))

/-- The signing answer of the realized game with its reveals dropped. -/
noncomputable def signAtD (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (hwSpec X Z Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature) :=
  (QComp.act (spec := hwSpec X Z Unit) (B := QReg.of (sAdvSpec.Out (.sign msg) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signD pub v _ msg

/-- The signing answer as reads. -/
noncomputable def signAtR (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    QComp (hwReadSpec X Z Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature) :=
  (QComp.act (spec := hwReadSpec X Z Unit) (B := QReg.of (sAdvSpec.Out (.sign msg) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ signR pub v _ msg

/-- **The challenger of the realized game with its reveals dropped**: as `challengeT`, the reads
lifted to `hwSpec` and a signing request answered by `signAtD`. -/
noncomputable def challengeD :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwSpec X Z Unit))
  | A, .prim o => liftReadProg ((simulate LocalSig.Interp.instruments pub.perm
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv (0 : SecretKey) A
        (.prim o))).liftOrdinary (t := hwReadCmdSpec X Z Unit))
  | A, .query (.perm p) E ℓ => liftReadProg ((simulate LocalSig.Interp.instruments pub.perm
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv (0 : SecretKey) A
        (.query (.perm p) E ℓ))).liftOrdinary (t := hwReadCmdSpec X Z Unit))
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (signAtD pub v msg E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The realized template game at `msgPol` with its reveals dropped** (over `hwSpec`): the
adversary on the revealed public key against `challengeD`, the verification through read ports,
the winning condition. -/
noncomputable def gameD (A : SAdversary) :
    QComp (hwSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeD pub v) (withSignLog (A (pkD pub v))))
    fun run ↦ (Quantum.Xmss.Assembly.liftReadQ Unit ((readsProgram Unit pub.perm _
      (schemeWithHash.verify (pkD pub v) run.1)).map Prod.fst)).bind fun verified ↦
        QuantumComp₂.pure (RandomPermutationModel.sufCmaScheme.winningCondition run.2 run.1 &&
          verified)

end programs

section reads

/-- **The challenger with honest reads, from a signer**: as `challengeReads`, a signing request
answered by `sgn`. -/
noncomputable def challengeWith (π : Equiv.Perm (X × Z)) (sk : SecretKey)
    (sgn : ∀ (msg : Message) (E : QReg) {A : QReg}, (A ≃ sAdvSpec.In (.sign msg) × E) →
      QComp (hwReadSpec X Z Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature)) :
    IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec X Z Unit))
  | A, .prim o => (simulate LocalSig.Interp.instruments π
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv sk A (.prim o))).liftOrdinary
  | A, .query (.perm p) E ℓ => (simulate LocalSig.Interp.instruments π
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv sk A
        (.query (.perm p) E ℓ))).liftOrdinary
  | _, .query (.sign msg) E ℓ =>
      QuantumComp.bind (sgn msg E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The game's reads from a signer** (`gameReads` has the signer `signReads`). -/
noncomputable def gameReadsWith (π : Equiv.Perm (X × Z)) (sk : SecretKey)
    (sgn : ∀ (msg : Message) (E : QReg) {A : QReg}, (A ≃ sAdvSpec.In (.sign msg) × E) →
      QComp (hwReadSpec X Z Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature))
    (pk : PublicKey) (A : SAdversary) :
    QComp (hwReadSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeWith π sk sgn) (withSignLog (A pk)))
    fun run ↦ ((readsProgram Unit π _ (schemeWithHash.verify pk run.1)).map Prod.fst).bind
      fun verified ↦ QuantumComp₂.pure
        (RandomPermutationModel.sufCmaScheme.winningCondition run.2 run.1 && verified)

/-- **The grind-only read game**: `gameReadsWith` with the signer `signAtR`, which reads only the
counter searches' trials and takes the other values of a signature from `v`. -/
noncomputable def gameReadsT (pub : Pub) (v : (s : HPos) → XD s) (A : SAdversary) :
    QComp (hwReadSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsWith pub.perm 0 (signAtR pub v) (pkD pub v) A

end reads

/-! ## Dropping the program calls -/

section drops

variable (W : Hw X Z)

theorem dropsTo_progPortsD (v : (s : HPos) → XD s) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec X Z Unit) B C α} {y : QComp (hwReadSpec X Z Unit) B C α}
    (hx : DropsTo W x y) :
    ∀ ps : List (LazyProg X Z HPos XD), (∀ p ∈ ps, ProgOf W (p.realize v)) →
      DropsTo W ((progPortsD v B ps).bind fun _ ↦ x) y
  | [], _ => hx
  | p :: ps, h => by
    rw [progPortsD, QuantumComp₂.bind_assoc]
    exact DropsTo.progCall_bind _ (h p List.mem_cons_self)
      (dropsTo_progPortsD v B hx ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

theorem dropsTo_progSlotsD (pub : Pub) (v : (s : HPos) → XD s) (B : QReg) {C : QReg} {α : Type}
    {x : QComp (hwSpec X Z Unit) B C α} {y : QComp (hwReadSpec X Z Unit) B C α}
    (hx : DropsTo W x y) :
    ∀ ss : List Slot, (∀ s ∈ ss, ∀ p ∈ slotPorts pub s, ProgOf W (p.realize v)) →
      DropsTo W ((progSlotsD pub v B ss).bind fun _ ↦ x) y
  | [], _ => hx
  | s :: ss, h => by
    rw [progSlotsD, QuantumComp₂.bind_assoc]
    exact dropsTo_progPortsD W v B
      (dropsTo_progSlotsD pub v B hx ss fun t ht ↦ h t (List.mem_cons_of_mem _ ht)) _
      (h s List.mem_cons_self)

/-- **Every program port the game calls at `pub`, `v` programs a cell of `W` with its `W`
value**: those of the in-table slots and of the `H_msg` calls at `msgPol`. -/
def ProgsOf (pub : Pub) (v : (s : HPos) → XD s) : Prop :=
  (∀ s, InTable s → ∀ p ∈ slotPorts pub s, ProgOf W (p.realize v)) ∧
    ∀ msg i, ∀ p ∈ hmsgPorts pub msgPol ∅ msg i, ProgOf W (p.realize v)

variable {W} {pub : Pub} {v : (s : HPos) → XD s}

theorem dropsTo_signLayerD (h : ProgsOf W pub v) (B : QReg) {K : Key} (hK : KeyIn K) :
    DropsTo W (signLayerD pub v B K) (signLayerR pub v B K) := by
  refine DropsTo.bind₂ (dropsTo_liftReadProg W _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact DropsTo.pure _
  · exact dropsTo_progSlotsD W pub v B (DropsTo.pure _) _ fun s hs ↦
      h.1 s (inTable_of_mem_layerSlots hK hs)

theorem dropsTo_signD (h : ProgsOf W pub v) (B : QReg) (msg : Message) :
    DropsTo W (signD pub v B msg) (signR pub v B msg) := by
  unfold signD signR signRAt
  refine dropsTo_progPortsD W v B ?_ _ fun p hp ↦ ?_
  · refine DropsTo.bind₂ (dropsTo_progSlotsD W pub v B (DropsTo.pure _) _ fun s hs ↦
      h.1 s (inTable_of_mem_forsSlots hs)) fun fo ↦ ?_
    refine DropsTo.bind₂ (dropsTo_signLayerD h B (keyIn_keyOf 0 _)) fun s₀ ↦ ?_
    rcases s₀ with _ | bottom
    · exact DropsTo.pure _
    refine DropsTo.bind₂ (dropsTo_signLayerD h B (keyIn_keyOf 1 _)) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact DropsTo.pure _
    refine DropsTo.bind₂ (dropsTo_signLayerD h B (keyIn_keyOf 2 _)) fun s₂ ↦ ?_
    rcases s₂ with _ | top
    · exact DropsTo.pure _
    · exact DropsTo.pure _
  · rcases List.mem_append.mp hp with hp | hp
    · exact h.2 msg 0 p hp
    · exact h.2 msg 1 p hp

theorem dropsTo_challengeD (h : ProgsOf W pub v) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DropsTo W (challengeD pub v A c) (challengeWith pub.perm 0 (signAtR pub v) A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact dropsTo_liftReadProg W _
  · exact dropsTo_liftReadProg W _
  · refine DropsTo.bind ?_ fun _ _ ↦ DropsTo.pure _
    rw [signAtD, signAtR, QComp.act_bind, QComp.act_bind]
    exact DropsTo.prim _ fun _ ↦ dropsTo_signD h _ msg

/-- **The realized game with its reveals dropped is the grind-only read game with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_gameD (h : ProgsOf W pub v) (A : SAdversary) :
    DropsTo W (gameD pub v A) (gameReadsT pub v A) :=
  DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeD h) _) fun _ ↦
    DropsTo.bind₂ (dropsTo_liftReadProg W _) fun _ ↦ DropsTo.pure _

theorem ProgsOf.mono {W' : Hw X Z} (hW : Quantum.Xmss.Assembly.HwLe W W') (h : ProgsOf W pub v) :
    ProgsOf W' pub v :=
  ⟨fun s hs p hp ↦ Quantum.Xmss.Assembly.progOf_mono hW (h.1 s hs p hp),
    fun msg i p hp ↦ Quantum.Xmss.Assembly.progOf_mono hW (h.2 msg i p hp)⟩

end drops

/-! ## At a table, the game programs cells of the full table -/

section full

/-- **The cells of round `j` of a hash are read by it**, with their key values. -/
theorem round_mem_inputReads (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (input : HashInput)
    {j : ℕ} (hj : j < (blocks input).length) :
    SpongeRead.k (rnK π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)
        (t.2.1 (rnK π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)) ∈
          inputReads t π input ∧
      SpongeRead.k' (rnR π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)
        (t.2.2 (rnR π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)) ∈
          inputReads t π input ∧
      SpongeRead.h (rnZ π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)
        (t.1 (rnZ π t.1 t.2.1 t.2.2 (fun i ↦ (blocks input).getD i 0) j)) ∈
          inputReads t π input := by
  have h := Quantum.Xmss.Assembly.roundReads_subset_spongeReads π t.1 t.2.1 t.2.2 (blocks input) hj
  rw [absorb_take_eq_rnSt π t.1 t.2.1 t.2.2 _ j hj.le] at h
  exact ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self),
    h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

variable (L : HonestTable)

/-- **The cells of an honest path are in the full table** with their programmed values, if the
final correction vanishes at the public `h` value. -/
theorem progOf_pathCells_full {s : Slot}
    (hs : InTable s ∨ ∃ msg i, s = .hmsg (L.randomizer msg) msg i) (cor : X → X → X) {n : ℕ}
    (hn : n ≤ (blocks (slotInput L.publicSeed s (valuePos L))).length)
    (hcor : cor (rnR L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
        (n - 1)) (L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2
          (slotBlk L.publicSeed s (valuePos L)) (n - 1))) =
      L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
        (n - 1))) :
    ∀ c ∈ pathCells (pubOf L) (slotBlk L.publicSeed s (valuePos L)) cor n,
      ProgOf (fullHw L) c := by
  intro c hc
  simp only [pathCells, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hc
  · exact readsT_full L hs (round_mem_inputReads L.keys L.perm _ (by omega)).1
  · exact readsT_full L hs (round_mem_inputReads L.keys L.perm _ (by omega)).2.1
  · have hr := readsT_full L hs (round_mem_inputReads L.keys L.perm _ (j := j) (by omega)).2.2
    show (fullHw L).1 (cellH (pubOf L) _ (n - 1) cor j).1 = some (cellH (pubOf L) _ (n - 1) cor j).2
    rw [cellH_fst, cellH_snd]
    split_ifs with hjl
    · subst hjl
      exact hr.trans (congrArg some hcor.symm)
    · exact hr

/-- **The digest of an in-table slot's honest path is the value at its output.** -/
theorem valuePos_slotOutPos_eq {s : Slot} (hs : InTable s) :
    valuePos L (slotOutPos s) =
      trunc128 (rnR L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
          (nBlk L.publicSeed s - 1) +
        L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
          (nBlk L.publicSeed s - 1))) := by
  have ht := L.target_eq_some hs
  rw [HonestTable.target, L.honestInput_eq_slotInput hs, Option.map_some] at ht
  exact (Option.some.inj ht).symm.trans (trunc128_spongeHash_slot (tabW L) L.keys.1 s (valuePos L))

/-- At an in-table slot's honest path the correction of the final `h` value vanishes. -/
theorem cor128_honest {s : Slot} (hs : InTable s) :
    cor128 (valuePos L (slotOutPos s))
        (rnR L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
          (nBlk L.publicSeed s - 1))
        (L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
          (nBlk L.publicSeed s - 1))) =
      L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (slotBlk L.publicSeed s (valuePos L))
        (nBlk L.publicSeed s - 1)) := by
  rw [valuePos_slotOutPos_eq L hs]
  exact sphFix_cor_dig _ _

/-- **The output of an `H_msg` call's honest one-block path is the table's.** -/
theorem out256_hmsg (msg : Message) (i : DigestCall) :
    out256 (rnR L.perm L.keys.1 L.keys.2.1 L.keys.2.2
        (slotBlk L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)) 0 +
      L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2
        (slotBlk L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)) 0)) =
      L.digestOutput msg i := by
  have hl := length_blocks_hmsg L.publicSeed (L.randomizer msg) msg i (valuePos L)
  have e := absorb_take_eq_rnSt L.perm L.keys.1 L.keys.2.1 L.keys.2.2
    (blocks (slotInput L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L))) 1 hl.ge
  rw [List.take_of_length_le hl.le] at e
  have hs : slotInput L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L) =
      messageDigestInput (L.randomizer msg) L.publicSeed L.root msg i := by
    rw [← valuePos_rootPos L]
    rfl
  rw [HonestTable.digestOutput, ← hs]
  exact (congrArg (fun p : X × Z ↦ out256 p.1) e).symm

theorem embed256_xor_self (y : HashOutput) : embed256 (y ^^^ y) = 0 := by
  funext j
  simp [embed256]

/-- **At a table, the game programs cells of the full table with their values.** -/
theorem progsOf_fullHw : ProgsOf (fullHw L) (pubOf L) (valueAt L) := by
  refine ⟨fun s hs p hp ↦ ?_, fun msg i p hp ↦ ?_⟩
  · have hc := List.mem_map_of_mem (f := LazyProg.realize (valueAt L)) hp
    rw [realize_slotPorts (pubOf L) hs (valueAt L)] at hc
    exact progOf_pathCells_full L (Or.inl hs) _ (length_blocks_slotInput _ _ _).ge
      (cor128_honest L hs) _ hc
  · have hc := List.mem_map_of_mem (f := LazyProg.realize (valueAt L)) hp
    rw [realize_hmsgPorts (pubOf L) msgPol ∅ msg i (valueAt L)] at hc
    have hcor : cor256 (L.digestOutput msg i)
        (rnR L.perm L.keys.1 L.keys.2.1 L.keys.2.2
          (slotBlk L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)) 0)
        (L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2
          (slotBlk L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)) 0)) =
        L.keys.1 (rnZ L.perm L.keys.1 L.keys.2.1 L.keys.2.2
          (slotBlk L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)) 0) := by
      rw [cor256, ← out256_hmsg L msg i, embed256_xor_self, add_zero]
    exact progOf_pathCells_full L (Or.inr ⟨msg, i, rfl⟩) _
      (length_blocks_hmsg _ _ _ _ _).ge hcor _ hc

end full

/-! ## The grind-only game reads neither the keys nor the hidden values off the full table -/

section congr

theorem grindK_keys (P : PublicParameter) (π : Equiv.Perm (X × Z)) (t t' : SpongeKeys X Z)
    (B : QReg) (K : Key) (m : Digest) :
    ∀ n c, grindK Unit (keepUpd Unit) ⟨P, π, t⟩ B K m n c =
      grindK Unit (keepUpd Unit) ⟨P, π, t'⟩ B K m n c
  | 0, _ => rfl
  | n + 1, c => by
    rw [grindK, grindK]
    simp only [grindK_keys P π t t' B K m n, trialInput]

/-- **The grind-only game does not read the public keys.** -/
theorem gameReadsT_keys (P : PublicParameter) (π : Equiv.Perm (X × Z)) (t t' : SpongeKeys X Z)
    (v : (s : HPos) → XD s) (A : SAdversary) :
    gameReadsT ⟨P, π, t⟩ v A = gameReadsT ⟨P, π, t'⟩ v A := by
  have h : ∀ B K, signLayerR ⟨P, π, t⟩ v B K = signLayerR ⟨P, π, t'⟩ v B K := fun B K ↦ by
    rw [signLayerR, signLayerR, grindK_keys P π t t']
  unfold gameReadsT signAtR signR signRAt
  simp only [pkD, pkOf, h]

variable {v v' : (s : HPos) → XD s} (hv : ∀ s, FullCoord s → v s = v' s)
include hv

theorem restrictTo_full {T : Finset HPos} (hT : ∀ s ∈ T, FullCoord s) :
    restrictTo T v = restrictTo T v' :=
  restrictTo_eq fun s hs ↦ hv s (hT s hs)

theorem signLayerR_congr (pub : Pub) (B : QReg) {K : Key} (hK : KeyIn K) :
    signLayerR pub v B K = signLayerR pub v' B K := by
  have h1 : keyMsgOf v K = keyMsgOf v' K := by
    unfold keyMsgOf
    rw [restrictTo_full hv fun s hs ↦ by
      rw [Finset.mem_singleton.mp hs]
      exact fullPos_msgPos hK]
  have h2 : ∀ c x, layerSigOf v K c x = layerSigOf v' K c x := fun c x ↦ by
    unfold layerSigOf
    rw [restrictTo_full hv fun _ ↦ fullCoord_valSet fun q hq ↦
      fullPos_layerNeed (l := K.1) (τ := K.2.1) (e := K.2.2) hK hq]
  simp only [signLayerR, h1, h2]

theorem signR_congr (pub : Pub) (B : QReg) (msg : Message) :
    signR pub v B msg = signR pub v' B msg := by
  have hd : dgOf v msg = dgOf v' msg := by
    unfold dgOf
    rw [restrictTo_full hv fun s hs ↦ by
      simp only [DigestPolicy.need, msgPol, Finset.mem_insert, Finset.notMem_empty,
        or_false] at hs
      rcases hs with rfl | rfl <;> trivial]
  have hr : rndD v msg = rndD v' msg := by
    unfold rndD
    rw [restrictTo_full hv fun s hs ↦ by
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact fullPos_rootPos
      · rw [Finset.mem_singleton.mp hs]
        trivial]
  have hf : ∀ idx lv, forsOf v idx lv = forsOf v' idx lv := fun idx lv ↦ by
    unfold forsOf
    rw [restrictTo_full hv fun _ ↦ fullCoord_valSet fun _ ↦ fullPos_forsNeed _]
  have hl : ∀ l idx, signLayerR pub v B (keyOf l idx) = signLayerR pub v' B (keyOf l idx) :=
    fun l idx ↦ signLayerR_congr hv pub B (keyIn_keyOf l idx)
  rw [signR, signR, hd]
  simp only [signRAt, hr, hf, hl]

/-- **The grind-only game reads the hidden values only on the full coordinates.** -/
theorem gameReadsT_congr (pub : Pub) (A : SAdversary) :
    gameReadsT pub v A = gameReadsT pub v' A := by
  have hp : pkD pub v = pkD pub v' := by
    unfold pkD
    rw [restrictTo_full hv fun s hs ↦ by
      rw [Finset.mem_singleton.mp hs]
      exact fullPos_rootPos]
  unfold gameReadsT signAtR
  simp only [hp, signR_congr hv pub]

end congr

/-! ## The grind-only game against the honest functions -/

section honest

variable (L : HonestTable) {B : QReg}

theorem readsTo_hashTrial (input : HashInput) :
    ReadsTo L.keys (hwEmpty X Z) () (hashTrial Unit (fun _ _ ↦ keepMem) L.perm B input)
      (L.hash input) := by
  have h := ((readsToS_readsImpl (t := L.keys) (W := hwEmpty X Z) (m := ()) (B := B) (M := Unit)
    L.perm input) []).map Prod.fst
  rw [overwrite_hwEmpty, readHash_eq_traceImpl] at h
  exact h

/-- **The counter search through read ports returns the table's selection.** -/
theorem readsTo_grindK (K : Key) (m : Digest) : ∀ n c,
    ReadsTo L.keys (hwEmpty X Z) () (grindK Unit (keepUpd Unit) (pubOf L) B K m n c)
      (L.selectFrom K.1 K.2.1 K.2.2 m n c)
  | 0, _ => readsTo_pure _
  | n + 1, c => by
    rw [grindK]
    refine (readsTo_hashTrial L _).bind ?_
    have he : L.encDigest K.1 K.2.1 K.2.2 m (BitVec.ofNat counterBits c) =
        truncateHash (L.hash (trialInput (pubOf L) K m c)) := rfl
    rw [HonestTable.selectFrom, he]
    cases TargetSum.decodeDigest (truncateHash (L.hash (trialInput (pubOf L) K m c))) with
    | none => exact readsTo_grindK K m n (c + 1)
    | some x => exact readsTo_pure _

theorem cpos_mem_layerNeed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding)
    (i : ChainIndex) : cpos l τ e i (x i).val ∈ layerNeed l τ e x :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun i ↦ cpos l τ e i (x i).val) (Finset.mem_univ i)))

theorem siblingPos_mem_layerNeed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding)
    (z : Fin (layerHeight l)) : siblingPos l τ e z ∈ layerNeed l τ e x :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (siblingPos l τ e) (Finset.mem_univ z))

/-- **A layer signature from the revealed values is the table's.** -/
theorem layerSigOf_valueAt {K : Key} (hK : KeyIn K) (c : EncodingCounter) (x : Encoding) :
    layerSigOf (valueAt L) K c x =
      ⟨c, fun i ↦ L.chainValue K.1 K.2.1 K.2.2 i (x i).val, L.authPath K.1 K.2.1 K.2.2⟩ := by
  have hc : ∀ i, extendVals (restrictTo (valSet (layerNeed K.1 K.2.1 K.2.2 x)) (valueAt L))
      (cpos K.1 K.2.1 K.2.2 i (x i).val) = L.chainValue K.1 K.2.1 K.2.2 i (x i).val := fun i ↦ by
    rw [extendVals_restrictTo (val_mem_valSet.mpr (cpos_mem_layerNeed _ _ _ x i))]
    exact valuePos_cpos L _ _ _ i (x i).isLt
  have hs : ∀ z, extendVals (restrictTo (valSet (layerNeed K.1 K.2.1 K.2.2 x)) (valueAt L))
      (siblingPos K.1 K.2.1 K.2.2 z) = L.authPath K.1 K.2.1 K.2.2 z := fun z ↦ by
    rw [extendVals_restrictTo (val_mem_valSet.mpr (siblingPos_mem_layerNeed _ _ _ x z))]
    have h10 := layerHeight_le K.1
    have htop : layerHeight topLayer = 10 := rfl
    have hz := z.isLt
    exact valuePos_tpos L _ _ (by omega) (lt_of_lt_of_le
      (lt_two_pow_of_lt (shiftRight_xor_lt hK.2 z.isLt)) (two_pow_layerHeight_le K.1))
  unfold layerSigOf
  simp only [hc, hs]

theorem forsNeed_eq (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsNeed idx lv = needUnion (forsSlots idx lv) ∪
      Finset.univ.image (fun κ ↦ ValPos.forsSecret idx κ (lv κ)) ∪
      Finset.univ.image
        (fun p : ForsTreeIndex × Fin forsTreeHeight ↦ forsSibPos idx lv p.1 p.2) := by
  rw [forsNeed]

/-- **A FORS opening from the revealed values is the table's.** -/
theorem forsOf_valueAt (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsOf (valueAt L) idx lv = L.forsOpening idx lv := by
  funext κ
  have h1 : extendVals (restrictTo (valSet (forsNeed idx lv)) (valueAt L))
      (.forsSecret idx κ (lv κ)) = L.forsSecret idx κ (lv κ) := by
    rw [forsNeed_eq]
    exact extendVals_restrictTo (val_mem_valSet.mpr (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ κ))))) _
  have h2 : ∀ z : Fin forsTreeHeight,
      extendVals (restrictTo (valSet (forsNeed idx lv)) (valueAt L))
      (forsSibPos idx lv κ z) = L.forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1) := by
    intro z
    rw [forsNeed_eq]
    refine (extendVals_restrictTo (val_mem_valSet.mpr (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : ForsTreeIndex × Fin forsTreeHeight ↦
        forsSibPos idx lv p.1 p.2) (Finset.mem_univ (κ, z))))) _).trans ?_
    exact valuePos_fpos L idx κ z.isLt.le
      (lt_two_pow_of_lt (shiftRight_xor_lt (lv κ).isLt z.isLt))
  exact congrArg₂ ForsTreeOpening.mk h1 (funext h2)

/-- The digest from the revealed `H_msg` outputs is the table's. -/
theorem dgOf_valueAt (msg : Message) : dgOf (valueAt L) msg = L.messageDigest msg := by
  unfold dgOf digestOf
  refine congrArg truncateMessageDigest (funext fun i ↦ ?_)
  rw [extendOut_restrictTo (msgPol.out_mem_need ∅ msg i)]
  rfl

theorem rndD_valueAt (msg : Message) : rndD (valueAt L) msg = L.randomizer msg :=
  extendRnd_restrictTo (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) _

/-- The public key the game reveals at `L` is `L`'s. -/
theorem pkD_pubOf : pkD (pubOf L) (valueAt L) = L.publicKey := by
  unfold pkD pkOf
  rw [extendVals_restrictTo (Finset.mem_singleton_self _)]
  show (⟨L.publicSeed, valuePos L rootPos⟩ : PublicKey) = ⟨L.publicSeed, L.root⟩
  rw [valuePos_rootPos]

theorem readsTo_signLayerR {K : Key} (hK : KeyIn K) :
    ReadsTo L.keys (hwEmpty X Z) () (signLayerR (pubOf L) (valueAt L) B K)
      (L.layerSignature K.1 K.2.1 K.2.2 (valuePos L (msgPos K))) := by
  have hm : keyMsgOf (valueAt L) K = valuePos L (msgPos K) :=
    extendVals_restrictTo (Finset.mem_singleton_self _) _
  rw [signLayerR, hm]
  refine (readsTo_grindK L K _ _ _).bind ?_
  rw [HonestTable.layerSignature, HonestTable.select]
  rcases L.selectFrom K.1 K.2.1 K.2.2 (valuePos L (msgPos K)) encodingAttemptLimit 0 with
    _ | ⟨c, x⟩
  · exact readsTo_pure _
  · show ReadsTo _ _ _ (QuantumComp₂.pure (some (layerSigOf (valueAt L) K c x))) _
    rw [layerSigOf_valueAt L hK]
    exact readsTo_pure _

/-- **The layer signature of `K_l(idx)` is the table's.** -/
theorem readsTo_signLayerR_keyOf (l : Layer) (idx : Index) :
    ReadsTo L.keys (hwEmpty X Z) () (signLayerR (pubOf L) (valueAt L) B (keyOf l idx))
      (L.layerSig idx l) := by
  rw [HonestTable.layerSig_eq]
  exact readsTo_signLayerR L (keyIn_keyOf l idx)

/-- **The grind-only signer returns the table's signature** against the honest functions. -/
theorem readsTo_signR (msg : Message) :
    ReadsTo L.keys (hwEmpty X Z) () (signR (pubOf L) (valueAt L) B msg) (L.signature msg) := by
  have hi : L.index msg = digestIndex (dgOf (valueAt L) msg) := by
    rw [dgOf_valueAt]
    rfl
  have hv : L.leaves msg = digestForsLeaves (dgOf (valueAt L) msg) := by
    rw [dgOf_valueAt]
    rfl
  have hf : L.forsOpening (L.index msg) (L.leaves msg) =
      forsOf (valueAt L) (digestIndex (dgOf (valueAt L) msg))
        (digestForsLeaves (dgOf (valueAt L) msg)) := by
    rw [hi, hv, forsOf_valueAt]
  unfold HonestTable.signature
  rw [hf, ← rndD_valueAt L msg, hi]
  unfold signR signRAt
  refine (readsTo_pure _).bind ?_
  refine (readsTo_signLayerR_keyOf L 0 _).bind ?_
  rcases L.layerSig (digestIndex (dgOf (valueAt L) msg)) 0 with _ | bottom
  · exact readsTo_pure _
  refine (readsTo_signLayerR_keyOf L 1 _).bind ?_
  rcases L.layerSig (digestIndex (dgOf (valueAt L) msg)) 1 with _ | middle
  · exact readsTo_pure _
  refine (readsTo_signLayerR_keyOf L 2 _).bind ?_
  rcases L.layerSig (digestIndex (dgOf (valueAt L) msg)) 2 with _ | top
  · exact readsTo_pure _
  · exact readsTo_pure _

variable (A : SAdversary)

/-- `challengeReads` is `challengeWith` with the signer `signReads`. -/
theorem challengeReads_eq (π : Equiv.Perm (X × Z)) (sk : SecretKey) :
    challengeReads Unit π RandomPermutationModel.sufCmaScheme schemeWithHash sk =
      challengeWith π sk (fun msg E _ ℓ ↦ signReads Unit π schemeWithHash sk msg E ℓ) := by
  funext A c
  rcases c with o | ⟨p | msg, E, ℓ⟩ <;> rfl

/-- The challenger's local operations and permutation calls do not read the secret key. -/
theorem challengeWith_sk (π : Equiv.Perm (X × Z)) (sk sk' : SecretKey)
    (sgn : ∀ (msg : Message) (E : QReg) {A : QReg}, (A ≃ sAdvSpec.In (.sign msg) × E) →
      QComp (hwReadSpec X Z Unit) A (QReg.of (sAdvSpec.Out (.sign msg) × E)) (Option Signature)) :
    challengeWith π sk sgn = challengeWith π sk' sgn := by
  funext A c
  rcases c with o | ⟨p | msg, E, ℓ⟩ <;> rfl

/-- **`gameReads` after the honest key generation of `L`** is `gameReadsWith` at `L`'s keys with
the signer `signReads`. -/
theorem gameReads_honest :
    gameReads Unit L.perm RandomPermutationModel.sufCmaScheme schemeWithHash A
        (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed)) =
      gameReadsWith L.perm L.secretSeed
        (fun msg E _ ℓ ↦ signReads Unit L.perm schemeWithHash L.secretSeed msg E ℓ)
        L.publicKey A := by
  rw [gameReads, challengedReads, L.fst_honestEval_keygen, challengeReads_eq]
  rfl

/-- **`gameReadsT` at `L`** is `gameReadsWith` at `L`'s keys with the grind-only signer. -/
theorem gameReadsT_pubOf :
    gameReadsT (pubOf L) (valueAt L) A =
      gameReadsWith L.perm L.secretSeed (signAtR (pubOf L) (valueAt L)) L.publicKey A := by
  rw [gameReadsT, pkD_pubOf, gameReadsWith, gameReadsWith,
    challengeWith_sk _ 0 L.secretSeed]
  rfl

theorem intertwines_classicalOn_readsTo_empty {B : QReg} {α : Type}
    {x₁ : QComp (qrpmSpec (X × Z)) B B α} {x₂ : QComp (hwReadSpec X Z Unit) B B α} {a : α}
    (h₁ : ClassicalOn (permutationRuntime (spongePerm L.keys L.perm)) x₁ (pure a) LinearMap.id)
    (h₂ : ReadsTo L.keys (hwEmpty X Z) () x₂ a) :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) ()).amplifyLeft B)
      (fun _ ↦ (hwAt (hwEmpty X Z) ()).amplifyLeft B)
      ((permutationRuntime (spongePerm L.keys L.perm)).run₂ .instruments x₁)
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).run₂ .instruments x₂) := by
  have h := intertwines_of_classicalOn_readsTo L.keys (hwEmpty X Z) () L.perm
    (by rw [overwrite_hwEmpty]; exact h₁) h₂
  rw [overwrite_hwEmpty] at h
  exact h

/-- **The challenger with the grind-only signer intertwines with the challenger** against the
honest functions of `L`. -/
theorem intertwines_challengeR (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) ()).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).src A c b = u} ↦
          (hwAt (hwEmpty X Z) ()).amplifyLeft p.1)
      ((permutationRuntime (spongePerm L.keys L.perm)).run .instruments
        (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv L.secretSeed A c))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).run .instruments
        (challengeWith L.perm L.secretSeed (signAtR (pubOf L) (valueAt L)) A c)) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · have h := intertwines_simulate L.perm L.keys (hwEmpty X Z) ()
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv L.secretSeed A (.prim o))
    rw [overwrite_hwEmpty] at h
    exact h
  · have h := intertwines_simulate L.perm L.keys (hwEmpty X Z) ()
      (challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv L.secretSeed A
        (.query (.perm p) E ℓ))
    rw [overwrite_hwEmpty] at h
    exact h
  · change DSubInstrument.Intertwines _ _
      ((permutationRuntime (spongePerm L.keys L.perm)).run .instruments
        (QuantumComp.bind (signTree RandomPermutationModel.sufCmaScheme keccakStateEquiv
          L.secretSeed msg E ℓ) _))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).run .instruments
        (QuantumComp.bind (signAtR (pubOf L) (valueAt L) msg E ℓ) _))
    refine intertwines_run_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
      (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ())
      (intertwines_run_of_run₂ (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ()) ?_)
      fun p ↦ ?_
    · rw [signTree, signAtR]
      refine intertwines_run₂_act_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ())
        (A := A) (B := QReg.of (sAdvSpec.Out (.sign msg) × E)) _ fun _ ↦ ?_
      exact intertwines_classicalOn_readsTo_empty L
        ((classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
          (L.simulateQ_sign_eq _ (fun _ ↦ rfl) msg) rfl) (readsTo_signR L msg)
    · exact intertwines_run_pure (R₁ := permutationRuntime (spongePerm L.keys L.perm))
        (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ()) _

/-- **The game and its grind-only reads intertwine** against the honest functions of `L`. -/
theorem intertwines_game_gameReadsT :
    DSubInstrument.Intertwines ((hwAt (hwEmpty X Z) ()).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt (hwEmpty X Z) ()).amplifyLeft (QReg.of Unit))
      ((permutationRuntime (spongePerm L.keys L.perm)).run₂ .instruments
        (game RandomPermutationModel.sufCmaScheme keccakStateEquiv L.secretSeed A))
      ((spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).run₂ .instruments
        (gameReadsT (pubOf L) (valueAt L) A)) := by
  rw [gameReadsT_pubOf, game, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
      (L.simulateQ_generateKeys_eq _ (fun _ ↦ rfl)) rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ())
    (intertwines_run₂_of_run (intertwines_substitute (spec₀ := sAdvSpec)
      (R₁ := permutationRuntime (spongePerm L.keys L.perm))
      (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ())
      (fun A c ↦ intertwines_challengeR L A c) _))
    fun run ↦ ?_
  refine intertwines_run₂_bind (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (V := hwAt (hwEmpty X Z) ())
    (intertwines_classicalOn_readsTo_empty L ?_
      ((readsTo_readsProgram_hwEmpty L.perm (schemeWithHash.verify _ run.1)).map Prod.fst))
    fun _ ↦ intertwines_run₂_pure _
  exact (classicalOn_toQuantumAt_permImpl L.keys L.perm _ _).congr
    (Quantum.Sphincs.simulateQ_verify L.keys L.perm _ (fun _ ↦ rfl) _ run.1) rfl

/-- **G1 → G2 with the grind-only signer**: against `φ = spongePerm L.keys L.perm`, the game at
`L`'s secret seed has the law of `gameReadsT` at `pubOf L`, `valueAt L` against the honest
functions `L.keys` read through read ports. -/
theorem evalDistMap_game_eq_gameReadsT (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (permutationRuntime (spongePerm L.keys L.perm)).evalDistMap .instruments
        (game RandomPermutationModel.sufCmaScheme keccakStateEquiv L.secretSeed A) ρ f =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReadsT (pubOf L) (valueAt L) A) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := permutationRuntime (spongePerm L.keys L.perm))
    (R₂ := spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()) (K := hwCol (hwEmpty X Z) ())
    (conjTranspose_hwCol_mul_self _ ()) (hwAt_basis _ ())
    (intertwines_run_of_run₂ (intertwines_game_gameReadsT L A)) ρ f

/-- **The two read programs have the same law against the honest functions**: `gameReads` after
the honest key generation of `L` and `gameReadsT` at `L`. -/
theorem evalDistMap_gameReads_eq_gameReadsT (ρ : SubState (QReg.of Unit)) {γ : Type*}
    [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReads Unit L.perm RandomPermutationModel.sufCmaScheme schemeWithHash A
          (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed))) ρ f =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReadsT (pubOf L) (valueAt L) A) ρ f := by
  have h := evalDistMap_game_eq_reads L.keys (hwEmpty X Z) () L.perm
    RandomPermutationModel.sufCmaScheme schemeWithHash overPermutation_schemeWithHash.symm
    L.secretSeed A ρ f
  rw [overwrite_hwEmpty] at h
  exact h.symm.trans (evalDistMap_game_eq_gameReadsT L A ρ f)

end honest

/-- **FullTable's contract for the grind-only game**: it does not read the public keys, reads the
hidden values only on the full coordinates, and against the honest functions has the law of
`gameReads` after honest key generation. -/
theorem fullReads_gameReadsT (A : SAdversary) : FullReads A fun pub v ↦ gameReadsT pub v A where
  keys seed π t t' v := gameReadsT_keys seed π t t' v A
  full _ _ _ h := gameReadsT_congr h _ A
  reads L := evalDistMap_gameReads_eq_gameReadsT L A _ _

end Quantum.Sphincs.Assembly

end
