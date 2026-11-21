module

public import Quantum.StdModel.Qrom.SphincsItsrRt1Tab

@[expose] public section

/-!
# B3's ITSR template game in runtime 1, as a read program

Runtime 1 with record ports, with the cells of `hwI θ` hardwired, running the realized ITSR
template game `gameIQ msgPol A θ` (any inner memory and trial update in the drops), has the law of
the average over the functions `t` of runtime 1's classical reads running the read program
`gameReadsI θ A`; against each `t`, that program intertwines with a program of the random oracle
(`gameL`) whose signer returns the table's signatures purely.

* **Records and programs** (`dropRec_gameIT`, `dropsTo_gameDI`): as `Quantum.Qrom.Sphincs.GameT`
  for the challenge prefix; the data of the signed messages (`foldT`) drops to program calls of
  the digest cells (`foldD`), then to the data read from the revealed values (`datumD`).
* **The pure signer** (`sigSch`, `gameL`): the adversary against the challenger whose signer
  returns `sigs M`, the data `dat` of the signed messages, the forgery's digest by hash calls and
  the ITSR decision of the template. `evalDistMap_gameL_eq`: against the regrouped function
  `regroup hmsgRoute (overwrite W t).1`, with the table's signatures, public key and data, it has
  the law of `gameReadsI θ A` against runtime 1's classical reads of `t`.
* `evalDistMap_runtime1R_gameIQ`: runtime 1 with record ports on `gameIQ msgPol A θ`, the cells of
  `hwI θ` hardwired, runs as the hardwired read runtime on `gameReadsI θ A`.
-/

open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open OracleComp OracleSpec

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Qrom.Sphincs
open Quantum.Qrom (regroup)
open Quantum.Sponge (Hw hwSpec hwReadSpec spongeFnReadRuntime spongeHardwiredReadRuntime overwrite
  hwAt hwCol hwAt_basis conjTranspose_hwCol_mul_self intertwines_run_pure intertwines_run₂_pure
  intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂ intertwines_run₂_of_run
  intertwines_run_bind intertwines_substitute evalDistMap_eq_of_intertwines
  read_port_eq_classical_read)
open Quantum.Xmss.Assembly (runtime1R realizeT realizeT_bind₂ DropRec liftReadC
  dropRec_realizeT_substitute evalDistMap_runtime1R_eq DropsTo progCall dropsTo_liftReadProg
  dropsTo_substitute evalDistMap_runtime1_eq_spongeHardwiredReadRuntime)
open Quantum.Qrom.Xmss (not_isHash_inl)

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/-! ## Dropping the reveals and the record calls -/

section drops

variable (θ : TVals)

/-- A signed message's ITSR datum read from the revealed values. -/
noncomputable def datumD (msg : Message) : ItsrDatum :=
  (msg, (sigTabD θ msg).randomizer msg, dgD θ msg)

/-- **The data of the signed messages, with the reveals dropped**: the program calls of the digest
cells, then the data read from the revealed values. -/
noncomputable def foldD (B : QReg) :
    List Message → QComp (hwSpec PairOut Qrom.HashDomain Unit) B B (List ItsrDatum)
  | [] => QuantumComp₂.pure []
  | msg :: ms => (progCall ((digPort msgPol ∅ msg).realize θ) B).bind fun _ ↦
      (foldD B ms).bind fun ds ↦ QuantumComp₂.pure (datumD θ msg :: ds)

/-- The forgery's digest through read ports, then the ITSR decision of the template. -/
noncomputable def tailR (y : PreI) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  readsThenR Unit (LeanSphincsOver.messageDigest Qrom.hashQ y.1 y.2.1.1.signature.randomizer
    y.2.1.1.message) fun dF ↦ itsrDecT y.2.1.2.length y.2.1.1 y.2.2 dF

/-- **The challenge prefix with the data, with the reveals dropped.** -/
noncomputable def prefixDI (A : SAdversary) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) PreI :=
  (QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeD θ)
      (Quantum.Qrom.SufCma.withSignLog (A (pkD θ)))) fun run ↦
        QuantumComp₂.pure (pkD θ, run)).bind fun x ↦
    (foldD θ (QReg.of Unit) (logMsgsT x.2.2)).bind fun ds ↦ QuantumComp₂.pure (x.1, x.2, ds)

/-- **The realized ITSR game with its reveals dropped** (over `hwSpec`). -/
noncomputable def gameDI (A : SAdversary) :
    QComp (hwSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixDI θ A).bind fun y ↦ liftReadC (tailR y)

/-- **The ITSR read game** (over `hwReadSpec`): the adversary against `challengeR`, the data of
the signed messages from the revealed values, the forgery's digest through read ports and the
ITSR decision. -/
noncomputable def gameReadsI (A : SAdversary) :
    QComp (hwReadSpec PairOut Qrom.HashDomain Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  ((QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeR θ)
      (Quantum.Qrom.SufCma.withSignLog (A (pkD θ)))) fun run ↦
        QuantumComp₂.pure (pkD θ, run)).bind fun x ↦
    (QuantumComp₂.pure ((logMsgsT x.2.2).map (datumD θ)) :
      QComp (hwReadSpec PairOut Qrom.HashDomain Unit) _ _ _).bind fun ds ↦
        QuantumComp₂.pure (x.1, x.2, ds)).bind tailR

variable {M : Type} (upd : TrialUpd M)

theorem dropRec_foldT (B : QReg) :
    ∀ msgs, DropRec TPos (realizeT θ (foldT M msgPol B msgs)) (foldD θ B msgs)
  | [] => .pure _
  | msg :: ms => by
    rw [foldT]
    refine dropRec_revealThen θ _ _ fun _ ↦ dropRec_revealThen θ _ _ fun _ ↦ ?_
    refine dropRec_progThen θ _ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_foldT B ms) fun _ ↦ .pure _

theorem dropRec_prefixIT (A : SAdversary) :
    DropRec TPos (realizeT θ (prefixIT M upd msgPol A)) (prefixDI θ A) := by
  unfold prefixIT prefixT
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_revealThen θ _ _ fun _ ↦ ?_) fun x ↦ ?_
  · rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_realizeT_substitute θ (dropRec_challengeT upd θ) _)
      fun _ ↦ .pure _
  · rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_foldT θ _ _) fun _ ↦ .pure _

/-- **The realized ITSR game drops to `gameDI`**: with its record calls removed and its reads
keeping the memory `Unit`. -/
theorem dropRec_gameIT (A : SAdversary) :
    DropRec TPos (realizeT θ (gameIT M upd msgPol A)) (gameDI θ A) := by
  rw [gameIT_eq, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_prefixIT θ upd A) fun _ ↦ dropRec_readsThenT θ _ _

end drops

section dropsTo

variable {W : Hw PairOut Qrom.HashDomain} {θ : TVals}

theorem dropsTo_foldD (h : ProgsOfQ W θ) (B : QReg) :
    ∀ msgs, DropsTo W (foldD θ B msgs) (QuantumComp₂.pure (msgs.map (datumD θ)))
  | [] => DropsTo.pure _
  | msg :: ms => by
    rw [foldD, List.map_cons]
    refine DropsTo.progCall_bind _ (h.2 msg) ?_
    rw [show (QuantumComp₂.pure (datumD θ msg :: ms.map (datumD θ)) :
        QComp (hwReadSpec PairOut Qrom.HashDomain Unit) B B (List ItsrDatum)) =
        (QuantumComp₂.pure (ms.map (datumD θ))).bind fun ds ↦
          QuantumComp₂.pure (datumD θ msg :: ds) from (QuantumComp₂.pure_bind _ _).symm]
    exact DropsTo.bind₂ (dropsTo_foldD h B ms) fun _ ↦ DropsTo.pure _

/-- **The realized ITSR game with its reveals dropped is the ITSR read game with program calls
inserted**, when every program call hardwires a cell of `W` with its `W` value. -/
theorem dropsTo_gameDI (h : ProgsOfQ W θ) (A : SAdversary) :
    DropsTo W (gameDI θ A) (gameReadsI θ A) :=
  DropsTo.bind₂ (DropsTo.bind₂ (DropsTo.bind₂ (dropsTo_substitute W (dropsTo_challengeD h) _)
    fun _ ↦ DropsTo.pure _) fun _ ↦ DropsTo.bind₂ (dropsTo_foldD h _ _) fun _ ↦ DropsTo.pure _)
    fun _ ↦ dropsTo_liftReadProg W _

end dropsTo

/-- **Runtime 1 with record ports runs the realized ITSR game as its read program**, with the
cells of `hwI θ` hardwired. -/
theorem evalDistMap_runtime1R_gameIQ (θ : TVals) (A : SAdversary) (ρ : SubState (QReg.of Unit))
    {γ : Type*} [MeasurableSpace γ] (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (runtime1R PairOut Qrom.HashDomain (hwI θ) m0H).evalDistMap .instruments
        (gameIQ msgPol A θ) ρ f =
      (spongeHardwiredReadRuntime PairOut Qrom.HashDomain (hwI θ) ()).evalDistMap .instruments
        (gameReadsI θ A) ρ f :=
  (evalDistMap_runtime1R_eq (hwI θ) m0H (dropRec_gameIT θ cwUpd A) ρ f).trans
    (evalDistMap_runtime1_eq_spongeHardwiredReadRuntime (hwI θ) ()
      (dropsTo_gameDI (progsOf_hwI θ) A) ρ f)

/-! ## The game with a pure signer -/

/-- **A scheme whose signer returns the signatures `sk`** (no keys, no verification). -/
noncomputable def sigSch : Quantum.Qrom.SchemeOver Quantum.Qrom.RomOracles Unit Unit
    (Message → Option Signature) Message (Option Signature) Forgery where
  sampleSeed := pure ()
  generateKeys _ := pure ((), fun _ ↦ none)
  sign sk msg := pure (sk msg)
  verify _ _ := pure false
  winningCondition _ _ := false

/-- The forgery's digest by hash calls, then the ITSR decision of the template. -/
noncomputable def tailL (y : PreI) :
    QComp Quantum.Qrom.romSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((LeanSphincsOver.messageDigest Qrom.hashQ y.1 y.2.1.1.signature.randomizer
    y.2.1.1.message).toQuantumAt (Quantum.Qrom.SufCma.romImpl _)).bind fun dF ↦
      QuantumComp₂.pure (itsrDecT y.2.1.2.length y.2.1.1 y.2.2 dF)

/-- **The ITSR game with the pure signer** `sigs`, the public key `pk` and the data `dat` of the
signed messages. -/
noncomputable def gameL (sigs : Message → Option Signature) (pk : PublicKey)
    (dat : List Message → List ItsrDatum) (A : SAdversary) :
    QComp Quantum.Qrom.romSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((QuantumComp₂.bind (Quantum.Qrom.SufCma.challenged sigSch sigs
      (Quantum.Qrom.SufCma.withSignLog (A pk))) fun run ↦ QuantumComp₂.pure (pk, run)).bind fun x ↦
    (QuantumComp₂.pure (dat (logMsgsT x.2.2)) : QComp Quantum.Qrom.romSpec _ _ _).bind fun ds ↦
      QuantumComp₂.pure (x.1, x.2, ds)).bind tailL

section intertwine

variable (t : (Qrom.HashDomain → PairOut) × (PairOut → Qrom.HashDomain) ×
  (PairOut → Qrom.HashDomain)) (W : Hw PairOut Qrom.HashDomain) (θ : TVals)
  {sigs : Message → Option Signature}

/-- **The pure signer intertwines with the grind-only signer** when it returns the table's
signatures against the regrouped function. -/
theorem intertwines_challengeL
    (hs : ∀ msg, sigs msg = (tabOf θ).signature (regroup hmsgRoute (overwrite W t).1) msg)
    (A : QReg) (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DSubInstrument.Intertwines ((hwAt W ()).amplifyLeft A)
      (fun p : Σ u, {b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).B A c //
        (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).src A c b = u} ↦
          (hwAt W ()).amplifyLeft p.1)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (Quantum.Qrom.SufCma.challenge sigSch sigs A c))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W ()).run .instruments
        (challengeR θ A c)) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact intertwines_liftH t W () _
  · exact intertwines_liftH t W () _
  · change DSubInstrument.Intertwines _ _
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run .instruments
        (QuantumComp.bind (Quantum.Qrom.SufCma.signTree sigSch sigs r E ℓ) _))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W ()).run .instruments
        (QuantumComp.bind (signAtR θ r E ℓ) _))
    refine intertwines_run_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
      (intertwines_run_of_run₂ (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ()) ?_) fun p ↦ ?_
    · rw [Quantum.Qrom.SufCma.signTree, signAtR]
      refine intertwines_run₂_act_bind
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ()) (A := A)
        (B := QReg.of (sAdvSpec.Out (.sign r) × E)) _ fun _ ↦ ?_
      exact intertwines_of_classicalOn_readsTo t W ()
        ((romWorld.classicalOn_toQuantumAt (regroup hmsgRoute (overwrite W t).1) _
          (pure (sigs r))).congr ((simulateQ_pure _ _).trans (congrArg pure (hs r))) rfl)
        (readsTo_signR r)
    · exact intertwines_run_pure
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ()) _

/-- **The game with the pure signer and the ITSR read game intertwine** on the block `(W, ())`,
when the signer returns the table's signatures, the public key is the table's and the data are
read from the revealed values. -/
theorem intertwines_gameL
    (hs : ∀ msg, sigs msg = (tabOf θ).signature (regroup hmsgRoute (overwrite W t).1) msg)
    {pk : PublicKey} (hpk : pk = pkD θ) {dat : List Message → List ItsrDatum}
    (hd : ∀ msgs, dat msgs = msgs.map (datumD θ)) (A : SAdversary) :
    DSubInstrument.Intertwines ((hwAt W ()).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W ()).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (gameL sigs pk dat A))
      ((spongeFnReadRuntime PairOut Qrom.HashDomain t W ()).run₂ .instruments
        (gameReadsI θ A)) := by
  subst hpk
  unfold gameL gameReadsI
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ()) ?_ fun y ↦ ?_
  · refine intertwines_run₂_bind
      (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
      (intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
        (intertwines_run₂_of_run (intertwines_substitute (spec₀ := sAdvSpec)
          (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
          (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
          (fun A c ↦ intertwines_challengeL t W θ hs A c) _))
        fun _ ↦ intertwines_run₂_pure _) fun x ↦ ?_
    rw [hd]
    exact intertwines_run₂_bind
      (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
      (intertwines_run₂_pure _) fun _ ↦ intertwines_run₂_pure _
  · rw [tailL, tailR, readsThenR_eq]
    exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (V := hwAt W ())
      (intertwines_readsProgram not_isHash_inl _ (isHash_messageDigest _ _ _))
      fun _ ↦ intertwines_run₂_pure _

/-- **The game with the pure signer has the law of the ITSR read game** against the classical
reads of `t` with the hardwired cells `W`. -/
theorem evalDistMap_gameL_eq
    (hs : ∀ msg, sigs msg = (tabOf θ).signature (regroup hmsgRoute (overwrite W t).1) msg)
    {pk : PublicKey} (hpk : pk = pkD θ) {dat : List Message → List ItsrDatum}
    (hd : ∀ msgs, dat msgs = msgs.map (datumD θ)) (A : SAdversary)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).evalDistMap .instruments
        (gameL sigs pk dat A) ρ f =
      (spongeFnReadRuntime PairOut Qrom.HashDomain t W ()).evalDistMap .instruments
        (gameReadsI θ A) ρ f :=
  evalDistMap_eq_of_intertwines
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut Qrom.HashDomain t W ()) (K := hwCol W ())
    (conjTranspose_hwCol_mul_self W ()) (hwAt_basis W ())
    (intertwines_run_of_run₂ (intertwines_gameL t W θ hs hpk hd A)) ρ f

end intertwine

end Quantum.StdModel.Sphincs.SphItsr

end
