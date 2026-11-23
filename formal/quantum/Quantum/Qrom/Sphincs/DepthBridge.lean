module

public import Quantum.Qrom.Sphincs.DepthLift
public import Quantum.Qrom.Sphincs.Security

@[expose] public section

/-!
# leanSPHINCS's QROM game for a parallel adversary, with batched rounds

The challenger of runtime 2 answers a call of `H` by a regrouped call of `h` (`regroupEmbed`,
`h`, `regroupProject`), so the game of the serialization `SufCma.serialize A` of a parallel
adversary `A` runs each round of `H` as the interleaved round `regRoundR`
(`realizeT_challengeT_seqCalls`). The game with batched rounds `gameQB pol A θ` answers a round
by `batRoundR` instead (the template challenger `challengeTPar`), and is the serialization of a
program with rounds of `h` (`gameQB_serialize`, `prefixQB_serialize`), the game with rounds
`gameQPar`.

The two games run alike against every runtime in which the interleaved and the batched rounds
run alike (`RoundsCommute`), and have the same summed weights for every weight vanishing at port
`h` (`runTWEq_gameQ`, `runTWEq_prefixQ`).
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Par
open Quantum.Xmss.Assembly (recHwSpec recSpec realizeT realizeT_bind realizeT_bind₂ revealThen
  extCls RevealVals readLift realizeT_substitute substitute_substitute)

attribute [local irreducible] sphincsRom

/-- Realizing keeps the relabelling of the value. -/
theorem realizeT_map (θ : TVals) {A B : QReg} {α β : Type}
    (x : QComp (SSpecQ SelMem) A B α) (g : α → β) :
    realizeT θ (x.map g) = QuantumComp₂.map g (realizeT θ x) :=
  (congrArg (realizeT θ) (QuantumComp₂.map_eq_bind_pure g x)).trans
    ((realizeT_bind₂ θ x _).trans (QuantumComp₂.map_eq_bind_pure g _).symm)

/-- **The challenger regroups a round of hash calls**: the interleaved round. -/
theorem realizeT_challengeT_seqCalls (θ : TVals) (pol : DigestPolicy) :
    ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn sAdvSpec (fun _ : Fin w ↦ .hash) × E)
    (post : roundOut sAdvSpec (fun _ : Fin w ↦ .hash) × E ≃ B),
    realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd pol)
      (seqCalls (fun _ : Fin w ↦ SufCma.AdvPort.hash) E ℓ post)) =
      regRoundR TPos SelMem hmsgRoute E ℓ post
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, _ => by
    rw [regRoundR]
    symm
    exact (congrArg (QuantumComp₂.primBind _) (funext fun _ ↦
      congrArg (QuantumComp₂.queryBind _ _ _) (funext fun _ ↦
        congrArg (QuantumComp₂.primBind _) (funext fun _ ↦
          ((congrArg (realizeT θ) (Quantum.Par.substitute_map _ _ _)).trans
            (realizeT_map θ _ _)).trans
            (congrArg (QuantumComp₂.map _) (realizeT_challengeT_seqCalls θ pol _ _ _)))))).symm

/-! ## The template game of a parallel adversary -/

section template

/-- leanSPHINCS's parallel quantum SUF-CMA adversaries in the QROM. -/
abbrev SAdversaryPar : Type 1 :=
  SufCma.AdversaryPar PublicKey Message (Option Signature) Forgery

-- The parallel adversary's commands.
set_option quotPrecheck false in
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpecPar Message (Option Signature))

/-- The batched round of runtime 1, as a template. -/
noncomputable def batRoundT (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ hRound Qrom.HashDomain HashOutput w × E) :
    QComp (SSpecQ SelMem) A (QReg.of (hRound Qrom.HashDomain HashOutput w × E)) (Fin w → Unit) :=
  readLift goodQ ((batRoundSG TPos SelMem hmsgRoute w E ℓ).liftOrdinary
    (t := Quantum.Sponge.hwReadCmdSpec PairOut Qrom.HashDomain SelMem))

theorem realizeT_batRoundT (θ : TVals) (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ hRound Qrom.HashDomain HashOutput w × E) :
    realizeT θ (batRoundT w E ℓ) = batRoundR TPos SelMem hmsgRoute w E ℓ (Equiv.refl _) :=
  liftRG_batRoundSG (S := TPos) (M := SelMem) (v := θ) (τ := hmsgRoute) w E ℓ

/-- **The challenger of a parallel adversary**, as a template: a local operation or a signing
request is the sequential challenger on its serialization, a round of `H` is the batched round. -/
noncomputable def challengeTPar (pol : DigestPolicy) :
    CommandSubstitution AdvPP (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpecQ SelMem))
  | A, .prim o => IFreeM.substitute (challengeT SelMem cwUpd pol) (SufCma.toSeq A (.prim o))
  | _, .query (.hashPar w) E ℓ =>
      QuantumComp.bind (batRoundT w E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | A, .query (.sign r) E ℓ =>
      IFreeM.substitute (challengeT SelMem cwUpd pol) (SufCma.toSeq A (.query (.sign r) E ℓ))

/-- The challenged parallel adversary with its signing transcript, as a template. -/
noncomputable def advTPar (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar Message (Option Signature)) A B α) :
    QComp (SSpecQ SelMem) A B (α × SufCma.SignLog Message (Option Signature)) :=
  IFreeM.substitute (challengeTPar pol)
    (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

/-- **The challenge prefix of a parallel adversary, as a template.** -/
noncomputable def prefixTPar (pol : DigestPolicy) (A : SAdversaryPar) :
    QComp (SSpecQ SelMem) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :=
  revealThen goodQ pkReveal fun r₀ ↦
    (advTPar pol (A (tabR r₀.1).publicKey)).bind fun run ↦
      QuantumComp₂.pure ((tabR r₀.1).publicKey, run)

/-- **The game of a parallel adversary, as a template.** -/
noncomputable def gameTPar (pol : DigestPolicy) (A : SAdversaryPar) :
    QComp (SSpecQ SelMem) (QReg.of Unit) (QReg.of Unit) Bool :=
  revealThen goodQ pkReveal fun r₀ ↦
    (advTPar pol (A (tabR r₀.1).publicKey)).bind fun run ↦
      verifyT SelMem ((tabR r₀.1).publicKey, run)

theorem gameTPar_eq_prefixTPar_bind (pol : DigestPolicy) (A : SAdversaryPar) :
    gameTPar pol A = (prefixTPar pol A).bind (verifyT SelMem) := by
  simp only [gameTPar, prefixTPar, Quantum.Xmss.Assembly.revealThen_bind,
    QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]

/-- The realized prefix with batched rounds. -/
noncomputable def prefixQB (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    QComp (RSpecS SelMem) (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :=
  realizeT θ (prefixTPar pol A)

/-- The realized game with batched rounds. -/
noncomputable def gameQB (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    QComp (RSpecS SelMem) (QReg.of Unit) (QReg.of Unit) Bool :=
  realizeT θ (gameTPar pol A)

theorem gameQB_eq (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    gameQB pol A θ = (prefixQB pol A θ).bind fun pre ↦ realizeT θ (verifyT SelMem pre) := by
  rw [gameQB, gameTPar_eq_prefixTPar_bind, realizeT_bind₂]
  rfl

end template

/-! ## The game with rounds -/

section par

set_option quotPrecheck false in
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpecPar Message (Option Signature))

/-- The port of the rounds: `h`. -/
abbrev portS : Unit → (RSpecS SelMem).Port :=
  fun _ ↦ hPortR TPos SelMem

/-- The signature of the game with rounds. -/
abbrev ParRSpecS : QuantumOracleSpec.{0, 0} :=
  parSpec (RSpecS SelMem) portS

/-- **The batched round as a program with rounds**: the slots embedded, one round of `h`, the
slots projected back. -/
noncomputable def roundCmdS (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ hRound Qrom.HashDomain HashOutput w × E) :
    QComp ParRSpecS A (QReg.of (hRound Qrom.HashDomain HashOutput w × E)) (Fin w → Unit) :=
  QuantumComp₂.primBind (L := LocalSig.instruments)
    ⟨PUnit, fun _ ↦ _, embAll TPos SelMem hmsgRoute w E ℓ⟩ fun _ ↦
  QuantumComp₂.queryBind (spec := ParRSpecS) (.inr (.round w fun _ ↦ ()))
    (QReg.of ((Fin w → Bool) × E)) (Equiv.refl _) fun rs ↦
  QuantumComp₂.primBind (L := LocalSig.instruments)
    ⟨PUnit, fun _ ↦ _, projAll TPos SelMem hmsgRoute w E (Equiv.refl _)⟩ fun _ ↦
  QuantumComp₂.pure rs

/-- **The challenged parallel adversary with rounds** at `θ`: a round of `H` is `roundCmdS`,
every other command the realized template command. -/
noncomputable def advSubstS (θ : TVals) (pol : DigestPolicy) :
    CommandSubstitution AdvPP (QuantumComp.toIPFunctor LocalSig.instruments.{0} ParRSpecS)
  | A, .prim o => QuantumComp.liftOrdinary (realizeT θ (challengeTPar pol A (.prim o)))
  | _, .query (.hashPar w) E ℓ =>
      QuantumComp.bind (roundCmdS w E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | A, .query (.sign r) E ℓ =>
      QuantumComp.liftOrdinary (realizeT θ (challengeTPar pol A (.query (.sign r) E ℓ)))

/-- **The serialized round with rounds is the batched round.** -/
theorem substitute_roundCmdS (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ hRound Qrom.HashDomain HashOutput w × E) :
    IFreeM.substitute (parToSeq portS) (roundCmdS w E ℓ) =
      batRoundR TPos SelMem hmsgRoute w E ℓ (Equiv.refl _) := by
  unfold roundCmdS batRoundR
  refine (substitute_parToSeq_primBind portS _ _).trans (Eq.trans ?_ (QComp.act_bind _ _).symm)
  refine congrArg (QuantumComp.primBind _) (funext fun _ ↦ ?_)
  refine (substitute_parToSeq_round₂ portS _ _ _ _).trans ?_
  refine congrArg (QuantumComp₂.bind _) (funext fun rs ↦ ?_)
  rfl

theorem realizeT_challengeTPar (θ : TVals) (pol : DigestPolicy) (A : QReg)
    (c : (AdvPP).A A) :
    realizeT θ (challengeTPar pol A c) =
      IFreeM.substitute (parToSeq portS) (advSubstS θ pol A c) := by
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact (substitute_parToSeq_liftOrdinary portS _).symm
  · refine (realizeT_bind θ _ _).trans (Eq.trans ?_ (IFreeM.substitute_bind _ _ _).symm)
    rw [realizeT_batRoundT, substitute_roundCmdS]
    rfl
  · exact (substitute_parToSeq_liftOrdinary portS _).symm

/-- **The challenged parallel adversary with rounds and its signing transcript.** -/
noncomputable def advParS (θ : TVals) (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar Message (Option Signature)) A B α) :
    QComp ParRSpecS A B (α × SufCma.SignLog Message (Option Signature)) :=
  IFreeM.substitute (advSubstS θ pol)
    (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

theorem realizeT_advTPar (θ : TVals) (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar Message (Option Signature)) A B α) :
    realizeT θ (advTPar pol x) = IFreeM.substitute (parToSeq portS) (advParS θ pol x) := by
  rw [advTPar, advParS, realizeT_substitute, substitute_substitute]
  exact congrArg (fun σ ↦ IFreeM.substitute σ _) (funext fun A ↦ funext fun c ↦
    realizeT_challengeTPar θ pol A c)

/-- The reveal of the public key, realized at `θ`. -/
noncomputable def pkRevealS (θ : TVals) :
    QComp (RSpecS SelMem) (QReg.of Unit) (QReg.of Unit)
      (RevealVals TVal pkReveal × (Finset TPos × SelMem)) :=
  realizeT θ (revealThen (M := SelMem) goodQ pkReveal QuantumComp₂.pure)

/-- **The challenge prefix of a parallel adversary, with rounds.** -/
noncomputable def prefixQPar (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    QComp ParRSpecS (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :=
  QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec (RSpecS SelMem) portS)
    (pkRevealS θ)) fun r₀ ↦
      (advParS θ pol (A (tabR r₀.1).publicKey)).bind fun run ↦
        QuantumComp₂.pure ((tabR r₀.1).publicKey, run)

/-- **The game of a parallel adversary, with rounds.** -/
noncomputable def gameQPar (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    QComp ParRSpecS (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixQPar pol A θ).bind fun pre ↦
    QuantumComp.liftOrdinary (t := roundSpec (RSpecS SelMem) portS)
      (realizeT θ (verifyT SelMem pre))

/-- **The batched prefix is the serialized prefix with rounds.** -/
theorem prefixQB_serialize (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    prefixQB pol A θ = IFreeM.substitute (parToSeq portS) (prefixQPar pol A θ) := by
  have h1 : prefixTPar pol A =
      (revealThen (M := SelMem) goodQ pkReveal QuantumComp₂.pure).bind fun r₀ ↦
        (advTPar pol (A (tabR r₀.1).publicKey)).bind fun run ↦
          QuantumComp₂.pure ((tabR r₀.1).publicKey, run) :=
    rfl
  have hR : IFreeM.substitute (parToSeq portS) (prefixQPar pol A θ) =
      QuantumComp₂.bind (pkRevealS θ) fun r₀ ↦ IFreeM.substitute (parToSeq portS)
        ((advParS θ pol (A (tabR r₀.1).publicKey)).bind fun run ↦
          QuantumComp₂.pure ((tabR r₀.1).publicKey, run)) :=
    (substitute_bind₂ _ _ _).trans
      (congrArg (fun z ↦ QuantumComp₂.bind z _) (substitute_parToSeq_liftOrdinary portS _))
  refine ((congrArg (realizeT θ) h1).trans (realizeT_bind₂ θ _ _)).trans (Eq.trans ?_ hR.symm)
  refine congrArg (QuantumComp₂.bind _) (funext fun r₀ ↦ ?_)
  exact (realizeT_bind₂ θ _ _).trans ((congrArg (fun z ↦ QuantumComp₂.bind z _)
    (realizeT_advTPar θ pol _)).trans (substitute_bind₂ (parToSeq portS)
      (advParS θ pol (A (tabR r₀.1).publicKey)) fun run ↦
        QuantumComp₂.pure ((tabR r₀.1).publicKey, run)).symm)

/-- **The batched game is the serialized game with rounds.** -/
theorem gameQB_serialize (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    gameQB pol A θ = IFreeM.substitute (parToSeq portS) (gameQPar pol A θ) :=
  (gameQB_eq pol A θ).trans ((congrArg (fun z ↦ QuantumComp₂.bind z _)
    (prefixQB_serialize pol A θ)).trans (Eq.trans (congrArg (QuantumComp₂.bind _) (funext fun _ ↦
      (substitute_parToSeq_liftOrdinary portS _).symm)) (substitute_bind₂ _ _ _).symm))

end par

end Quantum.Qrom.Sphincs

end
