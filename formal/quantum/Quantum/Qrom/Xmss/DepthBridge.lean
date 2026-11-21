module

public import Quantum.Qrom.Xmss.DepthPar
public import Quantum.Qrom.Xmss.End
public import Quantum.Qrom.Xmss.NoReuse

@[expose] public section

/-!
# leanXMSS's QROM game for a parallel adversary, as a program with rounds

The QROM chain runs runtime 2 with record ports (`runtimeR`) on the realized template
`gameQ A θ` of a sequential adversary. For a parallel adversary `A` (rounds of `w` calls of `H`,
`SufCma.AdversaryPar`) the game of its serialization `SufCma.serialize A` is the serialization of a
program over the parallel signature `parSpec (RSpec SelMem) portQ` whose rounds are rounds of the
sponge port `h` (`prefixQ_serialize`, `gameQ_serialize`): every other command of the game is a
single call, lifted unchanged.

* `refusePar A`: the parallel adversary refusing reused leaves; its serialization is
  `refuse (SufCma.serialize A)` (`refuse_serialize`) and it keeps every budget.
* `advSubstQ θ P`: the challenged parallel adversary at the hidden values `θ` and the parameter
  `P`: a round of `H` stays a round of port `h`, a signing request or local operation is the
  realized command of the sequential challenger.
* `prefixQPar A θ`, `gameQPar A θ`: the challenge prefix and the game with rounds.
* Budgets: total width `q`, classical calls `clsCapQ` (from the sequential budgets, through
  `isChargeBound_of_substitute_parToSeq`) and rounds `d` (`rounds_prefixQPar`,
  `rounds_gameQPar`).
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Par
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec realizeT realizeT_bind realizeT_bind₂ revealThen
  extCls RevealVals)

attribute [local irreducible] xmssRom

/-- leanXMSS's parallel quantum SUF-CMA adversary in the QROM. -/
abbrev AdversaryPar :=
  SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery

-- The parallel adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpecPar SigningRequest (Option Signature))

-- The sequential adversary's commands.
set_option quotPrecheck false in
local notation "AdvP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (SufCma.advSpec SigningRequest (Option Signature))

/-! ## Refusing reused leaves -/

section refuse

/-- **Refuse reused leaves** (parallel adversaries): as `refuseFrom`, rounds kept. -/
noncomputable def refuseFromPar {X : QReg → Type} :
    {A : QReg} → Finset LeafIndex → IFreeM AdvPP X A → IFreeM AdvPP X A
  | _, _, .pure x => .pure x
  | _, F, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ refuseFromPar F (next b)
  | _, F, .liftBind (.query (.hashPar w) E ℓ) next =>
      .liftBind (.query (.hashPar w) E ℓ) fun b ↦ refuseFromPar F (next b)
  | _, F, .liftBind (.query (.sign r) E ℓ) next =>
      if r.leafIndex ∈ F then
        .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFromPar F (next (ULift.up none))
      else .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFromPar (insert r.leafIndex F) (next b)

/-- **The parallel adversary that never reuses a leaf.** -/
noncomputable def refusePar (A : AdversaryPar) : AdversaryPar :=
  fun pk ↦ refuseFromPar ∅ (A pk)

variable {X : QReg → Type} {A : QReg} {F : Finset LeafIndex} {r : SigningRequest} {E : QReg}
  {ℓ : A ≃ (SufCma.advSpecPar SigningRequest (Option Signature)).In (.sign r) × E}
  {next : (b : (AdvPP).B A (QuantumComp.Cmd.query (SufCma.AdvPortPar.sign r) E ℓ)) →
    IFreeM AdvPP X ((AdvPP).src A (QuantumComp.Cmd.query (SufCma.AdvPortPar.sign r) E ℓ) b)}

theorem refuseFromPar_sign_of_mem (h : r.leafIndex ∈ F) :
    refuseFromPar F (IFreeM.liftBind (QuantumComp.Cmd.query (SufCma.AdvPortPar.sign r) E ℓ)
      next) =
      .liftBind (.prim (refuseOp r E ℓ)) fun _ ↦ refuseFromPar F (next (ULift.up none)) := by
  rw [refuseFromPar, ite_eq_left h]

theorem refuseFromPar_sign_of_notMem (h : r.leafIndex ∉ F) :
    refuseFromPar F (IFreeM.liftBind (QuantumComp.Cmd.query (SufCma.AdvPortPar.sign r) E ℓ)
      next) =
      .liftBind (.query (.sign r) E ℓ) fun b ↦ refuseFromPar (insert r.leafIndex F) (next b) := by
  rw [refuseFromPar, ite_eq_right h]

/-- Refusing keeps every charge bound of a parallel adversary. -/
theorem isChargeBound_refuseFromPar {c : SufCma.AdvPortPar SigningRequest → ℕ}
    (x : IFreeM AdvPP X A) (F : Finset LeafIndex) {n : ℕ}
    (h : IFreeM.IsChargeBound x (SufCma.cmdChargePar c) n) :
    IFreeM.IsChargeBound (refuseFromPar F x) (SufCma.cmdChargePar c) n := by
  induction x using IFreeM.inductionOn generalizing F n with
  | pure _ _ => trivial
  | liftBind A c' next ih =>
    rcases c' with o | ⟨_ | r, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · exact ⟨h.1, fun b ↦ ih b F (h.2 b)⟩
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFromPar_sign_of_mem hr]
        exact ⟨Nat.zero_le _, fun _ ↦ (ih _ F (h.2 _)).mono (Nat.sub_le n _)⟩
      · rw [refuseFromPar_sign_of_notMem hr]
        exact ⟨h.1, fun b ↦ ih b _ (h.2 b)⟩

/-- Refusing passes through a round's calls of `H`. -/
theorem refuseFrom_bind_seqCalls {Y : QReg → Type} (F : Finset LeafIndex) :
    ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (SufCma.advSpec SigningRequest (Option Signature))
      (fun _ : Fin w ↦ .hash) × E)
    (post : roundOut (SufCma.advSpec SigningRequest (Option Signature))
      (fun _ : Fin w ↦ .hash) × E ≃ B)
    (g : ∀ u, QuantumComp₂.Leaf B (Fin w → Unit) u → IFreeM AdvP Y u),
    refuseFrom F (IFreeM.bind (seqCalls (fun _ : Fin w ↦ SufCma.AdvPort.hash) E ℓ post) g) =
      IFreeM.bind (seqCalls (fun _ : Fin w ↦ SufCma.AdvPort.hash) E ℓ post) fun u l ↦
        refuseFrom F (g u l)
  | 0, _, _, _, _, _, _ => rfl
  | w + 1, E, _, B, ℓ, post, g =>
    congrArg (IFreeM.liftBind _) (funext fun b ↦ by
      dsimp only [QuantumComp.onDown]
      exact (congrArg (refuseFrom F) (IFreeM.bind_imap _ _ _)).trans
        ((refuseFrom_bind_seqCalls F (w := w) _ _ _ _).trans
          (IFreeM.bind_imap (fun s (p : QuantumComp₂.Leaf B (Fin w → Unit) s) ↦
            (⟨p.1, Fin.cons b.down p.2⟩ : QuantumComp₂.Leaf B (Fin (w + 1) → Unit) s))
            (fun u l ↦ refuseFrom F (g u l)) _).symm))

/-- **Refusing commutes with serialization.** -/
theorem refuseFrom_substitute_toSeq (x : IFreeM AdvPP X A) (F : Finset LeafIndex) :
    refuseFrom F (IFreeM.substitute SufCma.toSeq x) =
      IFreeM.substitute SufCma.toSeq (refuseFromPar F x) := by
  induction x using IFreeM.inductionOn generalizing F with
  | pure _ _ => rfl
  | liftBind _ c next ih =>
    rcases c with o | ⟨w | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b F)
    · refine (congrArg (refuseFrom F) (IFreeM.bind_assoc _ _ _)).trans
        ((refuseFrom_bind_seqCalls F E ℓ _ _).trans
          ((congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_)).trans
            (IFreeM.bind_assoc _ _ _).symm))
      obtain ⟨h, a⟩ := l
      subst h
      exact ih _ F
    · by_cases hr : r.leafIndex ∈ F
      · rw [refuseFromPar_sign_of_mem hr]
        exact (refuseFrom_sign_of_mem (next := fun b ↦ IFreeM.substitute SufCma.toSeq (next b))
          hr).trans (congrArg (IFreeM.liftBind _) (funext fun _ ↦ ih _ F))
      · rw [refuseFromPar_sign_of_notMem hr]
        exact (refuseFrom_sign_of_notMem (next := fun b ↦ IFreeM.substitute SufCma.toSeq (next b))
          hr).trans (congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b _))

/-- **The serialization of `refusePar A` refuses the reused leaves of the serialization.** -/
theorem refuse_serialize (A : AdversaryPar) :
    refuse (SufCma.serialize A) = SufCma.serialize (refusePar A) :=
  funext fun pk ↦ refuseFrom_substitute_toSeq (A pk) ∅

end refuse

/-! ## The challenged parallel adversary -/

section challenge

/-- The sponge port `h` of runtime 2 with record ports: the port of the rounds. -/
abbrev portQ : Unit → (RSpec SelMem).Port :=
  fun _ ↦ .inl (.inl (.inl .h))

/-- The signature of the parallel game: runtime 2's ports with record ports, and rounds of
`h`. -/
abbrev ParRSpec : QuantumOracleSpec.{0, 0} :=
  parSpec (RSpec SelMem) portQ

/-- Realizing a substituted template is substituting the realized commands. -/
theorem realizeT_substitute {P' : IPFunctor.Endo QReg}
    (σ : CommandSubstitution P' (QuantumComp.toIPFunctor LocalSig.instruments.{0}
      (XSpec SelMem))) {Ω : QReg → Type} {A : QReg} (θ : HPos → Digest) (x : IFreeM P' Ω A) :
    realizeT θ (IFreeM.substitute σ x) = IFreeM.substitute (fun s a ↦ realizeT θ (σ s a)) x := by
  unfold realizeT
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  simp only [IFreeM.substitute_toSubstitution]
  rfl

/-- Realizing keeps the relabelling of the value. -/
theorem realizeT_map (θ : HPos → Digest) {A B : QReg} {α β : Type}
    (x : QComp (XSpec SelMem) A B α) (g : α → β) :
    realizeT θ (x.map g) = QuantumComp₂.map g (realizeT θ x) :=
  (congrArg (realizeT θ) (QuantumComp₂.map_eq_bind_pure g x)).trans
    ((realizeT_bind₂ θ x _).trans (QuantumComp₂.map_eq_bind_pure g _).symm)

/-- The challenger passes a hash call through, as a call of `h`. -/
theorem realizeT_challengeT_queryBind_hash (θ : HPos → Digest) (P : PublicParameter) (E : QReg)
    {A B : QReg} {α : Type}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In .hash × E)
    (k : Unit → QComp (SufCma.advSpec SigningRequest (Option Signature))
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out .hash × E)) B α) :
    realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P)
      (QuantumComp₂.queryBind .hash E ℓ k)) =
      QuantumComp₂.queryBind (spec := RSpec SelMem) (portQ ()) E ℓ fun r ↦
        realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P) (k r)) :=
  rfl

/-- **The challenger keeps a round of hash calls**: the same calls of `h`. -/
theorem realizeT_challengeT_seqCalls (θ : HPos → Digest) (P : PublicParameter) :
    ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (SufCma.advSpec SigningRequest (Option Signature))
      (fun _ : Fin w ↦ .hash) × E)
    (post : roundOut (SufCma.advSpec SigningRequest (Option Signature))
      (fun _ : Fin w ↦ .hash) × E ≃ B),
    realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P)
      (seqCalls (fun _ : Fin w ↦ SufCma.AdvPort.hash) E ℓ post)) =
      seqCalls (spec := RSpec SelMem) (fun _ : Fin w ↦ portQ ()) E ℓ post
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, _ =>
    (realizeT_challengeT_queryBind_hash θ P _ _ _).trans
      (congrArg (QuantumComp₂.queryBind _ _ _) (funext fun _ ↦
        ((congrArg (realizeT θ) (Quantum.Par.substitute_map _ _ _)).trans
          (realizeT_map θ _ _)).trans
          (congrArg (QuantumComp₂.map _) (realizeT_challengeT_seqCalls θ P _ _ _))))

/-- The realized command of the sequential challenger at `θ` and `P`. -/
noncomputable def cmdQ (θ : HPos → Digest) (P : PublicParameter) (A : QReg) (c : (AdvPP).A A) :
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (RSpec SelMem))
      (fun t ↦ {b : (AdvPP).B A c // (AdvPP).src A c b = t}) A :=
  realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P) (SufCma.toSeq A c))

/-- **The challenged parallel adversary** at `θ` and `P`: a round of `H` is a round of `h`, a
local operation or a signing request is the realized command of the sequential challenger. -/
noncomputable def advSubstQ (θ : HPos → Digest) (P : PublicParameter) :
    CommandSubstitution AdvPP (QuantumComp.toIPFunctor LocalSig.instruments.{0} ParRSpec)
  | A, .prim o => QuantumComp.liftOrdinary (cmdQ θ P A (.prim o))
  | _, .query (.hashPar w) E ℓ =>
      QuantumComp.queryBind (spec := ParRSpec) (.inr (.round w fun _ ↦ ())) E ℓ fun _ ↦
        QuantumComp.pure ⟨ULift.up (), rfl⟩
  | A, .query (.sign r) E ℓ => QuantumComp.liftOrdinary (cmdQ θ P A (.query (.sign r) E ℓ))

/-- The round of `H` of the serialized challenged adversary is the serialized round of `h`. -/
theorem cmdQ_hashPar (θ : HPos → Digest) (P : PublicParameter) (w : ℕ) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpecPar SigningRequest (Option Signature)).In (.hashPar w) × E) :
    cmdQ θ P A (.query (.hashPar w) E ℓ) =
      IFreeM.substitute (parToSeq portQ) (advSubstQ θ P A (.query (.hashPar w) E ℓ)) := by
  have h1 : cmdQ θ P A (.query (.hashPar w) E ℓ) =
      IFreeM.bind (seqCalls (spec := RSpec SelMem) (fun _ : Fin w ↦ portQ ()) E ℓ
        (Equiv.refl _)) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩ :=
    (congrArg (realizeT θ) (IFreeM.substitute_bind (challengeT SelMem cwUpd P)
      (SufCma.hashRound w E ℓ) _)).trans ((realizeT_bind θ _ _).trans
        (congrArg (fun z ↦ IFreeM.bind z _) (realizeT_challengeT_seqCalls θ P E ℓ _)))
  refine h1.trans ((congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_)).trans
    (IFreeM.bind_assoc _ _ _).symm)
  obtain ⟨h, a⟩ := l
  subst h
  rfl

/-- **The challenged serialized adversary is the serialized challenged parallel adversary.** -/
theorem realizeT_challengeT_substitute_toSeq (θ : HPos → Digest) (P : PublicParameter)
    {X : QReg → Type} {A : QReg} (y : IFreeM AdvPP X A) :
    realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P) (IFreeM.substitute SufCma.toSeq y)) =
      IFreeM.substitute (parToSeq portQ) (IFreeM.substitute (advSubstQ θ P) y) := by
  rw [Quantum.Xmss.Assembly.substitute_substitute, realizeT_substitute,
    Quantum.Xmss.Assembly.substitute_substitute]
  refine congrArg (fun σ ↦ IFreeM.substitute σ y) (funext fun s ↦ funext fun c ↦ ?_)
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact (substitute_parToSeq_liftOrdinary portQ (cmdQ θ P s (.prim o))).symm
  · exact cmdQ_hashPar θ P w E ℓ
  · exact (substitute_parToSeq_liftOrdinary portQ (cmdQ θ P s (.query (.sign r) E ℓ))).symm

/-- **The challenged parallel adversary with its signing transcript.** -/
noncomputable def advParQ (θ : HPos → Digest) (P : PublicParameter) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar SigningRequest (Option Signature)) A B α) :
    QComp ParRSpec A B (α × SignLog) :=
  IFreeM.substitute (advSubstQ θ P) (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

theorem realizeT_challengedT_withSignLog (θ : HPos → Digest) (P : PublicParameter) {A B : QReg}
    {α : Type} (x : QComp (SufCma.advSpecPar SigningRequest (Option Signature)) A B α) :
    realizeT θ (challengedT SelMem cwUpd P
      (SufCma.withSignLog (IFreeM.substitute SufCma.toSeq x))) =
      IFreeM.substitute (parToSeq portQ) (advParQ θ P x) :=
  (congrArg (fun z ↦ realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd P) z))
    (SufCma.logSigns_substitute_toSeq _ x [])).trans (realizeT_challengeT_substitute_toSeq θ P _)

end challenge

/-! ## The game with rounds -/

section game

/-- The reveal of the public key, realized at `θ`. -/
noncomputable def pkRevealQ (θ : HPos → Digest) :
    QComp (RSpec SelMem) (QReg.of Unit) (QReg.of Unit)
      (RevealVals HD pkReveal × (Finset HPos × SelMem)) :=
  realizeT θ (revealThen (M := SelMem) goodQ pkReveal QuantumComp₂.pure)

/-- **The challenge prefix of a parallel adversary, with rounds**: the public key's reveal, then
the challenged parallel adversary with its signing transcript. -/
noncomputable def prefixQPar (A : AdversaryPar) (θ : HPos → Digest) :
    QComp ParRSpec (QReg.of Unit) (QReg.of Unit) (PublicKey × (Forgery × SignLog)) :=
  QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec (RSpec SelMem) portQ)
    (pkRevealQ θ)) fun r₀ ↦
      (advParQ θ (pkT r₀.1).parameter (A (pkT r₀.1))).bind fun run ↦
        QuantumComp₂.pure (pkT r₀.1, run)

/-- **The game of a parallel adversary, with rounds**: the prefix, then the verification. -/
noncomputable def gameQPar (A : AdversaryPar) (θ : HPos → Digest) :
    QComp ParRSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixQPar A θ).bind fun pre ↦ QuantumComp.liftOrdinary (t := roundSpec (RSpec SelMem) portQ)
    (realizeT θ (verifyT SelMem pre))

/-- **The challenge prefix of the serialization is the serialized prefix with rounds.** -/
theorem prefixQ_serialize (A : AdversaryPar) (θ : HPos → Digest) :
    prefixQ (SufCma.serialize A) θ = IFreeM.substitute (parToSeq portQ) (prefixQPar A θ) := by
  have h1 : prefixT SelMem cwUpd (SufCma.serialize A) =
      (revealThen (M := SelMem) goodQ pkReveal QuantumComp₂.pure).bind fun r₀ ↦
        (challengedT SelMem cwUpd (pkT r₀.1).parameter
          (SufCma.withSignLog (SufCma.serialize A (pkT r₀.1)))).bind fun run ↦
            QuantumComp₂.pure (pkT r₀.1, run) :=
    rfl
  have hR : IFreeM.substitute (parToSeq portQ) (prefixQPar A θ) =
      QuantumComp₂.bind (pkRevealQ θ) fun r₀ ↦ IFreeM.substitute (parToSeq portQ)
        ((advParQ θ (pkT r₀.1).parameter (A (pkT r₀.1))).bind fun run ↦
          QuantumComp₂.pure (pkT r₀.1, run)) :=
    (substitute_bind₂ _ _ _).trans
      (congrArg (fun z ↦ QuantumComp₂.bind z _) (substitute_parToSeq_liftOrdinary portQ _))
  refine ((congrArg (realizeT θ) h1).trans (realizeT_bind₂ θ _ _)).trans (Eq.trans ?_ hR.symm)
  refine congrArg (QuantumComp₂.bind _) (funext fun r₀ ↦ ?_)
  exact (realizeT_bind₂ θ _ _).trans ((congrArg (fun z ↦ QuantumComp₂.bind z _)
    (realizeT_challengedT_withSignLog θ _ _)).trans (substitute_bind₂ (parToSeq portQ)
      (advParQ θ (pkT r₀.1).parameter (A (pkT r₀.1))) fun run ↦
        QuantumComp₂.pure (pkT r₀.1, run)).symm)

/-- **The game of the serialization is the serialized game with rounds.** -/
theorem gameQ_serialize (A : AdversaryPar) (θ : HPos → Digest) :
    gameQ (SufCma.serialize A) θ = IFreeM.substitute (parToSeq portQ) (gameQPar A θ) :=
  (gameQ_eq_verify _ θ).trans ((congrArg (fun z ↦ QuantumComp₂.bind z _)
    (prefixQ_serialize A θ)).trans (Eq.trans (congrArg (QuantumComp₂.bind _) (funext fun _ ↦
      (substitute_parToSeq_liftOrdinary portQ _).symm)) (substitute_bind₂ _ _ _).symm))

end game

end Quantum.Qrom.Xmss

end
