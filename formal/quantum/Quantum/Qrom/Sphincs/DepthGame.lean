module

public import Quantum.Qrom.Sphincs.DepthBridge

@[expose] public section

/-!
# The serialized game and the game with batched rounds run alike

Against a runtime `R` in which the interleaved and the batched rounds run alike
(`RoundsCommute`), the game of the serialization of a parallel adversary and the game with
batched rounds run alike and have the same summed weights for every weight vanishing at port `h`
(`runTWEq_gameQ`, `runTWEq_prefixQ`): their only difference is the order of the calls inside
each round, blocks of calls of `h` whose results are unique (`runTWEq_bind_substitute`,
`runTWEq_bind_freeAt`).
-/

open IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Par
open Quantum.Xmss.Assembly (recHwSpec realizeT realizeT_bind realizeT_bind₂ revealThen RevealVals
  realizeT_substitute substitute_substitute)

attribute [local irreducible] sphincsRom

variable (R : QuantumRuntime (RSpecS SelMem))

/-- The reveal of `T`, realized, with related continuations. -/
theorem runTWEq_realizeT_revealThen (θ : TVals) {B C : QReg} {α : Type} (T : Finset TPos)
    {k₁ k₂ : RevealVals TVal T × (Finset TPos × SelMem) → QComp (SSpecQ SelMem) B C α}
    (h : ∀ r, RunTWEq R (hPortR TPos SelMem) (realizeT θ (k₁ r)) (realizeT θ (k₂ r))) :
    RunTWEq R (hPortR TPos SelMem) (realizeT θ (revealThen goodQ T k₁))
      (realizeT θ (revealThen goodQ T k₂)) :=
  RunTWEq.liftBind _ fun _ ↦ RunTWEq.liftBind _ fun _ ↦ h _

variable {R} (hR : RoundsCommute TPos SelMem hmsgRoute R)
include hR

/-- **The serialized challenged adversary and the batched one run alike**, with any
continuation. -/
theorem runTWEq_challenged (θ : TVals) (pol : DigestPolicy) {A B : QReg} {α : Type}
    (x : QComp (SufCma.advSpecPar Message (Option Signature)) A B α) {Y : QReg → Type}
    (k : ∀ u, QuantumComp₂.Leaf B (α × SufCma.SignLog Message (Option Signature)) u →
      QuantumComp LocalSig.instruments.{0} (RSpecS SelMem) Y u) :
    RunTWEq R (hPortR TPos SelMem)
      (IFreeM.bind (realizeT θ (challengedT SelMem cwUpd pol
        (SufCma.withSignLog (IFreeM.substitute SufCma.toSeq x)))) k)
      (IFreeM.bind (realizeT θ (advTPar pol x)) k) := by
  have e₁ : realizeT θ (challengedT SelMem cwUpd pol
      (SufCma.withSignLog (IFreeM.substitute SufCma.toSeq x))) =
      IFreeM.substitute (fun A c ↦ realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd pol)
        (SufCma.toSeq A c))) (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []) := by
    rw [challengedT, show SufCma.withSignLog (IFreeM.substitute SufCma.toSeq x) =
      IFreeM.substitute SufCma.toSeq (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])
      from SufCma.logSigns_substitute_toSeq _ x [], substitute_substitute, realizeT_substitute]
  have e₂ : realizeT θ (advTPar pol x) =
      IFreeM.substitute (fun A c ↦ realizeT θ (challengeTPar pol A c))
        (SufCma.logSignsPar (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []) :=
    realizeT_substitute θ _ _
  refine RunTWEq.of_eq (congrArg (IFreeM.bind · k) e₁) (congrArg (IFreeM.bind · k) e₂)
    (runTWEq_bind_substitute (fun A c Y g₁ g₂ hg ↦ ?_) _ fun _ _ ↦ RunTWEq.refl _)
  rcases c with o | ⟨w | r, E, ℓ⟩
  · exact runTWEq_bind_congr _ hg
  · have h₁ : realizeT θ (IFreeM.substitute (challengeT SelMem cwUpd pol)
        (SufCma.toSeq A (.query (.hashPar w) E ℓ))) =
        IFreeM.bind (regRoundR TPos SelMem hmsgRoute E ℓ (Equiv.refl _)) fun _ l ↦
          QuantumComp.pure ⟨ULift.up (), l.1.symm⟩ :=
      (congrArg (realizeT θ) (IFreeM.substitute_bind _ (SufCma.hashRound w E ℓ) _)).trans
        ((realizeT_bind θ _ _).trans (congrArg (fun z ↦ IFreeM.bind z _)
          (realizeT_challengeT_seqCalls θ pol E ℓ _)))
    have h₂ : realizeT θ (challengeTPar pol A (.query (.hashPar w) E ℓ)) =
        IFreeM.bind (batRoundR TPos SelMem hmsgRoute w E ℓ (Equiv.refl _)) fun _ l ↦
          QuantumComp.pure ⟨ULift.up (), l.1.symm⟩ :=
      (realizeT_bind θ _ _).trans (congrArg (fun z ↦ IFreeM.bind z _)
        (realizeT_batRoundT θ w E ℓ))
    refine RunTWEq.of_eq ((congrArg (IFreeM.bind · g₁) h₁).trans (IFreeM.bind_assoc _ _ _))
      ((congrArg (IFreeM.bind · g₂) h₂).trans (IFreeM.bind_assoc _ _ _)) ?_
    refine runTWEq_bind_freeAt
      (freeAt_regRoundR (S := TPos) (M := SelMem) (τ := hmsgRoute) R E ℓ _)
      (freeAt_batRoundR (S := TPos) (M := SelMem) (τ := hmsgRoute) R w E ℓ _)
      (hR w E (B := QReg.of (hRound Qrom.HashDomain HashOutput w × E)) ℓ (Equiv.refl _)) ?_
    exact hg _ _
  · exact runTWEq_bind_congr _ hg

/-- **The serialized prefix and the batched prefix run alike.** -/
theorem runTWEq_prefixQ (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    RunTWEq R (hPortR TPos SelMem) (prefixQ pol (SufCma.serialize A) θ) (prefixQB pol A θ) :=
  runTWEq_realizeT_revealThen R θ pkReveal fun _ ↦
    RunTWEq.of_eq (realizeT_bind₂ θ _ _) (realizeT_bind₂ θ _ _)
      (runTWEq_challenged hR θ pol _ _)

/-- **The serialized game and the batched game run alike.** -/
theorem runTWEq_gameQ (pol : DigestPolicy) (A : SAdversaryPar) (θ : TVals) :
    RunTWEq R (hPortR TPos SelMem) (gameQ pol (SufCma.serialize A) θ) (gameQB pol A θ) :=
  runTWEq_realizeT_revealThen R θ pkReveal fun _ ↦
    RunTWEq.of_eq (realizeT_bind₂ θ _ _) (realizeT_bind₂ θ _ _)
      (runTWEq_challenged hR θ pol _ _)

end Quantum.Qrom.Sphincs

end
