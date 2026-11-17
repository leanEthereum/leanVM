module

public import Quantum.Xmss.Assembly.Depth.MassGame
public import Quantum.Sphincs.Assembly.Depth.Sim

@[expose] public section

/-!
# Hidden masses of leanSPHINCS's canonical game with rounds

The hidden masses of `gameRPar Ap pol p v` against `(runtimeR m₀).par portR` (Hybrid's
`parSpongeMassR`: a round weighs the summed hidden masses of its slots) are the hidden masses
`spongeMass` of the canonical game of the serialization `gameR pol (serialize Ap) p v` against
`runtimeR m₀`, command by command (`massPair_cmdR`, leanXMSS's Depth.Mass `MassPair`).

* `massPair_prefixRPar`, `massPair_gameRPar`: the prefix and the game.
* `totalWeight_parSpongeMassR_gameRPar_eq`: the hidden masses at `m0R` and `initR`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs Common Common.SufCma
open HashSig (Message)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (spongeMass parSpongeMassR massPair_liftOrdinary_runtimeR
  massPair_lockRoundR_runtimeR)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR portR)

namespace Quantum.Sphincs.Assembly

set_option quotPrecheck false in
-- The parallel adversary's commands.
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z))

section game

variable (m₀ : Mem HPos) (Hh : Set Z) (Hk Hk' : Set X) (pol : DigestPolicy) (p : Pub)
  (v : (s : HPos) → XD s)

set_option quotPrecheck false in
-- Pairs against `runtimeR m₀` with the hidden masses.
local notation "HidPair" => MassPair (portR X Z HPos Selections) (runtimeR m₀)
  (spongeMass Hh Hk Hk') (parSpongeMassR Hh Hk Hk')

/-- **Command by command**, the challenged parallel adversary pairs with the serialized one. -/
theorem massPair_cmdR (A : QReg) (c : (AdvPP).A A) :
    HidPair (cmdR pol p v A c) (advSubstR pol p v A c) := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _
  · rw [cmdR_permPar pol p v dir E ℓ]
    exact massPair_lockRoundR_runtimeR m₀ Hh Hk Hk' p.perm dir E ℓ (Equiv.refl _)
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t}) fun _ h ↦ ⟨ULift.up (), h⟩
  · exact massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _

/-- The challenged parallel adversary pairs with the serialized one. -/
theorem massPair_advParR {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)) A B α) :
    HidPair (advSeqR pol p v x) (advParR pol p v x) :=
  massPair_substitute (massPair_cmdR m₀ Hh Hk Hk' pol p v) _

variable (Ap : SAdversaryPar)

/-- **The challenge prefix with rounds pairs with the prefix of the serialization.** -/
theorem massPair_prefixRPar :
    HidPair (prefixR pol (Quantum.SufCma.serialize Ap) p v) (prefixRPar Ap pol p v) := by
  rw [prefixR_serialize]
  exact Quantum.Xmss.Assembly.MassPair.bind₂
    (massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' (pkRevealR v)) fun r₀ ↦
      Quantum.Xmss.Assembly.MassPair.bind₂ (massPair_advParR m₀ Hh Hk Hk' pol p v _) fun run ↦
        massPair_pure _

/-- **The game with rounds pairs with the game of the serialization.** -/
theorem massPair_gameRPar :
    HidPair (gameR pol (Quantum.SufCma.serialize Ap) p v) (gameRPar Ap pol p v) := by
  rw [gameR_eq]
  exact Quantum.Xmss.Assembly.MassPair.bind₂ (massPair_prefixRPar m₀ Hh Hk Hk' pol p v Ap)
    fun pre ↦ massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _

end game

/-- **The hidden masses of the game with rounds**: a round weighs the summed hidden masses of its
slots, and the total is the hidden mass of the game of the serialization. -/
theorem totalWeight_parSpongeMassR_gameRPar_eq (Hh : Set Z) (Hk Hk' : Set X) (Ap : SAdversaryPar)
    (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR Hh Hk Hk') (gameRPar Ap pol p v) initR =
      (runtimeR m0R).totalWeight .instruments (spongeMass Hh Hk Hk')
        (gameR pol (Quantum.SufCma.serialize Ap) p v) initR :=
  ((massPair_gameRPar m0R Hh Hk Hk' pol p v Ap).totalWeight_eq initR_posSemidef).symm

end Quantum.Sphincs.Assembly

end
