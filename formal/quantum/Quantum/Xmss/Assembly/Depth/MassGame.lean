module

public import Quantum.Xmss.Assembly.Depth.Mass
public import Quantum.Xmss.Assembly.Depth.Sim

@[expose] public section

/-!
# Hidden masses of the canonical game with rounds

The hidden masses of `gameRPar Ap L` against `(runtimeR m₀).par portR` (Hybrid's
`parSpongeMassR`: a round weighs the summed hidden masses of its slots) are the hidden masses
`spongeMass` of the canonical game of the serialization `gameR (serialize Ap) L` against
`runtimeR m₀`, command by command (`massPair_cmdR`, Mass's `MassPair`).

* `massPair_gameRPar`, `totalWeight_parSpongeMassR_gameRPar_eq`: the games.
* `uavg_mask_parSpongeMass_le`, `uavg_mask_parReadMass_le`: the masked averages of the hybrid
  (Security's `uavg_mask_spongeMass_le`, `≤ 6q · kappaS`, and `uavg_mask_readMass_le`,
  `≤ readCap`, for the serialization), as the hypotheses `hμ`, `hν` of Depth.Security's
  `uavg_p1R_leD_of_par` at `xP := gameRPar Ap`.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid Quantum.Par
  HashSig LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel Quantum.SufCma

/-! ## Sequencing fixed-register pairs -/

section bind₂

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} {port : Q → spec.Port}
  {R : QuantumRuntime spec} {W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
  {W' : ∀ i, Matrix ((parSpec spec port).In i × R.D) ((parSpec spec port).In i × R.D) ℂ → ℝ≥0∞}

/-- **Sequencing pairs of fixed-register programs.** -/
theorem MassPair.bind₂ {A B C : QReg} {α β : Type}
    {x₁ : QuantumComp₂ LocalSig.instruments.{0} spec A B α}
    {x₂ : QuantumComp₂ LocalSig.instruments.{0} (parSpec spec port) A B α}
    {k₁ : α → QuantumComp₂ LocalSig.instruments.{0} spec B C β}
    {k₂ : α → QuantumComp₂ LocalSig.instruments.{0} (parSpec spec port) B C β}
    (hx : MassPair port R W W' x₁ x₂) (hk : ∀ a, MassPair port R W W' (k₁ a) (k₂ a)) :
    MassPair port R W W' (x₁.bind k₁) (x₂.bind k₂) := by
  rw [QuantumComp₂.bind_eq_freeM₂_bind, QuantumComp₂.bind_eq_freeM₂_bind]
  unfold FreeM₂.bind
  exact MassPair.bind hx fun u p ↦ by
    obtain ⟨rfl, a⟩ := p
    exact hk a

end bind₂

set_option quotPrecheck false in
-- The parallel adversary's commands.
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z))

/-! ## The games -/

section game

variable (m₀ : Mem) (Hh : Set Z) (Hk Hk' : Set X)

set_option quotPrecheck false in
-- Pairs against `runtimeR m₀` with the hidden masses.
local notation "HidPair" => MassPair (portR X Z HPos Selections) (runtimeR m₀)
  (spongeMass Hh Hk Hk') (parSpongeMassR Hh Hk Hk')

/-- **Command by command**, the challenged parallel adversary pairs with the serialized one. -/
theorem massPair_cmdR (L : HonestTable) (A : QReg) (c : (AdvPP).A A) :
    HidPair (cmdR L A c) (advSubstR L A c) := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _
  · rw [cmdR_permPar L dir E ℓ]
    exact massPair_lockRoundR_runtimeR m₀ Hh Hk Hk' (pubOf L).perm dir E ℓ (Equiv.refl _)
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t}) fun _ h ↦ ⟨ULift.up (), h⟩
  · exact massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _

/-- The challenged parallel adversary pairs with the serialized one. -/
theorem massPair_advParR (L : HonestTable) {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)) A B α) :
    HidPair (advSeqR L x) (advParR L x) :=
  massPair_substitute (massPair_cmdR m₀ Hh Hk Hk' L) _

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z))

/-- **The challenge prefix with rounds pairs with the prefix of the serialization.** -/
theorem massPair_prefixRPar (L : HonestTable) :
    HidPair (prefixR (Quantum.SufCma.serialize Ap) L) (prefixRPar Ap L) := by
  rw [prefixR_serialize]
  exact MassPair.bind₂ (massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' (pkRevealR L)) fun r₀ ↦
    MassPair.bind₂ (massPair_advParR m₀ Hh Hk Hk' L _) fun run ↦ massPair_pure _

/-- **The game with rounds pairs with the game of the serialization.** -/
theorem massPair_gameRPar (L : HonestTable) :
    HidPair (gameR (Quantum.SufCma.serialize Ap) L) (gameRPar Ap L) := by
  rw [gameR_eq]
  exact MassPair.bind₂ (massPair_prefixRPar m₀ Hh Hk Hk' Ap L) fun pre ↦
    massPair_liftOrdinary_runtimeR m₀ Hh Hk Hk' _

/-- **The hidden masses of the game with rounds**: a round weighs the summed hidden masses of its
slots, and the total is the hidden mass of the game of the serialization. -/
theorem totalWeight_parSpongeMassR_gameRPar_eq (L : HonestTable) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR Hh Hk Hk') (gameRPar Ap L) initR =
      (runtimeR m0R).totalWeight .instruments (spongeMass Hh Hk Hk')
        (gameR (Quantum.SufCma.serialize Ap) L) initR :=
  ((massPair_gameRPar m0R Hh Hk Hk' Ap L).totalWeight_eq initR_posSemidef).symm

end game

/-! ## The masked averages of the hybrid -/

section avg

variable {q : ℕ}
  (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery (X × Z))
  (hperm : ∀ pk, IFreeM.IsChargeBound (Quantum.SufCma.serialize Ap pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (Quantum.SufCma.serialize Ap pk) (cmdCharge signCharge)
    lifetime)
include hperm hsign

/-- **The masked hidden mass of the game with rounds** (hypothesis `hμ` of
`uavg_p1R_leD_of_par` at `xP := gameRPar Ap`): at most `6q · kappaS`, from Security's
`uavg_mask_spongeMass_le` for the serialization. -/
theorem uavg_mask_parSpongeMass_le :
    uavg (fun t : HonestTable × RE ↦ if maskG t then
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parSpongeMassR (coverH t.1) (coverK t.1) (coverK' t.1)) (gameRPar Ap t.1) initR
      else 0) ≤ ((6 * q : ℕ) : ℝ≥0∞) * kappaS := by
  refine le_of_eq_of_le (congrArg uavg (funext fun t ↦ ?_)) (uavg_mask_spongeMass_le hperm hsign)
  split_ifs
  · exact totalWeight_parSpongeMassR_gameRPar_eq _ _ _ Ap t.1
  · rfl

/-- **The masked read-port mass of the game with rounds** (hypothesis `hν` of
`uavg_p1R_leD_of_par` at `xP := gameRPar Ap`): at most `readCap`, from Security's
`uavg_mask_readMass_le` for the serialization and Sim's `readMass_gameRPar_eq`. -/
theorem uavg_mask_parReadMass_le :
    uavg (fun t : HonestTable × RE ↦ if maskG t then
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (readMass (coverH t.1) (coverK t.1) (coverK' t.1)))
        (gameRPar Ap t.1) initR
      else 0) ≤ readCap := by
  refine le_of_eq_of_le (congrArg uavg (funext fun t ↦ ?_)) (uavg_mask_readMass_le hperm hsign)
  split_ifs
  · exact (readMass_gameRPar_eq Ap t.1 _ _ _).symm
  · rfl

end avg

end Quantum.Xmss.Assembly

end
