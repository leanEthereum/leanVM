module

public import XmssSecurity.Proof.Seeded.Erasure

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

noncomputable def signRequestEquiv : SignRequest ≃ (LeafIndex × Message) where
  toFun request := (request.leafIndex, request.message)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype SignRequest := Fintype.ofEquiv (LeafIndex × Message) signRequestEquiv.symm

/-- The randomizer bases `R0(idx, m)`, one full derivation answer per request. -/
abbrev RandomizerOutputs := SignRequest → HashOutput

noncomputable opaque randomizerOutputsSampleableType : SampleableType RandomizerOutputs :=
  SampleableType.ofFintype RandomizerOutputs

noncomputable local instance : SampleableType RandomizerOutputs := randomizerOutputsSampleableType

noncomputable def sampleRandomizerOutputs : ProbComp RandomizerOutputs := $ᵗ RandomizerOutputs

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The trials `base + trial, base + trial + 1, ...` against the precomputed key, stopping at the first
admissible encoding. -/
def tableSignFrom (base : Randomness) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat randomnessBits trial
      match ← Concrete.precomputedSignAttempt secretKey leafIndex message randomness with
      | some signature => return some signature
      | none => tableSignFrom base secretKey leafIndex message attempts (trial + 1)

/-- The signer with its randomizer base read from a table of the derivations' answers. -/
def tableSign (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) : m (Option Signature) := do
  let result ← tableSignFrom ((randomizers ⟨leafIndex, message⟩).extractLsb' 0 randomnessBits)
    secretKey leafIndex message signingAttemptLimit 0
  return if Concrete.topSignedAt secretKey leafIndex then result else none

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme XmssSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk leafIndex message => liftM (tableSign randomizers sk leafIndex message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

end XmssSecurity.Seeded
