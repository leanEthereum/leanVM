module

public import FORS.Statement
public import FORS.CrateStatic
public import Common.Signature
public import Common.PiOnly
public import Common.Linear
public import Common.StaticSwap
public import Sphincs.Model
public import Sphincs.Queries

@[expose] public section

/-!
# Upstream's model and the crate's signer in the generic SUF-CMA game

Upstream's model of the scheme (`FORS.Seeded.keygen`, `FORS.Seeded.sign`: a landing call, sibling
subtrees, the verifier's recomputation of each layer's root) is the generic SUF-CMA game of `common`
(`modelScheme`, `experiment_eq`). The statement's key generation and signer are the crate's
(`sign`: the key expanded, the top tree rebuilt, every tree built level by level), not the
model's call for call; their copy in the model's hash monad is `FORS.Crate.keygen` /
`FORS.Crate.sign` (`crateScheme`, the seed as the secret key). On every answer function the crate's
copy gives the model's public key and signatures (`FORS.Crate.eval_keygen`, `eval_sign`), and both query only
inputs of at most 2084 bytes (`Sphincs.Queries`): `staticSwap`, which `Sphincs/AdvRpm.lean` uses to
move the model's bound to the crate's copy.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.Model

attribute [local instance] params

/- A weight bound of a concrete game must not be unfolded: it recurses through the whole game. -/
attribute [local irreducible] QueryCostAtMost

/-- Upstream's model in the generic SUF-CMA game: the seed, key generation, the deterministic
signer, the verifier, and the winning condition (`FORS.SigningTranscript`). -/
noncomputable def modelScheme :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.Seeded.SecretKey FORS.Message
      (Option FORS.Signature) FORS.Forgery where
  sample := FORS.sampleMasterSeed
  keygen := FORS.Seeded.keygen
  sign sk message := (FORS.Seeded.sign sk message : OracleComp FORS.HashSpec _)
  verify pk forgery :=
    FORS.Concrete.verify (m := OracleComp FORS.HashSpec) pk forgery.message forgery.signature
  win log forgery :=
    decide (FORS.SigningTranscript.Valid log ∧ ¬FORS.SigningTranscript.Contains log forgery)

/-- The model's ROM experiment is the generic one. -/
theorem experiment_eq
    (main : FORS.PublicKey → OracleComp (World + (FORS.Message →ₒ Option FORS.Signature))
      FORS.Forgery) :
    FORS.Security.experiment ⟨main⟩ = romExperiment modelScheme main := by
  have h : FORS.Security.countedOracle = countedImpl := by
    unfold FORS.Security.countedOracle countedImpl
    congr 1
  unfold FORS.Security.experiment romExperiment
  rw [h]
  rfl

/-- The crate's key generation and signer in the generic SUF-CMA game, the seed `SK.seed` as the
secret key (`FORS.Crate.keygen`, `FORS.Crate.sign`); the model's verifier and winning condition. -/
noncomputable def crateScheme :
    SchemeWithHash FORS.MasterSeed FORS.PublicKey FORS.MasterSeed FORS.Message
      (Option FORS.Signature) FORS.Forgery where
  sample := FORS.sampleMasterSeed
  keygen seed := (FORS.Crate.keygen seed : OracleComp FORS.HashSpec _)
  sign seed message := (FORS.Crate.sign seed message : OracleComp FORS.HashSpec _)
  verify := modelScheme.verify
  win := modelScheme.win

/-- **The crate's signer for the model's**: the same public key and signatures on every answer
function (`FORS/CrateStatic.lean`). -/
noncomputable def staticSwap : StaticSwap modelScheme crateScheme where
  keep := id
  sample_eq := rfl
  verify_eq := rfl
  win_eq := rfl
  keygen_eval f seed := by
    simp only [modelScheme, crateScheme, id]
    exact FORS.Crate.eval_keygen f seed
  sign_eval f seed message := by
    simp only [modelScheme, crateScheme, id]
    exact FORS.Crate.eval_sign f seed message

end Sphincs.Model
