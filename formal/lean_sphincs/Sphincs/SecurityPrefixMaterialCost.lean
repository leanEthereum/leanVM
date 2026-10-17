import Sphincs.SecurityPrefixMaterialView

/-! A signing attempt evaluates identically under publicly agreeing answer functions, and the
signer simulated from erased prepared material and the selected chain frontier
(`erasedMaterialSign`), which never receives the selected low secret. -/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open Concrete Completeness SeedModel PreparedScheme SphincsBase.QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Randomized.finishSign
  Seeded.forestKey Seeded.forestOpen chainWalk
set_option backward.isDefEq.respectTransparency false

namespace PublicAgreement

variable {parameter : PublicParameter} {seed : MasterSeed} {left right : QueryImpl HashSpec Id}
    (h : PublicAgreement parameter seed left right)
include h

variable [Params]

theorem signAttempt (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (hparameter : sk.parameter = parameter) :
    evalWithAnswerFn left (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) =
      evalWithAnswerFn right (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) := by
  simp only [Seeded.signAttempt, evalWithAnswerFn_bind, hparameter, h.digestCall]
  split <;> rfl

end PublicAgreement

variable [Params]

/-- The simulator receives the erased material and the frontier, never the selected low secret. -/
noncomputable def erasedMaterialSign (segment : Segment) (outside : QueryImpl HashSpec Id)
    (material : Material) (frontier root : Digest) (message : Message) : PMF (Option Signature × Nat) :=
  let erased := replaceMaterial segment material 0
  publicSignWithCost segment (preparedOracle outside 0 erased) (materialSecrets erased) frontier
    (fun level => evalWithAnswerFn (preparedOracle outside 0 erased)
      (Seeded.surrogate segment.parameter 0 level : OracleComp HashSpec Digest))
    ⟨0, parameter erased, root⟩ message

end Sphincs.Security.Prefix
