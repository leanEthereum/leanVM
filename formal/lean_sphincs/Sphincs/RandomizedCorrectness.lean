import Sphincs.Correctness
import Sphincs.Randomized

/-! The signature assembled from any landed randomizer verifies; no randomizer-derivation
assumption occurs. This is the deterministic assembly part of randomized-signing correctness. -/

open OracleComp

namespace Sphincs.Completeness
open Concrete Seeded

variable (f : QueryImpl HashSpec Id) [Params]
attribute [local irreducible] Seeded.signLayer Seeded.forestOpen Seeded.treePath Seeded.treeNode
  Seeded.forestKey Seeded.treeRoot Seeded.spineNode sequenceFin

/-- Successful assembly has the same WOTS, forest and path invariants as seeded signing. -/
theorem finishSign_spec (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) {signature : Signature}
    (hland : Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)))
    (h : evalWithAnswerFn f (Randomized.finishSign secretKey message randomness) = some signature) :
    Landed secretKey.parameter (digestIndex (digestValue f secretKey message signature.randomness))
      ∧ signature.forest = evalWithAnswerFn f (Seeded.forestOpen secretKey.parameter
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestMarks (digestValue f secretKey message signature.randomness)) secretKey.seed
          : OracleComp HashSpec (Coord → CoordOpening))
      ∧ ∀ lay : Layer, evalWithAnswerFn f (Seeded.signLayer secretKey
          (digestIndex (digestValue f secretKey message signature.randomness)) lay
          : OracleComp HashSpec (Option (LayerSignature lay))) = some (signature.layers lay) := by
  rw [Randomized.finishSign, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_bind] at h
  split at h
  next layers hlayers =>
    simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
    subst h
    exact ⟨hland, rfl, fun lay => sequenceLayers_spec f _ hlayers lay⟩
  next => exact absurd h (by simp)

/-- Every signature assembled after a randomizer lands verifies for the generated root. -/
theorem verify_of_finishSign (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) {signature : Signature}
    (hroot : secretKey.root = evalWithAnswerFn f (Seeded.treeRoot secretKey.parameter topLayer
      rootTree secretKey.seed : OracleComp HashSpec Digest))
    (hland : Landed secretKey.parameter (digestIndex (digestValue f secretKey message randomness)))
    (h : evalWithAnswerFn f (Randomized.finishSign secretKey message randomness) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true :=
  verify_of_parts f secretKey message hroot (finishSign_spec f secretKey message randomness hland h)

end Sphincs.Completeness
