import Sphincs.SecurityPrefixSignLayer
import Sphincs.SecurityPrefixExecution

/-! Hash-only evaluation inside the private-sampling interpreter is deterministic, and the hash-only
signature assembly that receives only the selected chain frontier (`publicFinishSign`). -/

open OracleComp OracleSpec

namespace Sphincs.Security.Prefix
open Concrete
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.signLayer
  Seeded.forestOpen Seeded.forestKey sequenceFin chainWalk

/-- Hash-only evaluation inside the private-sampling interpreter is deterministic. -/
theorem fixedHashWorld_lift_hash (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      PMF.pure (evalWithAnswerFn f computation) := by
  have hlift : simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      simulateQ (fun bytes => PMF.pure (f bytes) : QueryImpl HashSpec PMF) computation :=
    QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedHashWorld f)
      (fun bytes => PMF.pure (f bytes)) (fun _ => rfl) computation
  rw [hlift]
  clear hlift
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalWithAnswerFn_pure]; rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ← PMF.monad_pure_eq_pure, pure_bind]
      exact ih (f input)

variable [Params]

/-- The hash-only signature assembly receives only the selected chain frontier; the forest
opening and all other chains are evaluated using the outside function. -/
noncomputable def publicFinishSign (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (seed : MasterSeed) (root : Digest) (message : Message) (randomness : Randomness) : Option Signature :=
  let digest := evalWithAnswerFn outside
    (messageDigest segment.parameter root message randomness : OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let opening := evalWithAnswerFn outside (Seeded.forestOpen segment.parameter index (digestMarks digest) seed :
    OracleComp HashSpec (Coord → CoordOpening))
  let layer := publicLayer segment outside secrets frontier surrogates index topLayer
    (evalWithAnswerFn outside (Seeded.forestKey segment.parameter index seed : OracleComp HashSpec Digest))
  layer.map fun top => ⟨randomness, opening, Fin.cases top (fun i => Fin.elim0 i)⟩

end Sphincs.Security.Prefix
