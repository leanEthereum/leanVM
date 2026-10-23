import SphincsFors.SecurityPrefixCost

/-! Counting the hash queries of lifted hash computations: on a fixed answer function, counting
returns the value together with its `hashCalls`; and the signer with its cost evaluated on the
outside function from the selected chain frontier (`publicSignWithCost`). Private randomizer draws
contribute zero hash calls. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.Prefix
open Concrete SphincsBase.QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Randomized.finishSign
  Seeded.signAttempt
set_option backward.isDefEq.respectTransparency false

theorem counted_lift_hash {α : Type} (computation : OracleComp HashSpec α) :
    counted SourceHash (liftM computation : OracleComp OracleWorld α) =
    (liftM (counted (fun _ => True) computation) : OracleComp OracleWorld (α × Nat)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, counted_pure]
  | query_bind input next ih =>
      simp only [liftM_bind]
      change counted SourceHash (liftM (OracleWorld.query (.inr input)) >>= fun output => liftM (next output)) = _
      simp only [counted_query_bind, SourceHash, ite_true, ih, liftM_bind, liftM_pure]
      rfl

theorem eval_counted_hash {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    evalWithAnswerFn f (counted (fun _ => True) computation) =
      (evalWithAnswerFn f computation, hashCalls f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ih, ite_true]
      change (_, 1 + hashCalls f (next (f input))) = (_, (input :: queriedInputs f (next (f input))).length)
      simp only [List.length_cons, hashCalls, Nat.add_comm]

theorem fixedHashWorld_counted_lift_hash {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (counted SourceHash (liftM computation : OracleComp OracleWorld α)) =
      PMF.pure (evalWithAnswerFn f computation, hashCalls f computation) := by
  rw [counted_lift_hash, fixedHashWorld_lift_hash, eval_counted_hash]

variable [Params]

/-- The original assembly cost is evaluated using the outside function. Cost invariance
ensures that no hidden table or selected chain secret is needed to compute it. -/
noncomputable def publicSignWithCost (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message) : PMF (Option Signature × Nat) := do
  let loop ← simulateQ (fixedHashWorld outside)
    (counted SourceHash (Randomized.signDigestLoop sk message digestAttemptLimit))
  match loop.1 with
  | none => pure (none, loop.2)
  | some randomness => pure (publicFinishSign segment outside secrets frontier surrogates sk.seed sk.root message randomness,
        loop.2 + hashCalls outside (Randomized.finishSign sk message randomness))

end SphincsFors.Security.Prefix
