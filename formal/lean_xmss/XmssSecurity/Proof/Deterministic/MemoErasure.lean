import XmssSecurity.Proof.Deterministic.Replay
import XmssSecurity.Proof.Deterministic.Memoize
import XmssSecurity.Proof.Seeded.Erasure

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

variable {Request Answer : Type} [DecidableEq Request]

theorem erases_pure_of_resolves {α : Type} {known : QueryCache HashSpec}
    {computation : OracleComp HashSpec α} {value : α} (h : Resolves known computation value) :
    Erases known computation (pure value) := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih => exact Erases.skip (known := known) input answer hanswer next _ ih

theorem keeps_bind_of_resolves {α β : Type} {known : QueryCache HashSpec}
    {computation : OracleComp HashSpec α} {value : α} (h : Resolves known computation value)
    (left right : α → OracleComp OracleWorld β)
    (htail : Erases (worldKnown known) (left value) (right value)) :
    Erases (worldKnown known) ((liftM computation : OracleComp OracleWorld α) >>= left)
      (liftM computation >>= right) := by
  induction h with
  | pure value => simpa only [liftM_pure, pure_bind] using htail
  | query input answer hanswer next value _ ih =>
      simp only [liftM_bind, bind_assoc]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _)
        (liftM (OracleWorld.query (.inr input)) >>= _)
      exact Erases.cached (known := worldKnown known) (Sum.inr input) answer hanswer _ _ (ih htail)

def runSigning {α : Type} (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) : OracleComp OracleWorld α :=
  simulateQ ((QueryImpl.ofLift OracleWorld (OracleComp OracleWorld)) +
    (fun request => (liftM (sign request) : OracleComp OracleWorld Answer))) computation

theorem erases_memoize {α : Type} (known : QueryCache HashSpec)
    (sign : Request → OracleComp HashSpec Answer) (replies : Request → Answer)
    (hknown : ∀ request, Resolves known (sign request) (replies request))
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α)
    (cache : QueryCache (Request →ₒ Answer))
    (hcache : ∀ request answer, cache request = some answer → answer = replies request) :
    Erases (worldKnown known) (runSigning sign computation)
      (runSigning sign (memoize computation cache)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => exact .pure value
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [memoize_base]
          change Erases _ (liftM (OracleWorld.query input) >>= fun answer => runSigning sign (next answer))
            (liftM (OracleWorld.query input) >>= fun answer => runSigning sign (memoize (next answer) cache))
          exact .query input _ _ (fun answer => ih answer cache hcache)
      | inr input =>
          rw [memoize_request]
          cases hc : cache input with
          | some answer =>
              have ha := hcache input answer hc
              subst answer
              change Erases _ ((liftM (sign input) : OracleComp OracleWorld Answer) >>=
                fun answer => runSigning sign (next answer)) _
              exact (erases_pure_of_resolves (hknown input)).lift_hash.bind_known _ _
                (ih (replies input) cache hcache)
          | none =>
              change Erases _ ((liftM (sign input) : OracleComp OracleWorld Answer) >>=
                fun answer => runSigning sign (next answer))
                  (liftM (sign input) >>= fun answer => runSigning sign
                    (memoize (next answer) (cache.cacheQuery input answer)))
              apply keeps_bind_of_resolves (hknown input)
              apply ih
              intro request answer hanswer
              by_cases heq : request = input
              · subst request
                rw [QueryCache.cacheQuery_self] at hanswer
                exact (Option.some.inj hanswer).symm
              · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hanswer
                exact hcache request answer hanswer

end XmssSecurity.Seeded
