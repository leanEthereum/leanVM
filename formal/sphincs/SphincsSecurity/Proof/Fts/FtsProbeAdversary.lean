import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.DirectQueryBudget
import SphincsSecurity.Proof.Fts.FtsProbeGame
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open OracleComp OracleSpec

def signingTraceComputation
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    OracleComp (OracleWorld + SigningSpec) (alpha × QueryLog SigningSpec) :=
  OracleComp.construct
    (C := fun _ => OracleComp (OracleWorld + SigningSpec)
      (alpha × QueryLog SigningSpec))
    (fun value => pure (value, []))
    (fun input _next recursivelyTrace => do
      let output ← liftM ((OracleWorld + SigningSpec).query input)
      let result ← recursivelyTrace output
      pure (result.1, signingLogFragment input output ++ result.2))
    computation

theorem simulateQ_withTraceAppend_run_eq_signingTraceComputation
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (OracleWorld + SigningSpec) m)
    (computation : OracleComp (OracleWorld + SigningSpec) alpha) :
    (simulateQ (QueryImpl.withTraceAppend handler signingLogFragment)
        computation).run =
      simulateQ handler (signingTraceComputation computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp [signingTraceComputation]
  | query_bind input next ih =>
      simp [signingTraceComputation, ih]

noncomputable def liftOracleWorldLeft
    (computation : OracleComp OracleWorld alpha) :
    OracleComp (OracleWorld + SigningSpec) alpha := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  exact liftM computation

theorem simulateQ_liftOracleWorldLeft
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (left : QueryImpl OracleWorld m) (right : QueryImpl SigningSpec m)
    (computation : OracleComp OracleWorld alpha) :
    simulateQ (left + right) (liftOracleWorldLeft computation) =
      simulateQ left computation := by
  unfold liftOracleWorldLeft
  exact QueryImpl.simulateQ_add_liftM_left left right computation

noncomputable def tracedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) Bool := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure (decide (SigningTranscript.Valid log ∧
    ¬SigningTranscript.Contains log forgery) && verified)

end SphincsSecurity.Concrete.FtsProbeSimulation
