import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.ForgeryClassify
import SphincsSecurity.Proof.Ots.SecretProbe
import SphincsSecurity.Proof.Reference.SigningTrace
/-!
# Opaque one-time chain values

The lazy one-time simulation gives a separate opaque cell to every chain start and every structural
oracle answer. An ordinary chain query probes the value at its starting digit. A leaf query probes
chain zero's endpoint, which is the only endpoint needed by the fresh-opening extraction; a backward
opening always starts strictly before the endpoint and is therefore caught by a chain query.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

inductive Coordinate where
  | chainStart (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (chainIdx : ChainIndex)
  | position (position : Position)

abbrev RetainedRestResult := (Forgery × QueryLog SigningSpec) × Bool

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
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih => simp [signingTraceComputation, ih]

noncomputable def liftOracleWorldLeft
    (computation : OracleComp OracleWorld alpha) :
    OracleComp (OracleWorld + SigningSpec) alpha := by
  letI directLift : MonadLift (OracleQuery OracleWorld)
      (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left
      (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  exact liftM computation

noncomputable def retainedGameRestComputation (adversary : Adversary)
    (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) RetainedRestResult := do
  let (forgery, log) ← signingTraceComputation (adversary.main publicKey)
  let verified ← liftOracleWorldLeft
    (scheme.verify publicKey forgery.message forgery.signature)
  pure ((forgery, log), verified)

end SphincsSecurity.Concrete.OtsProbeSimulation
