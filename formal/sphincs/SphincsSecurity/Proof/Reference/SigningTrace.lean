import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.SignSupport
/-!
# Signing cache intervals

The ordinary signing log records only requests and responses. This trace additionally records the
random-oracle cache immediately before and after each signer invocation. Its projections recover
the ordinary logged adversary run exactly.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

def signingLogFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : QueryLog SigningSpec :=
  match input with
  | .inl _ => []
  | .inr request => [⟨request, output⟩]

def signingLogUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalCache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : QueryLog SigningSpec :=
  log ++ signingLogFragment input output

noncomputable def unloggedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) ProbComp) := by
  intro input
  cases input with
  | inl worldInput => exact romImpl worldInput
  | inr request => exact simulateQ romImpl (Concrete.scheme.sign secretKey request)

theorem unloggedMappedAdversaryImpl_cache_le
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((unloggedMappedAdversaryImpl secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache result hmem
  | inr request =>
      change result ∈ support
        ((simulateQ romImpl (Concrete.scheme.sign secretKey request)).run initialCache) at hmem
      exact simulateQ_romImpl_cache_le (Concrete.scheme.sign secretKey request)
        initialCache result hmem

noncomputable def logTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × QueryLog SigningSpec) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl secretKey) signingLogUpdate

end SphincsSecurity
