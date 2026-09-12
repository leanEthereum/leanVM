import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.OtsProbeOrigin
import SphincsSecurity.Proof.Residual.RetainedSigningTrace
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signingTraceComputation_fst {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Prod.fst <$> signingTraceComputation computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [signingTraceComputation]
  | query_bind input next ih =>
      rw [signingTraceComputation_query_bind, map_bind]
      apply bind_congr
      intro reply
      rw [Functor.map_map]
      exact ih reply

theorem expanded_unloggedRetainedRest_queryBound (oracle : QueryImpl HashSpec Id) (adversary : Adversary) (key : SecretKey) (q : Nat)
    (hbound : FixedHashQueryBound oracle (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) q) :
    FixedHashQueryBound oracle (simulateQ (expandedAdversaryImpl key)
      (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) q := by
  have h := simulateQ_expanded_retainedGameRestComputation_fixedHashQueryBound oracle adversary key q hbound
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, fixedHashQueryBound_map_iff] at h
  have heq : Prod.fst <$> simulateQ (expandedAdversaryImpl key)
      (signingTraceComputation (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) =
        simulateQ (expandedAdversaryImpl key) (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) := by
    rw [← simulateQ_map, signingTraceComputation_fst]
  exact (fixedHashQueryBound_iff_of_map_eq oracle heq q).mp h

end SphincsSecurity.Concrete.FtsProbeSimulation
