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

theorem expanded_unloggedRetainedRest_queryBound (adversary : Adversary) (key : SecretKey) (q : Nat)
    (hbound : (gameRest scheme adversary ⟨key.root, key.parameter⟩ key).IsQueryBoundP (· matches Sum.inr _) q) :
    (simulateQ (expandedAdversaryImpl key)
      (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)).IsQueryBoundP (· matches Sum.inr _) q := by
  have h := simulateQ_expanded_retainedGameRestComputation_isQueryBoundP adversary key q hbound
  rw [retainedGameRestComputation_eq_signingTrace, simulateQ_map, isQueryBoundP_map_iff] at h
  have heq : Prod.fst <$> simulateQ (expandedAdversaryImpl key)
      (signingTraceComputation (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)) =
        simulateQ (expandedAdversaryImpl key) (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) := by
    rw [← simulateQ_map, signingTraceComputation_fst]
  exact (isQueryBoundP_iff_of_map_eq (p := (· matches Sum.inr _)) heq).mp h

end SphincsSecurity.Concrete.FtsProbeSimulation
