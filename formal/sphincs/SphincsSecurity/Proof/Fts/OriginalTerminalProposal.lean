import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.OriginalProposalExecution
import SphincsSecurity.Proof.Fts.TerminalProposalWord
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem originalProposalImpl_complete {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    ((originalProposalImpl key spent enabled update input).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  simp only [originalProposalImpl, proposalRecordImpl, StateT.run_mk]
  by_cases hactive : originalProposalActive key spent enabled input state.2 = true
  · rw [if_pos hactive, PMF.bind_map]
    cases input with
    | inl world => simp only [originalProposalActive, Bool.false_eq_true] at hactive
    | inr message =>
        have hcache : ProposalCacheBound key state.2.1 (spent state.2) := by
          by_contra hcache
          simp [originalProposalActive, hcache] at hactive
        rw [originalRejectedProposal, dif_pos hcache]
        simpa only [cappedRecordProposalBridge, List.append_assoc, Function.comp_def] using
          complete_cappedRecordProposalBridge_prefix (PMF.uniformOfFintype Index)
            (originalProposalRecord key (.inr message) state.2.1) (fun record => record.index)
            targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one
            (originalProposalRecord_cap key message state.2.1 (spent state.2) hcache) total state.1
  · rw [if_neg hactive, PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _

theorem simulateQ_originalProposalImpl_complete {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    ((simulateQ (originalProposalImpl key spent enabled update) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
      simp_rw [ih]
      exact originalProposalImpl_complete key spent enabled update total input state

noncomputable def terminalProposalPotential {α : Type} (base : PMF α) (total : Nat)
    (payoff : List α → ENNReal) (consumed : List α) : ENNReal :=
  ∑' word, Pr[= word | completeProposalWord base total consumed] * payoff word

theorem expected_originalProposalImpl_terminalPotential {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    (∑' result, Pr[= result | (originalProposalImpl key spent enabled update input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (originalProposalImpl_complete key spent enabled update total input state)
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul] at h
  exact h

end SphincsSecurity.Concrete
