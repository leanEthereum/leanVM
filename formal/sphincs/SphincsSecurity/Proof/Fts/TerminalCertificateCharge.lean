import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateProposalInvariant
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private noncomputable def expectedStateCharge {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (computation : OracleComp spec α) : σ → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => charge input state +
      ∑' result, Pr[= result | (impl input).run state] * next result.1 result.2) computation

private theorem expectedStateCharge_query_bind {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α) (state : σ) :
    expectedStateCharge impl charge (OracleSpec.query input >>= next) state =
      charge input state + ∑' result, Pr[= result | (impl input).run state] *
        expectedStateCharge impl charge (next result.1) result.2 := rfl

private theorem expectedStateCharge_mono {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (first second : spec.Domain → σ → ENNReal)
    (invariant : σ → Prop)
    (hpreserve : ∀ input state, invariant state → ∀ result ∈ ((impl input).run state).support, invariant result.2)
    (hle : ∀ input state, invariant state → first input state ≤ second input state)
    (computation : OracleComp spec α) (state : σ) (hinv : invariant state) :
    expectedStateCharge impl first computation state ≤ expectedStateCharge impl second computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedStateCharge_query_bind, expectedStateCharge_query_bind]
      apply add_le_add (hle input state hinv)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ ((impl input).run state).support
      · exact mul_le_mul' le_rfl (ih result.1 result.2 (hpreserve input state hinv result hr))
      · have hp : Pr[= result | (impl input).run state] = 0 := by
          rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
          exact hr
        rw [hp, zero_mul, zero_mul]

private theorem expected_state_accumulator {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (counter : σ → ENNReal) (charge : spec.Domain → σ → ENNReal)
    (hstep : ∀ input state, (∑' result, Pr[= result | (impl input).run state] * counter result.2) =
      counter state + charge input state)
    (computation : OracleComp spec α) (state : σ) :
    (∑' result, Pr[= result | (simulateQ impl computation).run state] * counter result.2) =
      counter state + expectedStateCharge impl charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedStateCharge, OracleComp.construct_pure, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedStateCharge_query_bind]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      rw [hstep, add_assoc]

private theorem expected_pmf_congr_of_support {α : Type} (law : PMF α) (first second : α → ENNReal)
    (heq : ∀ result ∈ law.support, first result = second result) :
    (∑' result, Pr[= result | law] * first result) = ∑' result, Pr[= result | law] * second result := by
  apply tsum_congr
  intro result
  by_cases hr : result ∈ law.support
  · rw [heq result hr]
  · have hp : Pr[= result | law] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]

theorem certificateProposalImpl_counter_support (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (value : ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state.2 length record) = value)
    (result : (OracleWorld + SigningSpec).Range input × (List Index × CertificateMonitorState))
    (hr : result ∈ ((certificateProposalImpl key budget required stopAfter input).run state).support) :
    counter result.2.2 = value := by
  simp only [certificateProposalImpl, originalProposalImpl, proposalRecordImpl, StateT.run_mk] at hr
  split at hr <;> rw [PMF.mem_support_map_iff] at hr
  · obtain ⟨source, _, rfl⟩ := hr
    exact hadvance _ _
  · obtain ⟨record, _, rfl⟩ := hr
    exact hadvance _ _

theorem expected_certificateProposalImpl_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
      result.2.2.2.creationCost) = state.2.2.creationCost + certificateMonitorCharge key budget required input state.2 := by
  rw [expected_pmf_congr_of_support _ _ (fun _ => state.2.2.creationCost +
    certificateMonitorCharge key budget required input state.2) (fun result hr =>
      certificateProposalImpl_counter_support key budget required stopAfter input state
        (fun state => state.2.creationCost) _
        (certificateMonitorUpdate_creationCost key budget required stopAfter input state.2) result hr)]
  simp only [ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]

theorem expected_certificateProposalImpl_mass_terminalPotential (key : SecretKey) (budget total : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
      (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1)) =
        state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 +
          certificateMonitorMass key budget input state.2 *
            terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  let mass := state.2.2.creationMass + certificateMonitorMass key budget input state.2
  calc
    _ = ∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
        (mass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) := by
      apply expected_pmf_congr_of_support
      intro result hr
      rw [certificateProposalImpl_counter_support key budget required stopAfter input state
        (fun state => state.2.creationMass) mass
        (certificateMonitorUpdate_creationMass key budget required stopAfter input state.2) result hr]
    _ = mass * ∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1 := by
      simp_rw [mul_left_comm _ mass]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [expected_certificateProposalImpl_terminalPotential]
      exact add_mul _ _ _

theorem expected_certificateProposal_creationCost_le_mass_terminalPotential {α : Type}
    (key : SecretKey) (budget total : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState)
    (hbudget : budget ≤ 2 ^ 127) (hinv : CertificateProposalInvariant key total state) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required
      (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
      computation).run state] * result.2.2.2.creationCost) ≤
      state.2.2.creationCost +
        ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required
          (fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record))
          computation).run state] * (result.2.2.2.creationMass *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1) := by
  let guarded : CertificateStopRule := fun input state length record =>
    proposalPrefixStop input state length record || stopAfter input state length record
  let impl := certificateProposalImpl key budget required guarded
  let first := fun input (state : List Index × CertificateMonitorState) =>
    certificateMonitorCharge key budget required input state.2
  let second := fun input (state : List Index × CertificateMonitorState) =>
    certificateMonitorMass key budget input state.2 *
      terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1
  have hcost := expected_state_accumulator impl (fun state => state.2.2.creationCost) first
    (expected_certificateProposalImpl_creationCost key budget required guarded) computation state
  have hmass := expected_state_accumulator impl (fun state => state.2.2.creationMass *
      terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1) second
    (expected_certificateProposalImpl_mass_terminalPotential key budget total required guarded (terminalCertificatePrice required))
    computation state
  have hcharge := expectedStateCharge_mono impl first second (CertificateProposalInvariant key total)
    (certificateProposalImpl_invariant key budget total required stopAfter)
    (fun input state hinv => certificateMonitorCharge_le_terminalPrice_of_invariant key budget total required input state hbudget hinv)
    computation state hinv
  calc
    _ = state.2.2.creationCost + expectedStateCharge impl first computation state := hcost
    _ ≤ state.2.2.creationCost + expectedStateCharge impl second computation state := add_le_add le_rfl hcharge
    _ ≤ _ := by rw [hmass]; exact add_le_add le_rfl le_add_self

theorem expected_certificateTerminalGame_project (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (weight : CertificateGameResult → ENNReal) :
    (∑' result, Pr[= result | certificateTerminalGame adversary budget required stopAfter stopped total] * weight result.1) =
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * weight result := by
  have h := congrArg (fun law : PMF CertificateGameResult => ∑' result, Pr[= result | law] * weight result)
    (certificateTerminalGame_game adversary budget required stopAfter stopped total)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
  exact h

theorem expected_certificateTerminalGame_weight_payoff (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (weight : CertificateGameResult → ENNReal) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | certificateTerminalGame adversary budget required stopAfter stopped total] *
      (weight result.1 * payoff result.2)) =
        ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
          (weight result * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) := by
  rw [certificateTerminalGame, ← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul]
  simp_rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  apply tsum_congr
  intro result
  congr 1
  calc
    _ = ∑' word, weight result *
        (Pr[= word | completeProposalWord (PMF.uniformOfFintype Index) total result.2.1] * payoff word) := by
      apply tsum_congr
      intro word
      ring
    _ = _ := ENNReal.tsum_mul_left

theorem expected_certificateGame_creationCost_le_terminalPotential (adversary : Adversary)
    (budget total : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (hbudget : budget ≤ 2 ^ 127) :
    (∑' result, Pr[= result | certificateGame adversary budget required
      (fun key input state length record => proposalPrefixStop input state length record || stopAfter key input state length record)
      (decide (total < 25313293))] * result.2.2.2.creationCost) ≤
        ∑' result, Pr[= result | certificateGame adversary budget required
          (fun key input state length record => proposalPrefixStop input state length record || stopAfter key input state length record)
          (decide (total < 25313293))] * (result.2.2.2.creationMass *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1) := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  apply mul_le_mul' le_rfl
  have hinv := certificateProposalInvariant_initial generated.1.1.2 total generated.1.2.hashCalls generated.2
    (decide (total < 25313293)) (fun h => Nat.le_of_not_lt (of_decide_eq_false h))
  simpa only [initialCertificateMonitor, zero_add] using
    expected_certificateProposal_creationCost_le_mass_terminalPotential generated.1.1.2 budget total required
      (stopAfter generated.1.1.2) (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls (decide (total < 25313293))) hbudget hinv

theorem expected_certificateTerminalGame_count_le_mass_price (adversary : Adversary)
    (budget total : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (hbudget : budget ≤ 2 ^ 127) :
    (∑' result, Pr[= result | certificateTerminalGame adversary budget required
      (fun key input state length record => proposalPrefixStop input state length record || stopAfter key input state length record)
      (decide (total < 25313293)) total] * certificateBankCount result.1.2.2.2.bank) ≤
        ∑' result, Pr[= result | certificateTerminalGame adversary budget required
          (fun key input state length record => proposalPrefixStop input state length record || stopAfter key input state length record)
          (decide (total < 25313293)) total] * (result.1.2.2.2.creationMass * terminalCertificatePrice required result.2) := by
  rw [expected_certificateTerminalGame_project adversary budget required _ _ total
      (fun result => certificateBankCount result.2.2.2.bank),
    expected_certificateTerminalGame_weight_payoff adversary budget required _ _ total
      (fun result => result.2.2.2.creationMass) (terminalCertificatePrice required)]
  exact (expected_certificateGame_count_le_creationCost adversary budget required _ _).trans
    (expected_certificateGame_creationCost_le_terminalPotential adversary budget total required stopAfter hbudget)

end SphincsSecurity.Concrete
