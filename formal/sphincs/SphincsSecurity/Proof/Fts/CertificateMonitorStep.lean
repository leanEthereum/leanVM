import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMonitor
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem expected_certificateLengthImpl_potential_le (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcache, _⟩, hvalid, hcost⟩ := hdata
    rw [certificateMonitorCharge, if_pos hactive]
    cases input with
    | inl world =>
        rw [certificateLengthImpl_world_run, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inl world) state 0 _ hactive,
          signingLogFragment, List.append_nil]
        have hcost' : signingExecutionHashCost (.inl world) ≤ budget - state.2.spent := by
          cases world <;> exact hcost
        have h := expected_originalProposalRecord_world_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - state.2.log.length) required
          (certificateMonitorCoverState state) state.2.bank world
          (fun record => (certificateMonitorUpdate key budget required stopAfter (.inl world) state 0 record).stopped)
          hsigned hcost'
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
    | inr message =>
        rw [certificateLengthImpl_sign_run, if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inr message) state _ _ hactive,
          signingLogFragment, List.length_append, List.length_singleton]
        have hremaining : signatureLimit - (state.2.log.length + 1) + 1 = signatureLimit - state.2.log.length := by
          change state.2.log.length < signatureLimit at hvalid
          omega
        have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache key state.1 state.2.spent
          hcache.spent_le hcache.cache_le hcache.no_deficit message
        have h := expected_lengthBridge_sign_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - (state.2.log.length + 1)) required
          (certificateMonitorCoverState state) state.2.bank message
          (fun result => (certificateMonitorUpdate key budget required stopAfter (.inr message) state result.1 result.2).stopped)
          hsigned hreuse
        rw [hremaining] at h
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero, certificateLengthImpl_inactive_run key budget required stopAfter input state hactive,
      ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [certificateMonitorPotential, bankedTargetEnvelope_stopped]
    rw [ENNReal.tsum_mul_right]
    have hmass : (∑' record, Pr[= record | originalProposalRecord key input state.1]) = 1 := by
      simp only [PMF.probOutput_eq_apply, PMF.tsum_coe]
    rw [hmass, one_mul]
    exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

theorem expected_certificateLengthImpl_of_advance_constant (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (value : ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = value) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) = value := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split <;> rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] <;>
    simp only [hadvance, ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]

theorem expected_certificateLengthImpl_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationCost) =
      state.2.creationCost + certificateMonitorCharge key budget required input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationCost) _ (certificateMonitorUpdate_creationCost key budget required stopAfter input state)

theorem expected_certificateLengthImpl_creationMass (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationMass) =
      state.2.creationMass + certificateMonitorMass key budget input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationMass) _ (certificateMonitorUpdate_creationMass key budget required stopAfter input state)

noncomputable def expectedCertificateCharge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CertificateMonitorState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => charge input state +
      ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
        next result.1 result.2) computation

@[simp] theorem expectedCertificateCharge_pure {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (value : α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (pure value) state = 0 := rfl

theorem expectedCertificateCharge_query_bind {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (OracleSpec.query input >>= next) state =
      charge input state +
        ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
          expectedCertificateCharge key budget required stopAfter charge (next result.1) result.2 := rfl

theorem expected_certificate_accumulator {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (counter : CertificateMonitorState → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state,
      (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
        counter state + charge input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * counter result.2) =
      counter state + expectedCertificateCharge key budget required stopAfter charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      rw [hstep, add_assoc]

theorem expected_certificate_creationCost {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationCost)
    (certificateMonitorCharge key budget required) (expected_certificateLengthImpl_creationCost key budget required stopAfter)
    computation state

theorem expected_certificate_creationMass {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationMass) =
      state.2.creationMass + expectedCertificateCharge key budget required stopAfter (certificateMonitorMass key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationMass)
    (certificateMonitorMass key budget) (expected_certificateLengthImpl_creationMass key budget required stopAfter)
    computation state

theorem expected_certificate_potential_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            (certificateMonitorPotential key budget required result.2 +
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2) :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ = (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            certificateMonitorPotential key budget required result.2) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 := by simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 :=
          add_le_add (expected_certificateLengthImpl_potential_le key budget required stopAfter input state) le_rfl
        _ = _ := by rw [add_assoc]

theorem expected_certificate_count_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateBankCount result.2.2.bank) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  apply le_trans ?_ (expected_certificate_potential_le_initial_add_charge key budget required stopAfter computation state)
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem expected_certificate_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationCost := by
  rw [expected_certificate_creationCost]
  have h := expected_certificate_count_le_initial_add_charge key budget required stopAfter computation
    (cache, initialCertificateMonitor spent stopped)
  rw [certificateMonitorPotential_initial key budget spent required cache stopped hnone, zero_add] at h
  simpa only [initialCertificateMonitor, zero_add] using h

theorem expected_certificateProposal_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationCost := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hcount := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank) hmap
  have hcost := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationCost) hmap
  rw [tsum_probOutput_map_mul] at hcount hcost
  simp only [Prod.map] at hcount hcost
  rw [hcount, hcost]
  exact expected_certificate_count_le_creationCost key budget spent required stopAfter computation cache stopped hnone

end SphincsSecurity.Concrete
