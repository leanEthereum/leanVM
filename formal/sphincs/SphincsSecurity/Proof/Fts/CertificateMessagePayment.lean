import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMonitorStep
import SphincsSecurity.Proof.Fts.DigestMessageCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_originalProposalRecord_world_messageCalls (key : SecretKey)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) cache] *
      record.trace.messageCalls.length) = hashQueryCharge (messageHashCharge key.parameter) cache input := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  simp only [signingBoundaryTrace_messageCalls key.parameter input _ cache,
    ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem targetCreationMultiplier_le_expected_messageCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    targetCreationMultiplier key cache input ≤
      ∑' record, Pr[= record | originalProposalRecord key input cache] * record.trace.messageCalls.length := by
  cases input with
  | inl world =>
      rw [expected_originalProposalRecord_world_messageCalls, targetCreationMultiplier]
      cases world with
      | inl sample => simp only [freshWorldTargetHashCost, Nat.cast_zero, hashQueryCharge, Sum.elim_inl, le_refl]
      | inr input =>
          by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input <;>
            simp [freshWorldTargetHashCost, hashQueryCharge, messageHashCharge, hmessage]
          split_ifs <;> norm_num
  | inr message =>
      rw [expected_originalProposalRecord_sign_messageCalls]
      simpa only [targetCreationMultiplier, FtsLeaf, Fintype.card_fin] using
        freshDigestSelection_mass_le_messageCharge key message cache

noncomputable def certificateMonitorMessageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    ∑' record, Pr[= record | originalProposalRecord key input state.1] * record.trace.messageCalls.length
  else 0

theorem certificateMonitorMass_le_messageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    certificateMonitorMass key budget input state ≤ certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simpa only [certificateMonitorMass, certificateMonitorMessageCharge, if_pos hactive] using
      targetCreationMultiplier_le_expected_messageCalls key input state.1
  · simp only [certificateMonitorMass, certificateMonitorMessageCharge, if_neg hactive, le_refl]

theorem expected_certificateLengthImpl_of_record_function (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (weight : ProposalExecutionRecord input → ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = weight record) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
      ∑' record, Pr[= record | originalProposalRecord key input state.1] * weight record := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
      ∑' record, Pr[= record | law] * weight record)
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
    exact h
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]

theorem expected_certificateLengthImpl_messageCalls (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      result.2.2.messageCalls) = state.2.messageCalls + certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [expected_certificateLengthImpl_of_record_function key budget required stopAfter input state
        (fun current => current.2.messageCalls)
        (fun record => (state.2.messageCalls : ENNReal) + record.trace.messageCalls.length)
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_messageCalls key budget required stopAfter input state length record hactive, Nat.cast_add])]
    simp only [certificateMonitorMessageCharge, if_pos hactive, mul_add, ENNReal.tsum_add,
      ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
  · rw [expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
        (fun current => current.2.messageCalls) state.2.messageCalls
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_inactive key budget required stopAfter input state length record hactive])]
    simp only [certificateMonitorMessageCharge, if_neg hactive, add_zero]

theorem expected_certificate_messageCalls {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      result.2.2.messageCalls) = state.2.messageCalls +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorMessageCharge key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.messageCalls)
    (certificateMonitorMessageCharge key budget) (expected_certificateLengthImpl_messageCalls key budget required stopAfter)
    computation state

theorem expectedCertificateCharge_mono {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (first second : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hle : ∀ input state, first input state ≤ second input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter first computation state ≤
      expectedCertificateCharge key budget required stopAfter second computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedCertificateCharge_pure, le_refl]
  | query_bind input next ih =>
      rw [expectedCertificateCharge_query_bind, expectedCertificateCharge_query_bind]
      exact add_le_add (hle input state) (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2))

theorem expected_certificate_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.messageCalls := by
  rw [expected_certificate_creationMass, expected_certificate_messageCalls]
  simp only [initialCertificateMonitor, Nat.cast_zero, zero_add]
  exact expectedCertificateCharge_mono key budget required stopAfter _ _
    (certificateMonitorMass_le_messageCharge key budget) computation _

theorem expected_certificateProposal_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.messageCalls := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hmass := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationMass) hmap
  have hcalls := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * (result.2.2.messageCalls : ENNReal)) hmap
  rw [tsum_probOutput_map_mul] at hmass hcalls
  simp only [Prod.map] at hmass hcalls
  rw [hmass, hcalls]
  exact expected_certificate_creationMass_le_messageCalls key budget spent required stopAfter computation cache stopped

end SphincsSecurity.Concrete
