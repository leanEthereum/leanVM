import SphincsSecurity.Proof.Fts.CertificateMessagePayment
import SphincsSecurity.Proof.Fts.OriginalProposalBudget
import SphincsSecurity.Proof.Fts.CertificateCacheMonitor
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem probOutput_probCompLift {Result : Type} (computation : ProbComp Result) (result : Result) :
    Pr[= result | (liftM computation : PMF Result)] = Pr[= result | computation] := rfl

theorem certificateLengthImpl_original_cache (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (fun result => (result.1, result.2.1)) <$> (certificateLengthImpl key budget required stopAfter input).run state =
      (liftM ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1) : PMF _) := by
  have h := simulateQ_originalLengthImpl_forget key (fun current => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) (OracleSpec.query input) state
  simp only [simulateQ_spec_query, ← originalProposalRecord_project] at h
  have hb := congrArg (Functor.map (fun result => (result.1.1, result.2))) (originalProposalRecord_boundary key input state.1)
  simp only [← PMF.monad_map_eq_map, Functor.map_map, ← liftM_map (m := ProbComp) (n := PMF), boundaryRun_forget] at hb
  exact h.trans hb

theorem certificateMonitorMessageCharge_le_original (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    certificateMonitorMessageCharge key budget input state ≤
      expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) state.1 := by
  have h := congrArg (fun law => ∑' result, Pr[= result | law] * (result.1.2.messageCalls.length : ENNReal))
    (originalProposalRecord_boundary key input state.1)
  simp only [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, probOutput_probCompLift] at h
  rw [certificateMonitorMessageCharge]
  split_ifs
  · exact h.le
  · exact bot_le

theorem expectedCertificateMessageCharge_le_original {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter (certificateMonitorMessageCharge key budget) computation state ≤
      expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedCertificateCharge_pure, simulateQ_pure, expectedBoundaryMessageCalls_pure, le_refl]
  | query_bind input next ih =>
      rw [expectedCertificateCharge_query_bind, simulateQ_bind, simulateQ_spec_query, expectedBoundaryMessageCalls_bind]
      apply add_le_add (certificateMonitorMessageCharge_le_original key budget input state)
      have h := congrArg (fun law => ∑' result, Pr[= result | law] *
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2)
        (certificateLengthImpl_original_cache key budget required stopAfter input state)
      simp only [tsum_probOutput_map_mul, probOutput_probCompLift] at h
      calc
        _ ≤ ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1 :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ = _ := h

theorem expected_certificateLength_messageCalls_le_original {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      (result.2.2.messageCalls : ENNReal)) ≤ (state.2.messageCalls : ENNReal) +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 := by
  rw [expected_certificate_messageCalls]
  exact add_le_add le_rfl (expectedCertificateMessageCharge_le_original key budget required stopAfter computation state)

theorem expected_certificateCacheProposal_messageCalls_le_original {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : List Index × CertificateCacheMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state] *
      (result.2.2.2.1.messageCalls : ENNReal)) ≤ (state.2.2.1.messageCalls : ENNReal) +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.2.1 := by
  have h := expected_certificateLength_messageCalls_le_original key budget required stopAfter computation
    (certificateCacheMonitorProject state.2)
  rw [← simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    (state.1, certificateCacheMonitorProject state.2), tsum_probOutput_map_mul] at h
  rw [← simulateQ_certificateCacheProposalImpl_project key budget required stopAfter computation state, tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete
