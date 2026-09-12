import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificatePathBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

theorem certificateMonitorUpdate_stopped (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) (hstop : state.2.stopped = true) :
    certificateMonitorUpdate key budget required stopAfter input state length record = state.2 := by
  have hinactive : ¬ CertificateMonitorActive key budget input state := by
    intro hactive
    have h := hactive.1
    rw [hstop] at h
    exact Bool.noConfusion h
  rw [certificateMonitorUpdate_inactive key budget required stopAfter input state length record hinactive]
  rcases state with ⟨cache, log, spent, messageCalls, proposals, creationMass, creationCost, bank, stopped⟩
  change stopped = true at hstop
  subst stopped
  rfl

theorem certificateLength_run_stopped {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState)
    (hstop : state.2.stopped = true) (result : α × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2 = state.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ :=
        certificateLengthImpl_support key budget required stopAfter input state middle hmiddle
      have heq := certificateMonitorUpdate_stopped key budget required stopAfter input state length record hstop
      have hnext : (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          input state length record).2.stopped = true := by
        simpa only [originalProposalAdvance, heq] using hstop
      have htail := ih record.output _ hnext result hr
      simpa only [originalProposalAdvance, heq] using htail

end SphincsSecurity.Concrete
