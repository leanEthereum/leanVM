import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCacheExceptionPotential
import SphincsSecurity.Proof.Fts.CertificateMonitor
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev CertificateCacheMonitorState := QueryCache HashSpec × (CertificateMonitor × Bool)

def certificateCacheMonitorProject (state : CertificateCacheMonitorState) : CertificateMonitorState :=
  (state.1, state.2.1)

noncomputable def certificateCacheMonitorUpdate (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) : CertificateMonitor × Bool :=
  (certificateMonitorUpdate key budget required stopAfter input (certificateCacheMonitorProject state) length record,
    state.2.2 || decide (CertificateCacheExceptional key state.1) ||
      decide (CertificateCacheExceptional key record.cache))

noncomputable def certificateCacheLengthImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CertificateCacheMonitorState PMF) :=
  originalLengthImpl key (fun state => state.2.1.spent)
    (fun message state => certificateMonitorEnabled key budget message (certificateCacheMonitorProject state))
    (certificateCacheMonitorUpdate key budget required stopAfter)

noncomputable def certificateCacheProposalImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × CertificateCacheMonitorState) PMF) :=
  originalProposalImpl key (fun state => state.2.1.spent)
    (fun message state => certificateMonitorEnabled key budget message (certificateCacheMonitorProject state))
    (certificateCacheMonitorUpdate key budget required stopAfter)

theorem certificateCacheLengthImpl_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState) :
    Prod.map id certificateCacheMonitorProject <$>
      (certificateCacheLengthImpl key budget required stopAfter input).run state =
        (certificateLengthImpl key budget required stopAfter input).run (certificateCacheMonitorProject state) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateCacheLengthImpl, certificateLengthImpl, originalLengthImpl, lengthRecordImpl,
        StateT.run_mk, originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateCacheLengthImpl, certificateLengthImpl, originalLengthImpl, lengthRecordImpl,
        StateT.run_mk, originalProposalActive, certificateCacheMonitorProject]
      split <;> simp only [PMF.map_comp] <;> rfl

theorem simulateQ_certificateCacheLengthImpl_project {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateCacheMonitorState) :
    Prod.map id certificateCacheMonitorProject <$>
      (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state =
        (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
          (certificateCacheMonitorProject state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ certificateCacheMonitorProject
    (certificateCacheLengthImpl_project key budget required stopAfter) computation state

theorem simulateQ_certificateCacheProposalImpl_length {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateCacheMonitorState) :
    Prod.map id Prod.snd <$>
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state =
        (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state.2 :=
  simulateQ_originalProposalImpl_length key _ _ _ computation state

theorem certificateCacheProposalImpl_project (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateCacheMonitorState) :
    Prod.map id (Prod.map id certificateCacheMonitorProject) <$>
      (certificateCacheProposalImpl key budget required stopAfter input).run state =
        (certificateProposalImpl key budget required stopAfter input).run
          (state.1, certificateCacheMonitorProject state.2) := by
  change PMF.map _ _ = _
  cases input with
  | inl world =>
      simp only [certificateCacheProposalImpl, certificateProposalImpl, originalProposalImpl, proposalRecordImpl,
        StateT.run_mk, originalProposalActive, Bool.false_eq_true, if_false, PMF.map_comp]
      rfl
  | inr message =>
      simp only [certificateCacheProposalImpl, certificateProposalImpl, originalProposalImpl, proposalRecordImpl,
        StateT.run_mk, originalProposalActive, originalRejectedProposal, certificateCacheMonitorProject]
      split <;> simp only [PMF.map_comp] <;> rfl

theorem simulateQ_certificateCacheProposalImpl_project {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateCacheMonitorState) :
    Prod.map id (Prod.map id certificateCacheMonitorProject) <$>
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state =
        (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
          (state.1, certificateCacheMonitorProject state.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map id certificateCacheMonitorProject)
    (certificateCacheProposalImpl_project key budget required stopAfter) computation state

end SphincsSecurity.Concrete
