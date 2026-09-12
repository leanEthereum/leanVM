import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalPrefixStop
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable

def ProposalPrefixExceptional (proposals completed : Nat) : Prop :=
  targetProposalOverhead * completed + 131072 < (proposals : ENNReal)

theorem proposalPrefixStop_eq_after_exception (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    proposalPrefixStop input state length record =
      decide (ProposalPrefixExceptional
        (certificateMonitorUpdate key budget required stopAfter input state length record).proposals
        (certificateMonitorUpdate key budget required stopAfter input state length record).log.length) := by
  simp only [proposalPrefixStop, ProposalPrefixExceptional, certificateMonitorUpdate, if_pos hactive,
    proposalRecordLogState]

end SphincsSecurity.Concrete
