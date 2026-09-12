import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateCacheExceptionGame
import SphincsSecurity.Proof.Fts.CertificateProposalPrefixException
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

def CertificateGameExceptional (result : CertificateCacheGameResult) : Prop :=
  result.2.2.2.2 = true ∨
    ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length

theorem expected_certificateCacheGame_project (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (weight : CertificateGameResult → ENNReal) :
    (∑' result, Pr[= result | certificateCacheGame adversary budget required stopAfter stopped] *
      weight (certificateCacheGameProject result)) =
        ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * weight result := by
  have h := congrArg (fun law : PMF CertificateGameResult => ∑' result, Pr[= result | law] * weight result)
    (certificateCacheGame_project adversary budget required stopAfter stopped)
  rw [tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete
