import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ObservedAdaptiveCoverBound
import SphincsSecurity.Proof.Fts.SignerAdmissibleMessage
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem SigningDigestsCached.mono {parameter : PublicParameter} {root : Digest}
    {before after : QueryCache HashSpec} {log : QueryLog SigningSpec}
    (hsigned : SigningDigestsCached parameter before root log) (hcache : before ≤ after) :
    SigningDigestsCached parameter after root log := by
  intro entry hentry signature hresponse
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned entry hentry signature hresponse)
  exact Option.ne_none_iff_exists'.mpr ⟨output, hcache houtput⟩

theorem eligibleSigningView?_cache_stable (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (payload : HashInput) (entry : SigningEntry)
    (hsigned : ∀ signature, entry.2 = some signature →
      messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) ≠ none) :
    eligibleSigningView? (messageAnswers parameter after) root payload entry =
      eligibleSigningView? (messageAnswers parameter before) root payload entry := by
  cases hresponse : entry.2 with
  | none => simp [eligibleSigningView?, hresponse]
  | some signature =>
      obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (hsigned signature hresponse)
      have hafter : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache houtput
      simp [eligibleSigningView?, observedSigningView?, hresponse, houtput, hafter]

theorem SigningDigestsCached.after_signing (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (response : Option Signature) (view : Option FewTimeView)
    (hresult : ((response, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    SigningDigestsCached key.parameter after key.root (log ++ [⟨message, response⟩]) := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before ((response, view), after) hresult
  intro entry hentry signature hresponse
  rcases List.mem_append.mp hentry with hold | hnew
  · exact (hsigned.mono hcache) entry hold signature hresponse
  · obtain rfl := List.mem_singleton.mp hnew
    have hresponse' : response = some signature := hresponse
    rw [hresponse'] at hresult
    obtain ⟨output, houtput, _, _⟩ := signWithView_successful_cached_output key message before after signature view hresult
    exact Option.ne_none_iff_exists'.mpr ⟨output, houtput⟩

end SphincsSecurity.Concrete
