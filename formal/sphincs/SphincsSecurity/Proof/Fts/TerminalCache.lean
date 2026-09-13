import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Cached
/-!
# Cache witnesses for terminal events

Terminal classifications retain the executions that produced their oracle values. This module turns
those executions into concrete cache events for the probability bounds.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem CachedRun.messageDigest_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {root : Digest}
    {message : Message} {randomness : Randomness}
    (hrun : CachedRun cache f (messageDigest parameter root message randomness)) :
    cache (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness)) ≠ none := by
  apply hrun
  rw [messageDigest]
  apply queriedInputs_mono_bind_left
  change tweakableHashInput parameter .message
      (messageDigestPayload root message randomness) ∈
    [tweakableHashInput parameter .message (messageDigestPayload root message randomness)]
  simp

end SphincsSecurity.Concrete
