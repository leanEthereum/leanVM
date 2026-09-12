import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.NoMessage
/-!
# Message inputs inserted by a signer

The signer's only message-domain hash calls are the attempts in its digest loop. Once one attempt is
admissible the rest of signing avoids that domain entirely.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

@[simp] theorem queriedInputs_signAttempt (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    queriedInputs f (signAttempt secretKey message randomness) =
      [tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)] := by
  rw [signAttempt, queriedInputs_bind]
  change queriedInputs f
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))) >>=
          fun answer => pure (truncateMessageDigest answer)) ++ _ = _
  rw [queriedInputs_query_bind, queriedInputs_pure]
  split <;> simp

theorem signAttempt_cache_other_none (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (IndexGroup → FtsLeaf)))
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run beforeCache))
    (target : HashInput) (hbefore : beforeCache target = none)
    (hne : target ≠ tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) :
    afterCache target = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem f hf target hbefore
  simp [hne]

theorem signAfterDigest_cache_message_none (secretKey : SecretKey)
    (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest secretKey randomness index leaves)).run beforeCache))
    (payload : HashInput) (hbefore : beforeCache
      (tweakableHashInput secretKey.parameter .message payload) = none) :
    afterCache (tweakableHashInput secretKey.parameter .message payload) = none := by
  obtain ⟨answerFn, hagree⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAfterDigest secretKey randomness index leaves) beforeCache result afterCache
      hmem answerFn hagree _ hbefore
  exact avoidsMessage_signAfterDigest answerFn secretKey randomness index leaves payload

end SphincsSecurity.Concrete
