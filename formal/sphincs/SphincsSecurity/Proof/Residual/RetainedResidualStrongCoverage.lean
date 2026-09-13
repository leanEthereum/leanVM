import SphincsSecurity.Proof.Residual.RetainedResidualSigningHistory
import SphincsSecurity.Proof.Fts.BankedTargetEnvelope
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAfterDigest boundaryEval
set_option backward.isDefEq.respectTransparency false

theorem SigningHistory.digestsCached {key : SecretKey} {oracle : QueryImpl HashSpec Id} {memory : Memory}
    (hhistory : SigningHistory key oracle memory) : SigningDigestsCached key.parameter memory.external.cache key.root memory.log := by
  intro entry hentry signature hsignature
  have hentry' : (⟨entry.1, some signature⟩ : SigningEntry) ∈ memory.log := by
    simpa only [← hsignature] using hentry
  exact (hhistory.entries entry.1 signature hentry').1

theorem SigningHistory.signing_payload_ne {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hhistory : SigningHistory context.key context.oracle memory) (hcompatible : Compatible context memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf)) (forgery : Forgery)
    (hnew : ¬ SigningTranscript.Contains memory.log forgery)
    (hfull : let digest := truncateMessageDigest (context.oracle (signingInput context.key forgery.message forgery.signature))
      FullyHonestOpening context.oracle memory.external.cache context.key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ memory.log) :
    messageDigestPayload context.key.root message signature.randomness ≠
      messageDigestPayload context.key.root forgery.message forgery.signature.randomness := by
  intro heq
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective context.key.root heq
  have hsign := (hhistory.entries message signature hentry).2.2
  dsimp only [signingInput] at hsign
  rw [heq] at hsign
  have hsignature := hcompatible.honest_signature_eq hdummy _ _ forgery.signature signature hfull hsign hrandomness
  exact hnew ⟨⟨message, some signature⟩, hentry, hmessage, congrArg some hsignature⟩

theorem SigningHistory.strong_covered {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hhistory : SigningHistory context.key context.oracle memory) (hcompatible : Compatible context memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf)) (forgery : Forgery)
    (hnew : ¬ SigningTranscript.Contains memory.log forgery)
    (hfull : let digest := truncateMessageDigest (context.oracle (signingInput context.key forgery.message forgery.signature))
      FullyHonestOpening context.oracle memory.external.cache context.key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (hdisclosed : ∀ tree, memory.routing.disclosed (signingView context.key context.oracle forgery.message forgery.signature).1
      tree ((signingView context.key context.oracle forgery.message forgery.signature).2 tree)) :
    CoveredFewTimeView (fixedSigningViews context.key.parameter memory.external.cache context.key.root memory.log
      (signingInput context.key forgery.message forgery.signature)) (signingView context.key context.oracle forgery.message forgery.signature) := by
  intro tree
  obtain ⟨message, signature, hentry, hindex, hleaf⟩ := hhistory.disclosed _ tree _ (hdisclosed tree)
  have hne := hhistory.signing_payload_ne hcompatible hdummy forgery hnew hfull message signature hentry
  have horigin := hhistory.entries message signature hentry
  obtain ⟨answer, hcache⟩ := Option.ne_none_iff_exists'.mp horigin.1
  have hcached : memory.external.cache (signingInput context.key message signature) =
      some (context.oracle (signingInput context.key message signature)) :=
    hcache.trans (congrArg some (hcompatible.cached _ _ hcache))
  obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
  refine ⟨slot, signingView context.key context.oracle message signature, ?_, hindex.symm, hleaf.symm⟩
  change eligibleSigningView? _ _ _ (memory.log.get slot) = _
  rw [hslot]
  simp only [eligibleSigningView?, signingInput,
    payloadOf_tweakableHashInput, Option.bind_eq_bind', Option.bind_some, if_neg hne, observedSigningView?, FtsProbeSimulation.messageAnswers]
  change (memory.external.cache (signingInput context.key message signature) >>= fun answer => pure (hashOutputFewTimeView answer)) = _
  rw [hcached]
  rfl

theorem fixedSourceRun_rest_strong_covered {inputs : Finset HashInput} (context : Context inputs)
    (memory : Memory) (hcompatible : Compatible context memory) (hhistory : SigningHistory context.key context.oracle memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (adversary : Adversary) (forgery : Forgery) (after : Memory)
    (hresult : fixedSourceRun context
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
        memory (some (forgery, true), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.log forgery) :
    Admissible (truncateMessageDigest (context.oracle (signingInput context.key forgery.message forgery.signature))) ∧
      SigningDigestsCached context.key.parameter after.external.cache context.key.root after.log ∧
      CoveredFewTimeView (fixedSigningViews context.key.parameter after.external.cache context.key.root after.log
        (signingInput context.key forgery.message forgery.signature)) (signingView context.key context.oracle forgery.message forgery.signature) := by
  have hcompatible' := fixedSourceRun_compatible context _ memory hcompatible (forgery, true) after hresult
  have hhistory' := fixedSourceRun_signingHistory context _ memory hhistory (forgery, true) after hresult
  obtain ⟨digest, hdigest, _, hadmissible, hfull, hdisclosed⟩ :=
    fixedSourceRun_rest_honest context memory hcompatible hdummy hroot adversary forgery after hresult
  have heval : evalWithAnswerFn context.oracle
      (messageDigest context.key.parameter context.key.root forgery.message forgery.signature.randomness) =
      truncateMessageDigest (context.oracle (signingInput context.key forgery.message forgery.signature)) := by
    simp only [messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rfl
  have hdigest' := hdigest.symm.trans heval
  rw [hdigest'] at hadmissible hfull hdisclosed
  exact ⟨hadmissible, hhistory'.digestsCached, hhistory'.strong_covered hcompatible' hdummy forgery hnew hfull hdisclosed⟩

theorem fixedSourceRun_rest_certificate {inputs : Finset HashInput} (context : Context inputs)
    (memory : Memory) (hcompatible : Compatible context memory) (hhistory : SigningHistory context.key context.oracle memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (adversary : Adversary) (forgery : Forgery) (after : Memory)
    (hresult : fixedSourceRun context
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
        memory (some (forgery, true), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.log forgery) :
    TargetCertificateAt context.key Finset.univ (after.external.cache, after.log)
      (signingInput context.key forgery.message forgery.signature) := by
  obtain ⟨hadmissible, _, hcoverage⟩ :=
    fixedSourceRun_rest_strong_covered context memory hcompatible hhistory hdummy hroot adversary forgery after hresult hnew
  obtain ⟨_, _, hcached, _⟩ := fixedSourceRun_rest_honest context memory hcompatible hdummy hroot adversary forgery after hresult
  have hpresent : after.external.cache (signingInput context.key forgery.message forgery.signature) ≠ none := by
    apply hcached
    change signingInput context.key forgery.message forgery.signature ∈ [signingInput context.key forgery.message forgery.signature]
    exact List.mem_singleton_self _
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hpresent
  have hcompatible' := fixedSourceRun_compatible context _ memory hcompatible (forgery, true) after hresult
  refine ⟨context.oracle (signingInput context.key forgery.message forgery.signature),
    hanswer.trans (congrArg some (hcompatible'.cached _ _ hanswer)), ?_, hadmissible, ?_⟩
  · exact ⟨messageDigestPayload context.key.root forgery.message forgery.signature.randomness, rfl⟩
  · intro tree _
    exact (targetTreeMatchCount_pos_iff _ _ tree).mpr (hcoverage tree)

theorem observedRun_rest_certificate {inputs : Finset HashInput} (context : Context inputs) (adversary : Adversary)
    (hinputs : sourceInputs context.key
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (hhistory : SigningHistory context.key context.oracle state.memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (forgery : Forgery) (after : State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
        (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩))
      state (some (forgery, true), after) ≠ 0)
    (hnew : ¬ SigningTranscript.Contains after.memory.log forgery) :
    TargetCertificateAt context.key Finset.univ (after.memory.external.cache, after.memory.log)
      (signingInput context.key forgery.message forgery.signature) := by
  have h := map_nonzero _ forgetState (some (forgery, true), after) hresult
  rw [observedRun_source_memory context _ hinputs state hcovered hcompatible] at h
  exact fixedSourceRun_rest_certificate context state.memory hcompatible hhistory hdummy hroot adversary forgery after.memory h hnew

end SphincsSecurity.Concrete.RetainedResidual
