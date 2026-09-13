import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeSignerView
import SphincsSecurity.Proof.Fts.MessagePrehit
import SphincsSecurity.Proof.Fts.SignerDigestSource
import SphincsSecurity.Proof.Fts.TerminalCache
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem signWithView_successful_cached_output (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Signature) (view : Option FewTimeView)
    (hresult : ((some signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message signature.randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ view = some (hashOutputFewTimeView output) := by
  obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, hview⟩ :=
    signWithView_support_some key message before after signature view hresult
  have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loopCache after signature hfinish
  have hloopLe : loopCache ≤ after :=
    (replay_of_mem_support (signAfterDigest key randomness index leaves) loopCache (some signature) after hfinish
      (fromCache after) (agreesWithFn_fromCache after)).1
  have hf : loopCache.AgreesWithFn (fromCache after) := fun _ _ h => agreesWithFn_fromCache after (hloopLe h)
  have hreplay := replayRom_of_mem_support (signDigestLoop digestAttemptLimit key message) before
    (some (randomness, index, leaves)) loopCache hloop (fromCache after) hf
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message digestAttemptLimit randomness index leaves
    before loopCache after hreplay hloopLe (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, ?_, hdigest ▸ hadmissible, ?_⟩
  · rw [hrandomness]
    exact houtput
  · simpa only [selectedFewTimeView, hindex, hleaves, hdigest, hashOutputFewTimeView] using hview

theorem signDigestLoop_new_admissible_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)))
    (hresult : (result, after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    ∃ randomness index leaves, result = some (randomness, index, leaves) ∧
      payload = messageDigestPayload key.root message randomness := by
  induction attempts generalizing before after result with
  | zero =>
      have heq : (result, after) = (none, before) := by
        simpa only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hresult
      have hcache : after = before := congrArg Prod.snd heq
      rw [hcache, hbefore] at hafter
      contradiction
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hresult
      obtain ⟨sampled, _, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          simp only [signDigestLoopContinuation] at hfinish
          by_cases hsame : payload = messageDigestPayload key.root message sampled
          · have hle := simulateQ_romImpl_cache_le (signDigestLoop attempts key message) attemptCache (result, after) hfinish
            have heval := (replay_of_mem_support_of_le (signAttempt key message sampled) before none attemptCache after hattempt hle
              (fromCache after) (agreesWithFn_fromCache after)).1
            have hanswer : fromCache after (tweakableHashInput key.parameter .message
                (messageDigestPayload key.root message sampled)) = output :=
              agreesWithFn_fromCache after (hsame ▸ hafter)
            simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
              hanswer, evalWithAnswerFn_pure, hadmissible, if_pos] at heval
            exact False.elim (by simp only [reduceCtorEq] at heval)
          · have hnone := signAttempt_cache_other_none key message sampled before attemptCache none hattempt
              (tweakableHashInput key.parameter .message payload) hbefore (fun h =>
                hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) h).2)
            exact ih attemptCache after result hfinish hnone hafter
      | some selected =>
          obtain ⟨index, leaves⟩ := selected
          have heq : (result, after) = (some (sampled, index, leaves), attemptCache) := by
            simpa only [signDigestLoopContinuation, support_pure, Set.mem_singleton_iff] using hfinish
          by_cases hsame : payload = messageDigestPayload key.root message sampled
          · exact ⟨sampled, index, leaves, congrArg Prod.fst heq, hsame⟩
          · have hnone := signAttempt_cache_other_none key message sampled before attemptCache (some (index, leaves)) hattempt
              (tweakableHashInput key.parameter .message payload) hbefore (fun h =>
                hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) h).2)
            have hcache : after = attemptCache := congrArg Prod.snd heq
            rw [hcache, hnone] at hafter
            exact False.elim (by simp only [reduceCtorEq] at hafter)

end SphincsSecurity.Concrete
