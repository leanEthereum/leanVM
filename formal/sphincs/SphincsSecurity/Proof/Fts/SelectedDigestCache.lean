import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeSignerView
import SphincsSecurity.Proof.Fts.SignerDigestSource
import SphincsSecurity.Proof.Fts.TerminalCache
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_selected_cached_output (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = selectedFewTimeView index leaves := by
  have hreplay := replayRom_of_mem_support (signDigestLoop attempts key message) before
    (some (randomness, index, leaves)) after hloop (fromCache after) (agreesWithFn_fromCache after)
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message attempts randomness index leaves
    before after after hreplay le_rfl (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, houtput, hdigest ▸ hadmissible, ?_⟩
  simp only [hashOutputFewTimeView, selectedFewTimeView, ← hdigest, hindex, hleaves]

theorem signAfterDigest_message_cache_eq (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (before after : QueryCache HashSpec) (signature : Option Signature)
    (hfinish : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) (payload : HashInput) :
    after (tweakableHashInput key.parameter .message payload) = before (tweakableHashInput key.parameter .message payload) := by
  cases hbefore : before (tweakableHashInput key.parameter .message payload) with
  | none => exact signAfterDigest_cache_message_none key randomness index leaves before after signature hfinish payload hbefore
  | some output =>
      have hcache : before ≤ after :=
        (replay_of_mem_support (signAfterDigest key randomness index leaves) before signature after hfinish
          (fromCache after) (agreesWithFn_fromCache after)).1
      exact hcache hbefore

end SphincsSecurity.Concrete
