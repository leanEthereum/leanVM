import SphincsSecurity.Proof.Ots.LayerVerifierWitness
import SphincsSecurity.Proof.Ots.PublicEncodingMatch
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
  (messages : EncodingPosition → Digest) (selections : ReferenceFamily)

def EncodingOutputMatch (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, entry.1 ∈ canonicalEncodingInputs parameter ∧ PublicEncodingMatch.Match parameter messages words selections entry.1 entry.2

theorem equal_word_reference (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (trace : Trace)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some (words lay tree leaf))
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values)) :
    (∃ selected, selections ⟨lay, tree, leaf⟩ = some selected ∧ message = messages ⟨lay, tree, leaf⟩ ∧
      counter = BitVec.ofNat counterBits selected.1.val) ∨ EncodingOutputMatch parameter words messages selections trace := by
  let position : EncodingPosition := ⟨lay, tree, leaf⟩
  let input := tweakableHashInput parameter position.domain (digestBytes message ++ counterBytes counter)
  by_cases hreference : PublicEncodingMatch.referenceInput parameter messages selections position = some input
  · cases hselected : selections position with
    | none => simp only [PublicEncodingMatch.referenceInput, hselected, Option.map_none, reduceCtorEq] at hreference
    | some selected =>
        have hinput : encodingRetryInput parameter position (messages position) selected.1.val = input := by
          simpa only [PublicEncodingMatch.referenceInput, hselected, Option.map_some, Option.some.injEq] using hreference
        have hpayload := (tweakableHashInput_injective parameter (by trivial) (by trivial) hinput).2
        obtain ⟨hm, hc⟩ := List.append_inj hpayload (by simp [digestBytes_length])
        exact Or.inl ⟨selected, rfl, (digestBytes_injective hm).symm, (bytesLE_injective hc).symm⟩
  · refine Or.inr ⟨(input, f input), ?_, ?_, position, ⟨_, rfl⟩, hreference, ?_⟩
    · apply hrun.bind_left
      simp only [encode, queriedInputs_bind, queriedInputs_tweakableHash, queriedInputs_pure,
        List.append_nil, List.mem_singleton, input, position, EncodingPosition.domain]
    · have hcounter : counter.toNat < encodingAttemptLimit := by
        simpa only [encodingAttemptLimit, counterBits] using counter.isLt
      have hin := encodingRetryInput_mem_canonicalEncodingInputs parameter position message ⟨counter.toNat, hcounter⟩
      simpa only [encodingRetryInput, BitVec.ofNat_toNat, BitVec.setWidth_eq, input] using hin
    · exact decode_of_eval_encode_eq_some f parameter lay tree leaf message counter (words lay tree leaf) hencode

theorem layer_reference_classification (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (leaf : LeafIndex) (hleafIndex : leaf.val < 2 ^ layerHeight lay) (path : Nat → Digest)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (candidate : Encoding) (leafValue : Digest) (trace : Trace)
    (hvalid : TargetSum.Valid (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hots : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values) = some leafValue)
    (hfold : foldValue f parameter lay tree leaf path leafValue (layerHeight lay) = honestNode f parameter lay tree secret (layerHeight lay) 0)
    (hotsRun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hfoldRun : ContainsRun f trace (treeFold parameter lay tree leaf path (layerHeight lay) leafValue)) :
    (∃ selected, selections ⟨lay, tree, leaf⟩ = some selected ∧ message = messages ⟨lay, tree, leaf⟩ ∧
      counter = BitVec.ofNat counterBits selected.1.val ∧ candidate = words lay tree leaf ∧
      (∀ index, values index = frontier f parameter words lay tree leaf (secret leaf) index) ∧
      ∀ level, level < layerHeight lay → path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) ∨
      TreeOutputMatch f parameter lay tree secret trace ∨ LeafOutputMatch f parameter lay tree leaf (secret leaf) trace ∨
        ChainException f parameter words lay tree leaf (secret leaf) trace ∨ EncodingOutputMatch parameter words messages selections trace := by
  rcases layer_classification f parameter words lay tree secret leaf hleafIndex path message counter values candidate leafValue trace
      hvalid hencode hots hfold hotsRun hfoldRun with ⟨hword, hvalues, hpath⟩ | ht | hl | hc
  · rw [hword] at hencode
    rcases equal_word_reference f parameter words messages selections lay tree leaf message counter values trace hencode hotsRun
      with ⟨selected, hs, hm, hc⟩ | he
    · exact Or.inl ⟨selected, hs, hm, hc, hword, hvalues, hpath⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl hl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))

end SphincsSecurity.Concrete.OtsVerifierWitness
