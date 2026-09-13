import SphincsSecurity.Proof.Ots.OtsVerifierWitness
import SphincsSecurity.Proof.Hypertree.TreeFoldBound
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk canonicalPayloadInputs

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
  (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)

def TreeOutputMatch (trace : Trace) : Prop :=
  ∃ (level nodeIdx : Nat) (payload : HashInput), payload ∈ canonicalPayloadInputs ∧ level < layerHeight lay ∧ nodeIdx < 2 ^ maxLayerHeight ∧
    2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight ∧
    (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload,
      f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload)) ∈ trace.toList ∧
    NodeHit f parameter lay tree secret level nodeIdx payload

theorem canonicalLeaf_eq_honestNode (leaf : LeafIndex) :
    canonicalLeaf f parameter lay tree leaf (secret leaf) = honestNode f parameter lay tree secret 0 leaf.val := by
  rw [honestNode_zero_eq_leafHash]
  simp only [canonicalLeaf, leafHash, eval_tweakableHash]
  rfl

theorem layer_classification (leaf : LeafIndex) (hleafIndex : leaf.val < 2 ^ layerHeight lay)
    (path : Nat → Digest) (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (candidate : Encoding) (leafValue : Digest) (trace : Trace) (hvalid : TargetSum.Valid (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some candidate)
    (hots : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values) = some leafValue)
    (hfold : foldValue f parameter lay tree leaf path leafValue (layerHeight lay) =
      honestNode f parameter lay tree secret (layerHeight lay) 0)
    (hotsRun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hfoldRun : ContainsRun f trace (treeFold parameter lay tree leaf path (layerHeight lay) leafValue)) :
    (candidate = words lay tree leaf ∧
      (∀ index, values index = frontier f parameter words lay tree leaf (secret leaf) index) ∧
      ∀ level, level < layerHeight lay → path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) ∨
      TreeOutputMatch f parameter lay tree secret trace ∨ LeafOutputMatch f parameter lay tree leaf (secret leaf) trace ∨
        ChainException f parameter words lay tree leaf (secret leaf) trace := by
  have hroot : foldValue f parameter lay tree leaf path leafValue (layerHeight lay) =
      honestNode f parameter lay tree secret (layerHeight lay) (leaf.val / 2 ^ layerHeight lay) := by
    simpa only [Nat.div_eq_of_lt hleafIndex] using hfold
  rcases treeFold_extract f parameter lay tree secret leaf path leafValue (layerHeight lay) hroot with ⟨hleaf, hpath⟩ | ⟨level, hl, hh⟩
  · have hcanonical : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values) =
        some (canonicalLeaf f parameter lay tree leaf (secret leaf)) := by
      rw [canonicalLeaf_eq_honestNode, hots, hleaf]
    rcases otsLeaf_classification f parameter words lay tree leaf (secret leaf) message counter values candidate trace hvalid hencode hotsRun hcanonical
      with ⟨hword, hvalues⟩ | hleafMatch | hchains
    · exact Or.inl ⟨hword, hvalues, hpath⟩
    · exact Or.inr (Or.inr (Or.inl hleafMatch))
    · exact Or.inr (Or.inr (Or.inr hchains))
  · refine Or.inr (Or.inl ⟨level, leaf.val / 2 ^ (level + 1), _, orderedPayload_mem_canonicalPayloadInputs _ _ _, hl, ?_, ?_, ?_, hh⟩)
    · exact (Nat.div_le_self _ _).trans_lt leaf.isLt
    · exact fold_node_bound maxLayerHeight level leaf.val (hl.trans_le (layerHeight_le lay)) leaf.isLt
    · exact hfoldRun _ (treeFold_query_mem f parameter lay tree leaf path leafValue (layerHeight lay) level hl)

end SphincsSecurity.Concrete.OtsVerifierWitness
