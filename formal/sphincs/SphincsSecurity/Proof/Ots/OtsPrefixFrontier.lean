import SphincsSecurity.Proof.Ots.OtsPrefixOracle
import SphincsSecurity.Proof.Ots.CanonicalEncodingSampling
import SphincsSecurity.Proof.Hypertree.FrontierOracleCongruence
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalFrontierValues frontierLayerMessage

def SameChain (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) : Prop :=
  lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chainIdx = segment.chainIdx

instance (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) :
    Decidable (segment.SameChain lay tree leaf chainIdx) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def replaceChain (segment : OtsPrefix) (values : OtsFrontierValues) (value : Digest) : OtsFrontierValues :=
  fun lay tree leaf chainIdx => if segment.SameChain lay tree leaf chainIdx then value else values lay tree leaf chainIdx

theorem parse_other_chain (segment : OtsPrefix) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hother : ¬segment.SameChain lay tree leaf chainIdx) (step : ChainStep) (value : Digest) :
    segment.parse (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) = none := by
  cases hparse : segment.parse (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) with
  | none => rfl
  | some query =>
      have hinput := (segment.parse_some_iff _ query).mp hparse
      have hparts := tweakableHashInput_injective segment.parameter (by trivial) (by trivial) hinput
      have hchains : lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chainIdx = segment.chainIdx ∧
          step = segment.step query.1 := by
        simpa only [input, HashDomain.chain.injEq] using hparts.1
      exact False.elim (hother ⟨hchains.1, hchains.2.1, hchains.2.2.1, hchains.2.2.2.1⟩)

theorem answer_other_chain (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hother : ¬segment.SameChain lay tree leaf chainIdx) (step : ChainStep) (value : Digest) :
    segment.answer tables high outside (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) =
      outside (tweakableHashInput segment.parameter (.chain lay tree leaf chainIdx step) (digestBytes value)) := by
  simp only [answer, segment.parse_other_chain lay tree leaf chainIdx hother step value]

theorem lows_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    segment.lows (segment.answer tables high outside) = tables := by
  funext level value
  rw [lows, answer_input, truncate_combine]

noncomputable def frontierFromEndpoint (segment : OtsPrefix) (outside : QueryImpl HashSpec Id)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint : Digest) : OtsFrontierValues :=
  segment.replaceChain (fun lay tree leaf chainIdx => evalWithAnswerFn outside
    (chainWalk segment.parameter lay tree leaf chainIdx 0 (words lay tree leaf chainIdx).val
      (secrets lay tree leaf chainIdx))) endpoint

theorem frontierFromEndpoint_replaceSecret (segment : OtsPrefix) (outside : QueryImpl HashSpec Id)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.frontierFromEndpoint outside (segment.replaceChain secrets replacement) words endpoint =
      segment.frontierFromEndpoint outside secrets words endpoint := by
  funext lay tree leaf chainIdx
  by_cases h : segment.SameChain lay tree leaf chainIdx <;>
    simp only [frontierFromEndpoint, replaceChain, h, ↓reduceIte]

theorem canonicalFrontierValues_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (root : Digest)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit) :
    canonicalFrontierValues ⟨segment.parameter, root, secrets, ftsSecret⟩ (segment.answer tables high outside) words =
      segment.frontierFromEndpoint outside secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  funext lay tree leaf chainIdx
  rw [canonicalFrontierValues, frontierFromEndpoint, replaceChain]
  by_cases h : segment.SameChain lay tree leaf chainIdx
  · rw [if_pos h]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rw [hword, ← segment.evaluate_lows, segment.lows_answer]
  · rw [if_neg h]
    apply eval_chainWalk_congr_tail
    · have hdigit := (words lay tree leaf chainIdx).isLt
      simp only [chainLength, winternitzBits] at hdigit ⊢
      omega
    · intro step _ value
      exact congrArg truncateHash (segment.answer_other_chain tables high outside lay tree leaf chainIdx h step value)

theorem graphMessage_answer (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (root : Digest)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (position : EncodingPosition) :
    canonicalGraphMessage (canonicalGraphLabels segment.parameter secrets ftsSecret (segment.answer tables high outside)) position =
      evalWithAnswerFn outside (frontierLayerMessage segment.parameter ftsSecret words
        (segment.frontierFromEndpoint outside secrets words
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)))
        (referenceIndex position.lay position.tree position.leafIdx) position.lay) := by
  let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret⟩
  have hfrontier : IsSigningFrontier key (segment.answer tables high outside) words
      (segment.frontierFromEndpoint outside secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx))) := by
    rw [← segment.canonicalFrontierValues_answer tables high outside root secrets ftsSecret words hword]
    exact isSigningFrontier_canonical key _ words
  rw [canonicalGraphMessage_eq key, ← eval_frontierLayerMessage key _ words _ hfrontier]
  exact eval_frontierLayerMessage_eq_of_agree segment.parameter words _ outside
    (segment.answer_agrees_outside words (by rw [hword]) tables high outside) ftsSecret _ _ _

end SphincsSecurity.Concrete.OtsPrefix
