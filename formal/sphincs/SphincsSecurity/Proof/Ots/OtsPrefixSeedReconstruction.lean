import SphincsSecurity.Proof.Ots.OtsPrefixFrontier
import SphincsSecurity.Proof.Ots.OtsPrefixRawOracle
import SphincsSecurity.Proof.Ots.OtsPrefixReferenceSeed
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)

noncomputable def encodingFromMessages (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (seed : canonicalEncodingInputs parameter → HashOutput) : canonicalEncodingInputs parameter → HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (Function.uncurry rows) (fun cell => seed cell.val)

noncomputable def seedBaseOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph (fun _ => 0) auxiliary.remaining

noncomputable def seedFrontier (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint : Digest) : OtsFrontierValues :=
  segment.frontierFromEndpoint (segment.seedBaseOracle inputs hencoding hgraph auxiliary) secrets words endpoint

noncomputable def seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : EncodingPosition → Digest :=
  fun position => evalWithAnswerFn (segment.seedBaseOracle inputs hencoding hgraph auxiliary)
    (frontierLayerMessage segment.parameter ftsSecret words
      (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint)
      (referenceIndex position.lay position.tree position.leafIdx) position.lay)

noncomputable def seedEncoding (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : canonicalEncodingInputs segment.parameter → HashOutput :=
  encodingFromMessages segment.parameter (segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    auxiliary.selectedRows auxiliary.encoding

noncomputable def seedOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph
    (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint) auxiliary.remaining

theorem seedFrontier_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedFrontier inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) words endpoint =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint :=
  segment.frontierFromEndpoint_replaceSecret _ secrets words endpoint replacement

theorem seedMessages_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedMessages inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  funext position
  simp only [seedMessages, seedFrontier_replaceSecret]

theorem seedOracle_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedOracle inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  simp only [seedOracle, seedEncoding, seedMessages_replaceSecret]

theorem outsideGraphMessage_eq_seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  funext position
  change canonicalGraphMessage (canonicalGraphLabels segment.parameter secrets ftsSecret
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining)) position = _
  rw [rawAnswer_eq]
  exact segment.graphMessage_answer tables auxiliary.high _ root secrets ftsSecret words hword position

theorem referenceSeedTable_eq_raw (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret⟩ inputs hencoding
        (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary) =
      joinEncodingTable segment.parameter inputs hencoding
        (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)))
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) := by
  change joinEncodingTable segment.parameter inputs hencoding
    (encodingFromMessages segment.parameter
      (outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining))
      auxiliary.selectedRows auxiliary.encoding)
    (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) = _
  rw [segment.outsideGraphMessage_eq_seedMessages inputs hencoding hgraph auxiliary root secrets ftsSecret words hword tables]
  rfl

theorem referenceSeedOracle_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)) =
      segment.answer tables auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx))) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root secrets ftsSecret selections words hword tables]
  exact segment.rawAnswer_eq inputs hencoding hgraph _ tables auxiliary.high auxiliary.remaining

theorem referenceSeedFrontier_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    canonicalGraphFrontier secrets (canonicalGraphLabels segment.parameter secrets ftsSecret
      (finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)))) words =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root secrets ftsSecret selections words hword tables,
    canonicalGraphLabels_joinEncodingTable segment.parameter secrets ftsSecret inputs hencoding hgraph,
    canonicalGraphLabels_frontier segment.parameter secrets ftsSecret _ words root]
  change canonicalFrontierValues ⟨segment.parameter, root, secrets, ftsSecret⟩
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining) words = _
  rw [rawAnswer_eq, segment.canonicalFrontierValues_answer tables auxiliary.high _ root secrets ftsSecret words hword]
  rfl

end SphincsSecurity.Concrete.OtsPrefix
