import SphincsSecurity.Proof.Ots.OtsPrefixSeedReconstruction
import SphincsSecurity.Proof.Ots.OtsPrefixSimulation
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)

noncomputable def seedGame (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) (adversary : Adversary) : OracleComp segment.World (Bool × SigningBoundaryTrace) :=
  segment.game auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary

theorem seedGame_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) (adversary : Adversary) :
    segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint adversary =
      segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [seedGame, seedGame, seedOracle_replaceSecret, seedFrontier_replaceSecret]

theorem referenceSeedGame_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (hword : referenceFamilyWords selections dummy segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) (adversary : Adversary) :
    let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    referenceFamilyFrontierRest key oracle (canonicalGraphLabels segment.parameter secrets ftsSecret oracle) selections dummy adversary =
      simulateQ (segment.fixedImpl tables)
        (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets 0) ftsSecret
          (referenceFamilyWords selections dummy)
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) adversary) := by
  dsimp only
  rw [seedGame_replaceSecret, seedGame,
    segment.fixedImpl_game tables auxiliary.high _ ftsSecret (referenceFamilyWords selections dummy) (by rw [hword])]
  rw [referenceFamilyFrontierRest, causalFrontierGame_eq,
    segment.referenceSeedFrontier_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables,
    segment.referenceSeedOracle_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables]

end SphincsSecurity.Concrete.OtsPrefix
