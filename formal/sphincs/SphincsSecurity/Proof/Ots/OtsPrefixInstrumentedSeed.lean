import SphincsSecurity.Proof.Reference.ReferenceInstrumentedGame
import SphincsSecurity.Proof.Ots.OtsPrefixSeedGame
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable {Result : Type} (segment : OtsPrefix) (observer : FrontierObserver Result) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)

noncomputable def instrumentedSeedGame (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) (adversary : Adversary) : OracleComp segment.World Result :=
  let outside := segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint
  let frontier := segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint
  simulateQ (segment.worldImpl auxiliary.high outside) (observer segment.parameter words frontier
    (CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary))

theorem instrumentedSeedGame_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) (adversary : Adversary) :
    segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement)
      ftsSecret words endpoint adversary =
    segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  simp only [instrumentedSeedGame, seedOracle_replaceSecret, seedFrontier_replaceSecret]

theorem fixedImpl_world_program (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (computation : OracleComp OracleWorld Result) :
    simulateQ (segment.fixedImpl tables) (simulateQ (segment.worldImpl high outside) computation) =
      simulateQ (fixedHashWorld (segment.answer tables high outside)) computation := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  exact segment.fixedImpl_worldImpl tables high outside input

theorem referenceSeedGame_instrumented (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (hword : referenceFamilyWords selections dummy segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) (adversary : Adversary) :
    let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    referenceInstrumentedRest observer key oracle (canonicalGraphLabels segment.parameter secrets ftsSecret oracle) selections dummy adversary =
      simulateQ (segment.fixedImpl tables) (segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary
        (segment.replaceChain secrets 0) ftsSecret (referenceFamilyWords selections dummy)
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) adversary) := by
  dsimp only
  rw [instrumentedSeedGame_replaceSecret, instrumentedSeedGame, segment.fixedImpl_world_program]
  rw [referenceInstrumentedRest,
    segment.referenceSeedFrontier_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables,
    segment.referenceSeedOracle_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables]
  rw [segment.program_mask_answer tables auxiliary.high _ ftsSecret (referenceFamilyWords selections dummy) (by rw [hword])]

end SphincsSecurity.Concrete.OtsPrefix
