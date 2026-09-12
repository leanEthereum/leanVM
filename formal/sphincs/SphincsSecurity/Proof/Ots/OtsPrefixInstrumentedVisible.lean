import SphincsSecurity.Proof.Ots.OtsPrefixInstrumentedSeed
import SphincsSecurity.Proof.Ots.OtsPrefixVisible
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable {Result : Type} (segment : OtsPrefix) (observer : FrontierObserver Result) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

noncomputable def visibleInstrumentedSeedGame (endpoint : Digest) : OracleComp segment.VisibleWorld Result :=
  let outside := segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint
  let frontier := segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint
  simulateQ (segment.visibleWorldImpl auxiliary.high) (observer segment.parameter words frontier
    (CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary))

theorem erase_visibleInstrumentedSeedGame (endpoint : Digest) :
    simulateQ (PartialChainEndpoint.eraseAux (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleInstrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) =
    segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [visibleInstrumentedSeedGame, ← QueryImpl.simulateQ_compose, erase_visibleWorldImpl]
  rfl

theorem visibleInstrumentedSeedGame_real :
    PartialChainEndpoint.realRun (fun endpoint => PartialChainEndpoint.extendAux uniformImpl
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleInstrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none) =
    PartialChainEndpoint.realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none) := by
  simpa only [erase_visibleInstrumentedSeedGame] using
    (PartialChainEndpoint.realRun_eraseAux (fun _ => uniformImpl)
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words)
      (segment.visibleInstrumentedSeedGame observer inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none)).symm

end SphincsSecurity.Concrete.OtsPrefix
