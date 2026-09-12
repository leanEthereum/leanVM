import SphincsSecurity.Proof.Ots.OtsContactCheckpoint
import SphincsSecurity.Proof.Chains.AdaptiveChainCheckpointProjection
import SphincsSecurity.Proof.Ots.OtsPrefixInstrumentedVisible
import SphincsSecurity.Proof.Ots.TraceCheckpointObserver
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem visible_checkpoint_program (segment : OtsPrefix) (stop : FrontierStop)
    [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (high : segment.Query → High)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type} (computation : OracleComp OracleWorld Result) :
    (do
      let middle ← QueryPause.run (stop segment.parameter words frontier)
        (fun input answer history => history * segment.visibleObservationTrace high input answer)
        (simulateQ (segment.visibleWorldImpl high) computation) 1
      let tail ← QueryPause.traced (segment.visibleObservationTrace high) middle.2
      pure (middle.1, tail)) =
    simulateQ (segment.visibleWorldImpl high) (checkpointSplitRun stop segment.parameter words frontier computation) := by
  have htrace (program : OracleComp OracleWorld Result) :
      QueryPause.traced (segment.visibleObservationTrace high) (simulateQ (segment.visibleWorldImpl high) program) =
        simulateQ (segment.visibleWorldImpl high) (QueryPause.traced hashObservationTrace program) :=
    segment.visible_observation_program high program
  rw [visible_pause_program]
  simp only [bind_map_left, htrace, checkpointSplitRun, simulateQ_bind, simulateQ_pure]

variable (segment : OtsPrefix) (stop : FrontierStop)
  [∀ parameter words frontier, DecidablePred (stop parameter words frontier)] (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

noncomputable def traceCheckpointBefore (endpoint : Digest) :=
  QueryCap.counted IsPrefixQuery (QueryPause.run
    (stop segment.parameter words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint))
    (fun input answer history => history * segment.visibleObservationTrace auxiliary.high input answer)
    (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) 1)

noncomputable def traceCheckpointRun :=
  realCheckpointRun (fun endpoint => extendAux uniformImpl
    (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
    (segment.traceCheckpointBefore stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary)
    (fun _ middle => QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.1.2) (fun _ _ => none)

theorem traceCheckpointRun_project :
    (segment.traceCheckpointRun stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary).map
      (fun result => (result.1,
        (⟨segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1,
          result.2.1.1.1.1, result.2.2.1.1.1, result.2.2.1.1.2⟩ : ContactResult), result.2.2.2)) =
    realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none) := by
  rw [traceCheckpointRun]
  rw [realCheckpointRun_project
    (fun endpoint => extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
    (segment.traceCheckpointBefore stop inputs hencoding hgraph auxiliary secrets ftsSecret words adversary)
    (fun _ middle => QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.1.2)
    (fun _ _ => none)
    (fun endpoint middle tail => (⟨segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint,
      middle.1.1, tail.1, tail.2⟩ : ContactResult))]
  rw [← segment.visibleInstrumentedSeedGame_real (checkpointObserver stop) inputs hencoding hgraph auxiliary secrets ftsSecret words adversary]
  congr 1
  funext endpoint
  let frontier := segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint
  let program := CausalFrontierProgram.game segment.parameter
    (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint) ftsSecret words frontier adversary
  let paused := QueryPause.run (stop segment.parameter words frontier)
    (fun input answer history => history * segment.visibleObservationTrace auxiliary.high input answer)
    (simulateQ (segment.visibleWorldImpl auxiliary.high) program) 1
  let finish := fun middle : OtsContactTrace.Trace × OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) => do
    let tail ← QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.2
    pure (⟨frontier, middle.1, tail.1, tail.2⟩ : ContactResult)
  change (QueryCap.counted IsPrefixQuery paused >>= fun middle => finish middle.1) = _
  have hforget := congrArg (fun computation => computation >>= finish) (QueryCap.counted_forget IsPrefixQuery paused)
  rw [bind_map_left] at hforget
  rw [hforget]
  have hmap : (paused >>= finish) = (fun result => (⟨frontier, result.1, result.2.1, result.2.2⟩ : ContactResult)) <$>
      (do let middle ← paused; let tail ← QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.2; pure (middle.1, tail)) := by
    simp only [map_bind, map_pure, finish]
  rw [hmap]
  rw [show (do let middle ← paused; let tail ← QueryPause.traced (segment.visibleObservationTrace auxiliary.high) middle.2; pure (middle.1, tail)) =
      simulateQ (segment.visibleWorldImpl auxiliary.high) (checkpointSplitRun stop segment.parameter words frontier program) from
        segment.visible_checkpoint_program stop auxiliary.high words frontier program]
  rw [← simulateQ_map]
  rfl

end SphincsSecurity.Concrete.OtsPrefix
