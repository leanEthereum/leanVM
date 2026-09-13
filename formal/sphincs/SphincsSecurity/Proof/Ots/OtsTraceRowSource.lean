import SphincsSecurity.Proof.Ots.OtsTraceRows
import SphincsSecurity.Proof.Ots.OtsContactFirstLaw
import SphincsSecurity.Proof.Ots.EncodingMarkerBound
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)

theorem visibleInstrumentedContact_trace (endpoint : Digest) :
    (fun result : ContactResult => (result.output, result.before * result.after)) <$>
      segment.visibleInstrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint =
      QueryPause.traced (segment.visibleObservationTrace auxiliary.high)
        (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) := by
  rw [visibleInstrumentedSeedGame, ← simulateQ_map, contactObserver_trace]
  exact (segment.visible_observation_program auxiliary.high _).symm

theorem instrumentedContact_rows (result : Digest × ContactResult × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ (realRun (fun _ => uniformImpl)
      (fun endpoint => segment.instrumentedSeedGame contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support) :
    RowsObserved segment (result.2.1.before * result.2.1.after) result.2.2 := by
  rw [← segment.visibleInstrumentedSeedGame_real contactObserver inputs hencoding hgraph auxiliary secrets ftsSecret words adversary] at hr
  have hlazy := realRun_support_lazy _ _ _ result hr
  have htrace : ((result.2.1.output, result.2.1.before * result.2.1.after), result.2.2) ∈
      (lazyRun (extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words result.1))
        (QueryPause.traced (segment.visibleObservationTrace auxiliary.high)
          (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary result.1)) (fun _ _ => none)).support := by
    rw [← segment.visibleInstrumentedContact_trace inputs hencoding hgraph auxiliary secrets ftsSecret words adversary, lazyRun_map,
      PMF.mem_support_map_iff]
    exact ⟨result.2, hlazy, rfl⟩
  have h := segment.visible_traced_rows auxiliary.high
    (extendAux uniformImpl (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words result.1))
    (CausalFrontierProgram.game segment.parameter (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words result.1)
      ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words result.1) adversary)
    1 (fun _ _ => none) (rowsObserved_empty segment) _ htrace
  simpa only [one_mul] using h

end SphincsSecurity.Concrete.OtsPrefix
