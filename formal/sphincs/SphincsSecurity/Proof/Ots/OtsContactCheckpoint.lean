import SphincsSecurity.Proof.Ots.OtsPrefixVisibleContact
import SphincsSecurity.Proof.Ots.OtsContactSplit
import SphincsSecurity.Proof.Chains.AdaptiveChainPotential
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
  (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
  {Result : Type} (computation : OracleComp OracleWorld Result) (trace : OtsContactTrace.Trace)
  (observed : Fin segment.digit.val → Digest → Option Digest)

theorem lazyRun_visible_pause :
    lazyRun auxiliary (QueryPause.run stop
      (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) trace) observed =
    ((simulateQ (segment.visibleLazyImpl high auxiliary)
      (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace)).run observed).map
        (fun result => ((result.1.1, simulateQ (segment.visibleWorldImpl high) result.1.2), result.2)) := by
  rw [visible_pause_program, lazyRun_map]
  simp only [lazyRun, visibleLazyImpl, QueryImpl.simulateQ_compose]

theorem lazyRun_visible_pause_observation (endpoint : Digest)
    (hseen : OtsContactTrace.Seen segment endpoint trace ↔ Contact observed endpoint)
    (hcount : queryCount observed ≤ OtsContactTrace.prefixCalls segment trace)
    (result : (OtsContactTrace.Trace × OracleComp segment.VisibleWorld Result) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (lazyRun auxiliary (QueryPause.run stop
      (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) trace) observed).support) :
    (OtsContactTrace.Seen segment endpoint result.1.1 ↔ Contact result.2 endpoint) ∧
      queryCount result.2 ≤ OtsContactTrace.prefixCalls segment result.1.1 := by
  rw [lazyRun_visible_pause, PMF.mem_support_map_iff] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  exact ⟨segment.visible_pause_contact high auxiliary endpoint stop computation trace observed hseen source hsource,
    segment.visible_pause_queryCount high auxiliary stop computation trace observed hcount source hsource⟩

end SphincsSecurity.Concrete.OtsPrefix

namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts

variable (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
  (address : OtsPrefix.ChainAddress)
  (high : (OtsPrefix.atAddress parameter words address).Query → OtsPrefix.High) (auxiliary : QueryImpl OracleWorld PMF)
  {Result : Type} (computation : OracleComp OracleWorld Result)

end SphincsSecurity.Concrete.OtsContactTrace
