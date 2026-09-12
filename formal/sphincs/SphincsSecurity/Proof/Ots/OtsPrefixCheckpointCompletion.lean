import SphincsSecurity.Proof.Ots.OtsPrefixVisibleCompletion
import SphincsSecurity.Proof.Ots.OtsContactCheckpoint
import SphincsSecurity.Proof.Chains.AdaptiveChainCapContact
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
  (endpoint : Digest) (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
  {Result : Type} (computation : OracleComp OracleWorld Result)

theorem visible_checkpoint_observation
    (middle : ((OtsContactTrace.Trace × OracleComp segment.VisibleWorld Result) × Nat) × (Fin segment.digit.val → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery (QueryPause.run stop
      (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) 1)) (fun _ _ => none)).support)
    (result : ((Result × OtsContactTrace.Trace) × Nat) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery
      (QueryPause.traced (segment.visibleObservationTrace high) middle.1.1.2)) middle.2).support) :
    (OtsContactTrace.Seen segment endpoint middle.1.1.1 ↔ Contact middle.2 endpoint) ∧
    (OtsContactTrace.Seen segment endpoint (middle.1.1.1 * result.1.1.2) ↔ Contact result.2 endpoint) ∧
    queryCount middle.2 ≤ OtsContactTrace.prefixCalls segment middle.1.1.1 ∧
    result.1.2 ≤ OtsContactTrace.prefixCalls segment result.1.1.2 := by
  let paused := QueryPause.run stop (fun input answer history => history * segment.visibleObservationTrace high input answer)
    (simulateQ (segment.visibleWorldImpl high) computation) 1
  have hmiddle' : (middle.1.1, middle.2) ∈ (lazyRun auxiliary paused (fun _ _ => none)).support := by
    have hforget := congrArg (fun program => lazyRun auxiliary program (fun _ _ => none)) (QueryCap.counted_forget IsPrefixQuery paused)
    rw [lazyRun_map] at hforget
    rw [← hforget, PMF.mem_support_map_iff]
    exact ⟨middle, hmiddle, rfl⟩
  have hbefore := segment.lazyRun_visible_pause_observation high auxiliary stop computation 1 (fun _ _ => none) endpoint
    (by simp only [OtsContactTrace.seen_one, Contact, reduceCtorEq, exists_false, and_false])
    (by simp only [queryCount_empty, OtsContactTrace.prefixCalls_one, le_refl]) (middle.1.1, middle.2) hmiddle'
  have hcontinuation : ∃ source : OracleComp OracleWorld Result, middle.1.1.2 = simulateQ (segment.visibleWorldImpl high) source := by
    change (middle.1.1, middle.2) ∈ (lazyRun auxiliary
      (QueryPause.run stop (fun input answer history => history * segment.visibleObservationTrace high input answer)
        (simulateQ (segment.visibleWorldImpl high) computation) 1) (fun _ _ => none)).support at hmiddle'
    rw [lazyRun_visible_pause, PMF.mem_support_map_iff] at hmiddle'
    obtain ⟨source, _, heq⟩ := hmiddle'
    exact ⟨source.1.2, (congrArg (fun output => output.1.2) heq).symm⟩
  have hresult' : (result.1.1, result.2) ∈ (lazyRun auxiliary
      (QueryPause.traced (segment.visibleObservationTrace high) middle.1.1.2) middle.2).support := by
    have hforget := congrArg (fun program => lazyRun auxiliary program middle.2)
      (QueryCap.counted_forget IsPrefixQuery (QueryPause.traced (segment.visibleObservationTrace high) middle.1.1.2))
    rw [lazyRun_map] at hforget
    rw [← hforget, PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  refine ⟨hbefore.1, ?_, hbefore.2, ?_⟩
  · obtain ⟨source, hsource⟩ := hcontinuation
    rw [hsource] at hresult'
    exact segment.visible_traced_contact high auxiliary endpoint source middle.1.1.1 middle.2 hbefore.1 (result.1.1, result.2) hresult'
  · exact segment.visible_traced_queries_le high middle.1.1.2 result.1 (lazyRun_result_mem auxiliary _ middle.2 result hresult)

end SphincsSecurity.Concrete.OtsPrefix
