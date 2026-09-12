import SphincsSecurity.Proof.Ots.OtsPrefixVisibleContact
import SphincsSecurity.Proof.Base.QueryTraceInvariant
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem visible_traced_contact (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (endpoint : Digest) {Result : Type} (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (hseen : OtsContactTrace.Seen segment endpoint history ↔ Contact observed endpoint)
    (result : (Result × OtsContactTrace.Trace) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ (lazyRun auxiliary (QueryPause.traced (segment.visibleObservationTrace high)
      (simulateQ (segment.visibleWorldImpl high) computation)) observed).support) :
    OtsContactTrace.Seen segment endpoint (history * result.1.2) ↔ Contact result.2 endpoint := by
  have htrace : QueryPause.traced (segment.visibleObservationTrace high) (simulateQ (segment.visibleWorldImpl high) computation) =
      simulateQ (segment.visibleWorldImpl high) (QueryPause.traced hashObservationTrace computation) :=
    segment.visible_observation_program high computation
  rw [htrace, lazyRun, ← QueryImpl.simulateQ_compose] at hresult
  apply QueryPause.traced_simulation_invariant hashObservationTrace (segment.visibleLazyImpl high auxiliary)
    (fun trace rows => OtsContactTrace.Seen segment endpoint trace ↔ Contact rows endpoint) _
    computation history observed hseen result hresult
  intro trace rows hrows input answer hanswer
  exact segment.visible_step_contact high auxiliary endpoint trace rows hrows input answer hanswer

theorem visible_traced_queries_le (segment : OtsPrefix) (high : segment.Query → High)
    {Result : Type} (computation : OracleComp segment.VisibleWorld Result)
    (result : (Result × OtsContactTrace.Trace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsPrefixQuery (QueryPause.traced (segment.visibleObservationTrace high) computation))) :
    result.2 ≤ OtsContactTrace.prefixCalls segment result.1.2 := by
  apply QueryPause.traced_counted_le (segment.visibleObservationTrace high) IsPrefixQuery (OtsContactTrace.prefixCalls segment)
    (OtsContactTrace.prefixCalls_mul segment) _ computation result hresult
  intro input answer
  cases input with
  | inl input => simp only [IsPrefixQuery, if_false, Nat.zero_le]
  | inr query =>
      have hs : segment.Selects (.inr (segment.input query)) := by
        change segment.parse (segment.input query) ≠ none
        rw [parse_input]
        exact Option.some_ne_none query
      have h := OtsContactTrace.prefixCalls_step segment (.inr (segment.input query)) (combine answer (high query)) 1
      simpa only [hashObservationTrace, visibleObservationTrace, mul_one, if_pos hs,
        OtsContactTrace.prefixCalls_one, Nat.add_zero, IsPrefixQuery, if_true] using le_of_eq h.symm

end SphincsSecurity.Concrete.OtsPrefix
