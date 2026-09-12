import SphincsSecurity.Proof.Ots.OtsContactAllocation
import SphincsSecurity.Proof.Chains.PartialChainLastRow
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem contact_record_consistent {State : Type} [DecidableEq State] {n : Nat}
    (observed : Fin n → State → Option State) (query : Fin n × State) (answer endpoint : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    Contact (record observed query answer) endpoint ↔ Contact observed endpoint ∨ query.1.val + 1 = n ∧ answer = endpoint := by
  by_cases hc : Contact observed endpoint
  · exact iff_of_true (contact_mono (record_extends observed query answer hconsistent) endpoint hc) (Or.inl hc)
  · simpa only [hc, false_or] using contact_record_iff observed query answer endpoint hc

noncomputable def visibleLazyImpl (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF) :
    QueryImpl OracleWorld (StateT (Fin segment.digit.val → Digest → Option Digest) PMF) :=
  (lazyImpl auxiliary).compose (segment.visibleWorldImpl high)

theorem visible_step_contact (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (endpoint : Digest) (trace : OtsContactTrace.Trace) (observed : Fin segment.digit.val → Digest → Option Digest)
    (hseen : OtsContactTrace.Seen segment endpoint trace ↔ Contact observed endpoint)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    OtsContactTrace.Seen segment endpoint (trace * hashObservationTrace input result.1) ↔ Contact result.2 endpoint := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simpa only [hashObservationTrace, mul_one] using hseen
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hparse,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          simpa only [hashObservationTrace, OtsContactTrace.seen_mul, OtsContactTrace.seen_of,
            OtsContactTrace.EntryContact, hparse, reduceCtorEq, false_and, exists_false, or_false] using hseen
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, hanswer, rfl⟩ := hresult
          have hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer := by
            cases hrow : observed query.1 query.2 with
            | none => exact Or.inl rfl
            | some old =>
                rw [hrow, rowLaw, PMF.mem_support_pure_iff] at hanswer
                exact Or.inr (congrArg some hanswer.symm)
          rw [hashObservationTrace, OtsContactTrace.seen_mul, OtsContactTrace.seen_of, hseen,
            contact_record_consistent observed query answer endpoint hconsistent]
          simp only [OtsContactTrace.EntryContact, parse_input, Option.some.injEq, truncate_combine]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨other, rfl, h⟩; exact h
          · intro h; exact ⟨query, rfl, h⟩

theorem visible_pause_contact (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (endpoint : Digest) (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : OtsContactTrace.Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (hseen : OtsContactTrace.Seen segment endpoint trace ↔ Contact observed endpoint)
    (result : (OtsContactTrace.Trace × OracleComp OracleWorld Result) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((simulateQ (segment.visibleLazyImpl high auxiliary)
      (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace)).run observed).support) :
    OtsContactTrace.Seen segment endpoint result.1.1 ↔ Contact result.2 endpoint := by
  apply QueryPause.run_simulation_invariant stop _ (segment.visibleLazyImpl high auxiliary)
    (fun history rows => OtsContactTrace.Seen segment endpoint history ↔ Contact rows endpoint) _
    computation trace observed hseen result hresult
  intro history rows hrows _ input answer hanswer
  exact segment.visible_step_contact high auxiliary endpoint history rows hrows input answer hanswer

theorem visible_step_queryCount (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (trace : OtsContactTrace.Trace) (observed : Fin segment.digit.val → Digest → Option Digest)
    (hcount : queryCount observed ≤ OtsContactTrace.prefixCalls segment trace)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    queryCount result.2 ≤ OtsContactTrace.prefixCalls segment (trace * hashObservationTrace input result.1) := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simpa only [hashObservationTrace, mul_one] using hcount
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hparse,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          rw [OtsContactTrace.prefixCalls_mul]
          exact hcount.trans (Nat.le_add_right _ _)
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          have hselected : segment.Selects (.inr (segment.input query)) := by
            change segment.parse (segment.input query) ≠ none
            rw [parse_input]
            exact Option.some_ne_none query
          have hsingle := OtsContactTrace.prefixCalls_step segment (.inr (segment.input query)) (combine answer (high query)) 1
          simp only [mul_one, if_pos hselected, OtsContactTrace.prefixCalls_one, Nat.add_zero] at hsingle
          rw [OtsContactTrace.prefixCalls_mul, hsingle]
          exact (queryCount_record_le observed query answer).trans (Nat.add_le_add_right hcount 1)

theorem visible_pause_queryCount (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : OtsContactTrace.Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (hcount : queryCount observed ≤ OtsContactTrace.prefixCalls segment trace)
    (result : (OtsContactTrace.Trace × OracleComp OracleWorld Result) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((simulateQ (segment.visibleLazyImpl high auxiliary)
      (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace)).run observed).support) :
    queryCount result.2 ≤ OtsContactTrace.prefixCalls segment result.1.1 := by
  apply QueryPause.run_simulation_invariant stop _ (segment.visibleLazyImpl high auxiliary)
    (fun history rows => queryCount rows ≤ OtsContactTrace.prefixCalls segment history) _
    computation trace observed hcount result hresult
  intro history rows hrows _ input answer hanswer
  exact segment.visible_step_queryCount high auxiliary history rows hrows input answer hanswer

end SphincsSecurity.Concrete.OtsPrefix
