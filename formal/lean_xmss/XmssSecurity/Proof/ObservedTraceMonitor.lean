import XmssSecurity.Proof.RevealTraceReplay
import XmssSecurity.Proof.RunObservedAppend

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity
namespace RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_support_traceAgrees
    (table : Index → Digest) (computation : OracleComp (World Index) α)
    (result : α × ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (eagerTraceImpl table) computation).run)) :
    TraceAgrees table result.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      trivial
  | query_bind input next ih =>
      rw [simulateQ_query_bind, WriterT.run_bind',
        mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases input with
      | uniform n =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output tail htail
      | probe index target =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simp only [List.cons_append]
          exact ih () tail htail
      | reveal index =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          simp only [List.cons_append]
          exact ⟨rfl, ih (table index) tail htail⟩

def advanceObserved
    (table : Index → Digest) :
    AdaptiveRevealMonitor.State Index → ActionTrace Index →
      Option (AdaptiveRevealMonitor.State Index)
  | state, [] =>
      if tableHits state table then none else some state
  | state, .probe index target :: rest =>
      match state.revealed index with
      | some _ => advanceObserved table state rest
      | none => advanceObserved table (state.addPending index target) rest
  | state, .reveal index _ :: rest =>
      match state.revealed index with
      | some _ => advanceObserved table state rest
      | none =>
          if table index ∈ state.pending index then none
          else advanceObserved table (state.install index (table index)) rest

theorem advanceObserved_eq_none_iff_runObserved_eq_true
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index) :
    advanceObserved table state trace = none ↔
      runObserved table state trace = true := by
  induction trace generalizing state with
  | nil =>
      by_cases hhit : tableHits state table <;>
        simp [advanceObserved, runObserved, hhit]
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [advanceObserved, runObserved]
          cases hrevealed : state.revealed index <;> simp [ih]
      | reveal index value =>
          simp only [advanceObserved, runObserved]
          cases hrevealed : state.revealed index with
          | some previous => simp [ih]
          | none =>
              by_cases hhit : table index ∈ state.pending index
              · simp [hhit]
              · simp [hhit, ih]

theorem advanceObserved_eq_none_append
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index)
    (hleft : advanceObserved table state left = none) :
    advanceObserved table state (left ++ right) = none := by
  apply (advanceObserved_eq_none_iff_runObserved_eq_true
    table state (left ++ right)).2
  apply runObserved_append_eq_true_of_prefix table state left right
  exact (advanceObserved_eq_none_iff_runObserved_eq_true
    table state left).1 hleft

theorem advanceObserved_append_of_some
    (table : Index → Digest) (state final : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index)
    (hleft : advanceObserved table state left = some final) :
    advanceObserved table state (left ++ right) =
      advanceObserved table final right := by
  induction left generalizing state final with
  | nil =>
      by_cases hhit : tableHits state table
      · simp [advanceObserved, hhit] at hleft
      · simp [advanceObserved, hhit] at hleft
        subst final
        rfl
  | cons action left ih =>
      cases action with
      | probe index target =>
          simp only [List.cons_append, advanceObserved] at hleft ⊢
          cases hrevealed : state.revealed index with
          | none =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih (state.addPending index target) final hleft
          | some value =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih state final hleft
      | reveal index value =>
          simp only [List.cons_append, advanceObserved] at hleft ⊢
          cases hrevealed : state.revealed index with
          | some previous =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              exact ih state final hleft
          | none =>
              rw [hrevealed] at hleft
              simp only at hleft ⊢
              by_cases hhit : table index ∈ state.pending index
              · simp [hhit] at hleft ⊢
              · rw [if_neg hhit] at hleft ⊢
                exact ih (state.install index (table index)) final hleft

theorem advanceObserved_append
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index)
    (left right : ActionTrace Index) :
    advanceObserved table state (left ++ right) =
      (advanceObserved table state left).bind fun middle =>
        advanceObserved table middle right := by
  cases hleft : advanceObserved table state left with
  | none =>
      rw [advanceObserved_eq_none_append table state left right hleft]
      simp
  | some final =>
      rw [advanceObserved_append_of_some table state final left right hleft]
      simp

theorem advanceObserved_preserves_stateAgrees
    (table : Index → Digest)
    (monitor finalMonitor : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index)
    (hadvance : advanceObserved table monitor trace = some finalMonitor)
    (hagrees : StateAgrees table monitor) :
    StateAgrees table finalMonitor := by
  induction trace generalizing monitor finalMonitor with
  | nil =>
      simp only [advanceObserved] at hadvance
      split at hadvance
      · contradiction
      · exact Option.some.inj hadvance ▸ hagrees
  | cons action rest ih =>
      cases action with
      | probe index target =>
          simp only [advanceObserved] at hadvance
          cases hrevealed : monitor.revealed index with
          | some value =>
              rw [hrevealed] at hadvance
              exact ih monitor finalMonitor hadvance hagrees
          | none =>
              rw [hrevealed] at hadvance
              exact ih (monitor.addPending index target) finalMonitor hadvance
                (hagrees.addPending index target)
      | reveal index value =>
          simp only [advanceObserved] at hadvance
          cases hrevealed : monitor.revealed index with
          | some previous =>
              rw [hrevealed] at hadvance
              exact ih monitor finalMonitor hadvance hagrees
          | none =>
              rw [hrevealed] at hadvance
              by_cases hhit : table index ∈ monitor.pending index
              · simp [hhit] at hadvance
              · apply ih (monitor.install index (table index)) finalMonitor
                  (by simpa [hhit] using hadvance)
                  (hagrees.install index)

theorem advanceObserved_preserves_replayed_reveals
    (table : Index → Digest)
    (monitor finalMonitor : AdaptiveRevealMonitor.State Index)
    (before after : Index → Option Digest) (trace : ActionTrace Index)
    (hadvance : advanceObserved table monitor trace = some finalMonitor)
    (hmonitor : StateAgrees table monitor)
    (hinitial : monitor.revealed = before)
    (hagrees : TraceAgrees table trace)
    (hreplay : ReplaysCausalReveals before trace after) :
    finalMonitor.revealed = after := by
  induction hreplay generalizing monitor finalMonitor with
  | nil revealed =>
      simp only [advanceObserved] at hadvance
      split at hadvance
      · contradiction
      · exact Option.some.inj hadvance |>.symm ▸ hinitial
  | probe initial final index target trace hrest ih =>
      simp only [advanceObserved] at hadvance
      simp only [TraceAgrees] at hagrees
      cases hrevealed : monitor.revealed index with
      | some value =>
          rw [hrevealed] at hadvance
          exact ih monitor finalMonitor hadvance hmonitor hinitial hagrees
      | none =>
          rw [hrevealed] at hadvance
          apply ih (monitor.addPending index target) finalMonitor hadvance
            (hmonitor.addPending index target)
          · simpa [AdaptiveRevealMonitor.State.addPending] using hinitial
          · exact hagrees
  | reveal initial final index value trace changed hchange hrest ih =>
      simp only [advanceObserved] at hadvance
      simp only [TraceAgrees] at hagrees
      cases hrevealed : monitor.revealed index with
      | some previous =>
          rw [hrevealed] at hadvance
          apply ih monitor finalMonitor hadvance hmonitor
          · funext candidate
            by_cases heq : candidate = index
            · subst candidate
              have hprevious := hmonitor index previous hrevealed
              rw [hagrees.1] at hprevious
              rw [hchange.1]
              exact hrevealed.trans (congrArg some hprevious.symm)
            · rw [hchange.2 candidate heq, ← hinitial]
          · exact hagrees.2
      | none =>
          rw [hrevealed] at hadvance
          by_cases hhit : table index ∈ monitor.pending index
          · simp [hhit] at hadvance
          · apply ih (monitor.install index (table index)) finalMonitor
              (by simpa [hrevealed, hhit] using hadvance)
              (hmonitor.install index)
            · funext candidate
              by_cases heq : candidate = index
              · subst candidate
                rw [hchange.1]
                simp [AdaptiveRevealMonitor.State.install, hagrees.1]
              · rw [hchange.2 candidate heq, ← hinitial]
                simp [AdaptiveRevealMonitor.State.install,
                  Function.update_of_ne heq]
            · exact hagrees.2

end RevealProbeOracleSimulation

end XmssSecurity
