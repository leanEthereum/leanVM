import XmssSecurity.Proof.FirstLaneOracleSimulation
import XmssSecurity.Proof.EncodingOracleSimulation
import XmssSecurity.Proof.RevealProbeOracleSimulation
import XmssSecurity.Proof.CappedEncodingMonitor

open OracleComp OracleSpec

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive ObservedAction (Index : Type) where
  | encoding (action : EncodingMonitor.ObservedAction)
  | chain (action : RevealProbeOracleSimulation.ObservedAction Index)

abbrev ActionTrace (Index : Type) := List (ObservedAction Index)

def ActionTrace.encodingActions : ActionTrace Index → EncodingActionTrace :=
  List.filterMap fun action =>
    match action with
    | .encoding observed => some observed
    | .chain _ => none

def ActionTrace.chainActions : ActionTrace Index →
    RevealProbeOracleSimulation.ActionTrace Index :=
  List.filterMap fun action =>
    match action with
    | .encoding _ => none
    | .chain observed => some observed

def hazardCount : ActionTrace Index → Nat
  | [] => 0
  | .encoding (.query _ _) :: rest => (hazardCount rest).succ
  | .encoding (.sign _ _) :: rest => hazardCount rest
  | .chain (.probe _ _) :: rest => (hazardCount rest).succ
  | .chain (.reveal _ _) :: rest => hazardCount rest

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem ActionTrace.encodingActions_append
    (left right : ActionTrace Index) :
    (left ++ right).encodingActions =
      left.encodingActions ++ right.encodingActions := by
  simp [ActionTrace.encodingActions]

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem ActionTrace.chainActions_append
    (left right : ActionTrace Index) :
    (left ++ right).chainActions =
      left.chainActions ++ right.chainActions := by
  simp [ActionTrace.chainActions]

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem hazardCount_append (left right : ActionTrace Index) :
    hazardCount (left ++ right) = hazardCount left + hazardCount right := by
  induction left with
  | nil => simp [hazardCount]
  | cons action left ih =>
      cases action with
      | encoding action =>
          cases action <;>
            simp [hazardCount, ih, Nat.add_comm,
              Nat.add_left_comm]
      | chain action =>
          cases action <;>
            simp [hazardCount, ih, Nat.add_comm,
              Nat.add_left_comm]

noncomputable def eagerImpl (table : Index → Digest) :
    QueryImpl (World Index) ProbComp := fun input =>
  match input with
  | .uniform n => liftM (unifSpec.query n)
  | .encodingQuery _ => uniformHashOutput
  | .encodingSignAttempt _ => uniformHashOutput
  | .probe _ _ => pure ()
  | .reveal index => pure (table index)

def traceFragment
    (input : (World Index).Domain) (output : (World Index).Range input) :
    ActionTrace Index :=
  match input with
  | .uniform _ => []
  | .encodingQuery leafIndex => [.encoding (.query leafIndex output)]
  | .encodingSignAttempt leafIndex => [.encoding (.sign leafIndex output)]
  | .probe index target => [.chain (.probe index target)]
  | .reveal index => [.chain (.reveal index output)]

noncomputable def eagerTraceImpl (table : Index → Digest) :
    QueryImpl (World Index) (WriterT (ActionTrace Index) ProbComp) :=
  (eagerImpl table).withTraceAppend traceFragment

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_liftProbComp
    (table : Index → Digest) (computation : ProbComp α) :
    (simulateQ (eagerTraceImpl table)
      (liftProbComp (Index := Index) computation)).run =
        (fun result => (result, ([] : ActionTrace Index))) <$> computation := by
  unfold liftProbComp
  rw [← QueryImpl.simulateQ_compose]
  change (simulateQ ((QueryImpl.id' unifSpec).withTraceAppend
    (fun _ _ => ([] : ActionTrace Index))) computation).run = _
  simpa using QueryImpl.run_simulateQ_withTraceAppend_const_empty
    (Log := ActionTrace Index) (QueryImpl.id' unifSpec) computation

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_support_hazardCount_le
    (table : Index → Digest) (computation : OracleComp (World Index) α)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel)
    (result : α × ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (eagerTraceImpl table) computation).run)) :
    hazardCount result.2 ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [hazardCount]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_query_bind, WriterT.run_bind', mem_support_bind_iff]
        at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      cases input with
      | uniform n =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output fuel
            (by simpa [IsHazardQuery] using hbound.2 output) tail htail
      | encodingQuery leafIndex =>
          cases fuel with
          | zero => simp [IsHazardQuery] at hbound
          | succ remaining =>
              simp [eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
              obtain ⟨output, _houtput, rfl⟩ := hhead
              rw [support_map] at htail
              obtain ⟨tail, htail, rfl⟩ := htail
              have htailCount := ih output remaining
                (by simpa [IsHazardQuery] using hbound.2 output) tail htail
              simpa [Prod.map, hazardCount] using Nat.succ_le_succ htailCount
      | encodingSignAttempt leafIndex =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, _houtput, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output fuel
            (by simpa [IsHazardQuery] using hbound.2 output) tail htail
      | probe index target =>
          cases fuel with
          | zero => simp [IsHazardQuery] at hbound
          | succ remaining =>
              simp [eagerTraceImpl, eagerImpl, traceFragment,
                QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
              subst head
              rw [support_map] at htail
              obtain ⟨tail, htail, rfl⟩ := htail
              have htailCount := ih () remaining
                (by simpa [IsHazardQuery] using hbound.2 ()) tail htail
              simpa [Prod.map, hazardCount] using Nat.succ_le_succ htailCount
      | reveal index =>
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          subst head
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih (table index) fuel
            (by simpa [IsHazardQuery] using hbound.2 (table index)) tail htail

def CombinedHit
    (table : Index → Digest) (trace : ActionTrace Index) : Prop :=
  CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      trace.encodingActions = true ∨
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty trace.chainActions = true

noncomputable def eagerExperiment
    (computation : OracleComp (World Index) α) :
    ProbComp ((Index → Digest) × (α × ActionTrace Index)) := do
  let table ← RevealProbeOracleSimulation.eagerTableSample
  let result ← (simulateQ (eagerTraceImpl table) computation).run
  pure (table, result)

def ExperimentHit
    (result : (Index → Digest) × (α × ActionTrace Index)) : Prop :=
  CombinedHit result.1 result.2.2

end XmssSecurity.FirstLaneOracleSimulation
