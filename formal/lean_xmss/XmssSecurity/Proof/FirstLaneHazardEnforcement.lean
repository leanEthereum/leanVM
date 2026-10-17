import XmssSecurity.Proof.FirstLaneEagerSimulation
import XmssSecurity.Proof.RunObservedAppend

open OracleComp OracleSpec

namespace QueryImpl

theorem simulateQ_stateHandler_trace
    {ι : Type} {spec : OracleSpec ι}
    {Log State : Type}
    [EmptyCollection Log] [Append Log] [LawfulAppend Log]
    (eager : QueryImpl spec (WriterT Log ProbComp))
    (handler : QueryImpl spec (StateT State (OracleComp spec)))
    (advance : State → Log → State)
    (project : State → Log → Log)
    (advance_empty : ∀ state, advance state ∅ = state)
    (advance_append : ∀ state left right,
      advance state (left ++ right) = advance (advance state left) right)
    (project_empty : ∀ state, project state ∅ = ∅)
    (project_append : ∀ state left right,
      project state (left ++ right) =
        project state left ++ project (advance state left) right)
    (hquery : ∀ input state,
      (simulateQ eager ((handler input).run state)).run =
        (fun result =>
          ((result.1, advance state result.2), project state result.2)) <$>
          (simulateQ eager (liftM (spec.query input))).run)
    (computation : OracleComp spec α) (state : State) :
    (simulateQ eager ((simulateQ handler computation).run state)).run =
      (fun result =>
        ((result.1, advance state result.2), project state result.2)) <$>
        (simulateQ eager computation).run := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp [advance_empty, project_empty]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      rw [simulateQ_bind, WriterT.run_bind']
      change (do
        let head ← (simulateQ eager ((handler input).run state)).run
        (Prod.map id fun tail => head.2 ++ tail) <$>
          ((simulateQ (eager.mapStateTBase handler) (next head.1.1)).run
            head.1.2).run) = _
      rw [hquery input state]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      rw [WriterT.run_bind']
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply bind_congr
      intro head
      rw [ih head.1 (advance state head.2)]
      simp [advance_append, project_append, Prod.map]

end QueryImpl

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def hazardEnforcementImpl :
    QueryImpl (World Index) (StateT Nat (OracleComp (World Index))) :=
  fun input fuel =>
    match input with
    | .uniform n => do
        let output ← uniformQuery n
        pure (output, fuel)
    | .encodingQuery leafIndex =>
        match fuel with
        | 0 => do
            let output ← liftProbComp uniformHashOutput
            pure (output, 0)
        | remaining + 1 => do
            let output ← encodingQuery leafIndex
            pure (output, remaining)
    | .encodingSignAttempt leafIndex => do
        let output ← encodingSignAttemptQuery leafIndex
        pure (output, fuel)
    | .probe index target =>
        match fuel with
        | 0 => pure ((), 0)
        | remaining + 1 => do
            probeQuery index target
            pure ((), remaining)
    | .reveal index => do
        let value ← revealQuery index
        pure (value, fuel)

noncomputable def enforceHazardBound
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) α :=
  Prod.fst <$> (simulateQ hazardEnforcementImpl computation).run fuel

omit [Fintype Index] [DecidableEq Index] in
theorem liftProbComp_isHazardQueryBoundP (computation : ProbComp α) :
    (liftProbComp (Index := Index) computation).IsQueryBoundP
      IsHazardQuery 0 := by
  unfold liftProbComp
  apply OracleComp.IsQueryBoundP.simulateQ_of_step
    (p := fun _ : unifSpec.Domain => False)
    (q := IsHazardQuery)
    (OracleComp.isQueryBoundP_false computation 0)
  · intro input hfalse
    exact hfalse.elim
  · intro input _
    change (uniformQuery (Index := Index) input).IsQueryBoundP
      IsHazardQuery 0
    rw [uniformQuery, OracleComp.isQueryBoundP_query_iff]
    simp [IsHazardQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_hazardEnforcementImpl_run_isHazardQueryBoundP
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ hazardEnforcementImpl computation).run fuel |>.IsQueryBoundP
      IsHazardQuery fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure result => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      cases input with
      | uniform n =>
          change (uniformQuery n >>= fun output =>
            (simulateQ hazardEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro output
            simpa [IsHazardQuery] using ih output fuel
      | encodingQuery leafIndex =>
          cases fuel with
          | zero =>
              change (liftProbComp uniformHashOutput >>= fun output =>
                (simulateQ hazardEnforcementImpl (next output)).run 0)
                  |>.IsQueryBoundP IsHazardQuery 0
              apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
                (liftProbComp_isHazardQueryBoundP uniformHashOutput)
              intro output _
              exact ih output 0
          | succ remaining =>
              change (encodingQuery leafIndex >>= fun output =>
                (simulateQ hazardEnforcementImpl (next output)).run remaining)
                  |>.IsQueryBoundP IsHazardQuery (remaining + 1)
              rw [encodingQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsHazardQuery]
              · intro output
                simpa [IsHazardQuery] using ih output remaining
      | encodingSignAttempt leafIndex =>
          change (encodingSignAttemptQuery leafIndex >>= fun output =>
            (simulateQ hazardEnforcementImpl (next output)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [encodingSignAttemptQuery,
            OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro output
            simpa [IsHazardQuery] using ih output fuel
      | probe index target =>
          cases fuel with
          | zero =>
              change (simulateQ hazardEnforcementImpl (next ())).run 0
                |>.IsQueryBoundP IsHazardQuery 0
              exact ih () 0
          | succ remaining =>
              change (probeQuery index target >>= fun _ =>
                (simulateQ hazardEnforcementImpl (next ())).run remaining)
                  |>.IsQueryBoundP IsHazardQuery (remaining + 1)
              rw [probeQuery, OracleComp.isQueryBoundP_query_bind_iff]
              constructor
              · simp [IsHazardQuery]
              · intro _
                simpa [IsHazardQuery] using ih () remaining
      | reveal index =>
          change (revealQuery index >>= fun value =>
            (simulateQ hazardEnforcementImpl (next value)).run fuel)
              |>.IsQueryBoundP IsHazardQuery fuel
          rw [revealQuery, OracleComp.isQueryBoundP_query_bind_iff]
          constructor
          · simp [IsHazardQuery]
          · intro value
            simpa [IsHazardQuery] using ih value fuel

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardBound_isHazardQueryBoundP
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    (enforceHazardBound fuel computation).IsQueryBoundP IsHazardQuery fuel := by
  unfold enforceHazardBound
  apply (OracleComp.isQueryBoundP_map_iff _ _ fuel).2
  exact simulate_hazardEnforcementImpl_run_isHazardQueryBoundP computation fuel

def enforceHazardTrace : Nat → ActionTrace Index → ActionTrace Index
  | _, [] => []
  | fuel, .encoding (.sign leafIndex output) :: trace =>
      .encoding (.sign leafIndex output) :: enforceHazardTrace fuel trace
  | fuel, .chain (.reveal index value) :: trace =>
      .chain (.reveal index value) :: enforceHazardTrace fuel trace
  | 0, .encoding (.query _ _) :: trace => enforceHazardTrace 0 trace
  | fuel + 1, .encoding (.query leafIndex output) :: trace =>
      .encoding (.query leafIndex output) :: enforceHazardTrace fuel trace
  | 0, .chain (.probe _ _) :: trace => enforceHazardTrace 0 trace
  | fuel + 1, .chain (.probe index target) :: trace =>
      .chain (.probe index target) :: enforceHazardTrace fuel trace

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardTrace_eq_self_of_count_le
    (trace : ActionTrace Index) (fuel : Nat)
    (hcount : hazardCount trace ≤ fuel) :
    enforceHazardTrace fuel trace = trace := by
  induction trace generalizing fuel with
  | nil => rfl
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign leafIndex output =>
              simp only [hazardCount] at hcount
              simp only [enforceHazardTrace, List.cons.injEq, true_and]
              exact ih fuel hcount
          | query leafIndex output =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ fuel =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  simp only [enforceHazardTrace, List.cons.injEq, true_and]
                  exact ih fuel hcount
      | chain action =>
          cases action with
          | reveal index value =>
              simp only [hazardCount] at hcount
              simp only [enforceHazardTrace, List.cons.injEq, true_and]
              exact ih fuel hcount
          | probe index target =>
              cases fuel with
              | zero => simp [hazardCount] at hcount
              | succ fuel =>
                  simp only [hazardCount, Nat.succ_le_succ_iff] at hcount
                  simp only [enforceHazardTrace, List.cons.injEq, true_and]
                  exact ih fuel hcount

omit [Fintype Index] [DecidableEq Index] in
theorem enforceHazardTrace_append
    (fuel : Nat) (left right : ActionTrace Index) :
    enforceHazardTrace fuel (left ++ right) =
      enforceHazardTrace fuel left ++
        enforceHazardTrace (fuel - hazardCount left) right := by
  induction left generalizing fuel with
  | nil => simp [hazardCount, enforceHazardTrace]
  | cons action left ih =>
      cases action with
      | encoding action =>
          cases action with
          | sign leafIndex output =>
              simp [hazardCount, enforceHazardTrace, ih]
          | query leafIndex output =>
              cases fuel with
              | zero => simp [hazardCount, enforceHazardTrace, ih]
              | succ fuel => simp [hazardCount, enforceHazardTrace, ih]
      | chain action =>
          cases action with
          | reveal index value =>
              simp [hazardCount, enforceHazardTrace, ih]
          | probe index target =>
              cases fuel with
              | zero => simp [hazardCount, enforceHazardTrace, ih]
              | succ fuel => simp [hazardCount, enforceHazardTrace, ih]

omit [Fintype Index] [DecidableEq Index] in
theorem CappedEncodingMonitor.runObserved_append_eq_true_of_prefix
    (state : EncodingMonitor.State) (left right : EncodingActionTrace)
    (hhit : CappedEncodingMonitor.runObserved state left = true) :
    CappedEncodingMonitor.runObserved state (left ++ right) = true := by
  induction left generalizing state with
  | nil => simp [CappedEncodingMonitor.runObserved] at hhit
  | cons action left ih =>
      cases happly : CappedEncodingMonitor.State.applyObserved state action with
      | none => simp [CappedEncodingMonitor.runObserved, happly] at hhit
      | some result =>
          rcases result with ⟨nextState, hit⟩
          cases hit with
          | false =>
              simp only [List.cons_append,
                CappedEncodingMonitor.runObserved, happly,
                Bool.false_or] at hhit ⊢
              exact ih nextState hhit
          | true =>
              simp [List.cons_append, CappedEncodingMonitor.runObserved,
                happly]

theorem CombinedHit.append_of_prefix
    (table : Index → Digest) (left right : ActionTrace Index)
    (hhit : CombinedHit table left) : CombinedHit table (left ++ right) := by
  rcases hhit with hencoding | hchain
  · apply Or.inl
    rw [ActionTrace.encodingActions_append]
    exact CappedEncodingMonitor.runObserved_append_eq_true_of_prefix
      EncodingMonitor.State.empty left.encodingActions right.encodingActions
        hencoding
  · apply Or.inr
    rw [ActionTrace.chainActions_append]
    exact RevealProbeOracleSimulation.runObserved_append_eq_true_of_prefix
      table AdaptiveRevealMonitor.State.empty left.chainActions
        right.chainActions hchain

theorem CombinedHit.enforce_append_of_prefix
    (table : Index → Digest) (fuel : Nat)
    (left right : ActionTrace Index)
    (hhit : CombinedHit table (enforceHazardTrace fuel left)) :
    CombinedHit table (enforceHazardTrace fuel (left ++ right)) := by
  rw [enforceHazardTrace_append]
  exact CombinedHit.append_of_prefix table (enforceHazardTrace fuel left)
    (enforceHazardTrace (fuel - hazardCount left) right) hhit

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_hazardEnforcementImpl_query
    (table : Index → Digest)
    (input : (World Index).Domain) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      ((hazardEnforcementImpl input).run fuel)).run =
        (fun result =>
          ((result.1, fuel - hazardCount result.2),
            enforceHazardTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table)
            (liftM ((World Index).query input))).run := by
  unfold hazardEnforcementImpl
  cases input with
  | uniform n =>
      simp [StateT.run, uniformQuery, eagerTraceImpl, eagerImpl,
        traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell,
        hazardCount, enforceHazardTrace]
  | encodingQuery leafIndex =>
      cases fuel with
      | zero =>
          simp [StateT.run, eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            enforceHazardTrace]
          change (fun x => ((x.1, 0), x.2)) <$>
              (simulateQ (eagerTraceImpl table)
                (liftProbComp uniformHashOutput)).run = _
          rw [simulate_eagerTrace_liftProbComp]
          simp
      | succ remaining =>
          simp [StateT.run, encodingQuery, eagerTraceImpl, eagerImpl,
            traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            hazardCount, enforceHazardTrace]
  | encodingSignAttempt leafIndex =>
      simp [StateT.run, encodingSignAttemptQuery, eagerTraceImpl,
        eagerImpl, traceFragment, QueryImpl.withTraceAppend_apply,
        WriterT.run_tell, hazardCount, enforceHazardTrace]
  | probe index target =>
      cases fuel with
      | zero =>
          simp [StateT.run, eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            enforceHazardTrace]
      | succ remaining =>
          simp [StateT.run, probeQuery, eagerTraceImpl, eagerImpl,
            traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            hazardCount, enforceHazardTrace]
  | reveal index =>
      simp [StateT.run, revealQuery, eagerTraceImpl, eagerImpl,
        traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell,
        hazardCount, enforceHazardTrace]

omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_hazardEnforcementImpl_run
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      ((simulateQ hazardEnforcementImpl computation).run fuel)).run =
        (fun result =>
          ((result.1, fuel - hazardCount result.2),
            enforceHazardTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  apply QueryImpl.simulateQ_stateHandler_trace
    (eagerTraceImpl table) hazardEnforcementImpl
    (fun fuel trace => fuel - hazardCount trace) enforceHazardTrace
  · intro state
    simp [hazardCount]
  · intro state left right
    simp [hazardCount_append, Nat.sub_add_eq]
  · intro state
    rfl
  · exact enforceHazardTrace_append
  · exact simulate_eagerTrace_hazardEnforcementImpl_query table
omit [Fintype Index] [DecidableEq Index] in
theorem simulate_eagerTrace_enforceHazardBound
    (table : Index → Digest)
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    (simulateQ (eagerTraceImpl table)
      (enforceHazardBound fuel computation)).run =
        (fun result => (result.1, enforceHazardTrace fuel result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  unfold enforceHazardBound
  rw [simulateQ_map, WriterT.run_map',
    simulate_eagerTrace_hazardEnforcementImpl_run]
  simp [Functor.map_map, Prod.map]

def enforceEagerResult
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index)) :
    (Index → Digest) × (α × ActionTrace Index) :=
  (result.1, (result.2.1, enforceHazardTrace fuel result.2.2))

omit [Fintype Index] [DecidableEq Index] in
theorem enforceEagerResult_eq_self_of_count_le
    (fuel : Nat)
    (result : (Index → Digest) × (α × ActionTrace Index))
    (hcount : hazardCount result.2.2 ≤ fuel) :
    enforceEagerResult fuel result = result := by
  unfold enforceEagerResult
  rw [enforceHazardTrace_eq_self_of_count_le result.2.2 fuel hcount]

theorem eagerExperiment_enforceHazardBound_eq_map
    (computation : OracleComp (World Index) α) (fuel : Nat) :
    eagerExperiment (enforceHazardBound fuel computation) =
      enforceEagerResult fuel <$> eagerExperiment computation := by
  unfold eagerExperiment
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_enforceHazardBound]
  rw [map_eq_bind_pure_comp]
  simp only [bind_assoc, pure_bind, Function.comp_apply, enforceEagerResult]

end XmssSecurity.FirstLaneOracleSimulation
