import XmssSecurity.Proof.AdaptiveRevealMonitor
import XmssSecurity.Proof.IndexedHiddenValue

open OracleComp OracleSpec ENNReal

namespace QueryImpl

@[simp] theorem run_simulateQ_withTraceAppend_const_empty
    {spec : OracleSpec ι} {m : Type → Type*} [Monad m] [LawfulMonad m] {Log : Type}
    [EmptyCollection Log] [Append Log] [LawfulAppend Log]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    (simulateQ (impl.withTraceAppend (fun _ _ => (∅ : Log))) computation).run =
      (fun result => (result, ∅)) <$> simulateQ impl computation := by
  induction computation using OracleComp.inductionOn <;> simp [*]

theorem mapLog_run_simulateQ_of_query
    {SourceLog TargetLog : Type}
    [EmptyCollection SourceLog] [Append SourceLog] [LawfulAppend SourceLog]
    [EmptyCollection TargetLog] [Append TargetLog] [LawfulAppend TargetLog]
    (source : QueryImpl spec (WriterT SourceLog ProbComp))
    (target : QueryImpl spec (WriterT TargetLog ProbComp))
    (project : SourceLog → TargetLog)
    (h_empty : project ∅ = ∅)
    (h_append : ∀ left right,
      project (left ++ right) = project left ++ project right)
    (hquery : ∀ input,
      Prod.map id project <$> (source input).run = (target input).run)
    (computation : OracleComp spec α) :
    Prod.map id project <$> (simulateQ source computation).run =
      (simulateQ target computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp [h_empty]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, WriterT.run_bind', map_bind]
      rw [← hquery input, bind_map_left]
      apply bind_congr
      intro result
      simp only [Prod.map, id_eq]
      rw [← ih result.1]
      simp [h_append, Prod.map]

end QueryImpl

namespace XmssSecurity.RevealProbeOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive Query (Index : Type) where
  | uniform (n : Nat)
  | probe (index : Index) (target : Digest)
  | reveal (index : Index)

@[reducible]
def World (Index : Type) : OracleSpec (Query Index) :=
  OracleSpec.ofFn fun
  | .uniform n => Fin (n + 1)
  | .probe _ _ => Unit
  | .reveal _ => Digest

def probeQuery (index : Index) (target : Digest) :
    OracleComp (World Index) Unit :=
  liftM ((World Index).query (.probe index target))

def revealQuery (index : Index) : OracleComp (World Index) Digest :=
  liftM ((World Index).query (.reveal index))

def uniformQuery (n : Nat) : OracleComp (World Index) (Fin (n + 1)) :=
  liftM ((World Index).query (.uniform n))

def uniformForwardImpl : QueryImpl unifSpec (OracleComp (World Index)) :=
  fun n => uniformQuery n

def liftProbComp (computation : ProbComp α) :
    OracleComp (World Index) α :=
  simulateQ uniformForwardImpl computation

def IsSpecialQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | .probe _ _ => True
  | .reveal _ => True

def IsProbeQuery : (World Index).Domain → Prop
  | .uniform _ => False
  | .probe _ _ => True
  | .reveal _ => False

noncomputable instance : DecidablePred (IsSpecialQuery (Index := Index)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsSpecialQuery])
  | .probe _ _ => isTrue (by simp [IsSpecialQuery])
  | .reveal _ => isTrue (by simp [IsSpecialQuery])

noncomputable instance : DecidablePred (IsProbeQuery (Index := Index)) :=
  fun input => match input with
  | .uniform _ => isFalse (by simp [IsProbeQuery])
  | .probe _ _ => isTrue (by simp [IsProbeQuery])
  | .reveal _ => isFalse (by simp [IsProbeQuery])

omit [Fintype Index] [DecidableEq Index] in
theorem liftProbComp_isProbeQueryBoundP
    (computation : ProbComp α) (probes : Nat) :
    (liftProbComp (Index := Index) computation).IsQueryBoundP
      IsProbeQuery probes := by
  induction computation using OracleComp.inductionOn with
  | pure result => trivial
  | query_bind n next ih =>
      rw [liftProbComp, simulateQ_query_bind]
      change (uniformQuery n >>= fun output =>
        liftProbComp (next output)).IsQueryBoundP IsProbeQuery probes
      rw [uniformQuery, OracleComp.isQueryBoundP_query_bind_iff]
      constructor
      · simp [IsProbeQuery]
      · intro output
        simpa [IsProbeQuery] using ih output

omit [Fintype Index] [DecidableEq Index] in
theorem probeQuery_isProbeQueryBoundP
    (index : Index) (target : Digest) :
    (probeQuery index target).IsQueryBoundP IsProbeQuery 1 := by
  rw [probeQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbeQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem revealQuery_isProbeQueryBoundP (index : Index) (probes : Nat) :
    (revealQuery index).IsQueryBoundP IsProbeQuery probes := by
  rw [revealQuery, OracleComp.isQueryBoundP_query_iff]
  simp [IsProbeQuery]

inductive ObservedAction (Index : Type) where
  | probe (index : Index) (target : Digest)
  | reveal (index : Index) (value : Digest)
deriving DecidableEq

abbrev ActionTrace (Index : Type) := List (ObservedAction Index)

noncomputable def eagerImpl (table : Index → Digest) :
    QueryImpl (World Index) ProbComp := fun input =>
  match input with
  | .uniform n => liftM (unifSpec.query n)
  | .probe _ _ => pure ()
  | .reveal index => pure (table index)

def traceFragment
    (input : (World Index).Domain) (output : (World Index).Range input) :
    ActionTrace Index :=
  match input with
  | .uniform _ => []
  | .probe index target => [.probe index target]
  | .reveal index => [.reveal index output]

noncomputable def eagerTraceImpl (table : Index → Digest) :
    QueryImpl (World Index) (WriterT (ActionTrace Index) ProbComp) :=
  (eagerImpl table).withTraceAppend traceFragment

omit [Fintype Index] [DecidableEq Index] in
@[simp]
theorem simulate_eagerTrace_revealQuery
    (table : Index → Digest) (index : Index) :
    (simulateQ (eagerTraceImpl table) (revealQuery index)).run =
      pure (table index, [.reveal index (table index)]) := by
  simp [revealQuery, eagerTraceImpl, eagerImpl, traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell]

noncomputable local instance sampleableTable :
    SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

noncomputable def eagerTableSample : ProbComp (Index → Digest) :=
  $ᵗ (Index → Digest)

def StateValid
    (state : AdaptiveRevealMonitor.State Index) : Prop :=
  ∀ index value, state.revealed index = some value → state.pending index = ∅

def StateAgrees
    (table : Index → Digest) (state : AdaptiveRevealMonitor.State Index) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

omit [Fintype Index] [DecidableEq Index] in
theorem stateValid_empty :
    StateValid (AdaptiveRevealMonitor.State.empty :
      AdaptiveRevealMonitor.State Index) := by
  intro index value hvalue
  simp [AdaptiveRevealMonitor.State.empty] at hvalue

omit [Fintype Index] [DecidableEq Index] in
theorem stateAgrees_empty (table : Index → Digest) :
    StateAgrees table (AdaptiveRevealMonitor.State.empty :
      AdaptiveRevealMonitor.State Index) := by
  intro index value hvalue
  simp [AdaptiveRevealMonitor.State.empty] at hvalue

omit [Fintype Index] in
theorem StateValid.addPending
    {state : AdaptiveRevealMonitor.State Index} (hvalid : StateValid state)
    (index : Index) (target : Digest)
    (hhidden : state.revealed index = none) :
    StateValid (state.addPending index target) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [AdaptiveRevealMonitor.State.addPending, hhidden] at hvalue
  · simpa [AdaptiveRevealMonitor.State.addPending,
      Function.update_of_ne heq] using hvalid candidate value hvalue

omit [Fintype Index] in
theorem StateAgrees.addPending
    {table : Index → Digest} {state : AdaptiveRevealMonitor.State Index}
    (hagrees : StateAgrees table state) (index : Index) (target : Digest) :
    StateAgrees table (state.addPending index target) := by
  exact hagrees

omit [Fintype Index] in
theorem StateValid.install
    {state : AdaptiveRevealMonitor.State Index} (hvalid : StateValid state)
    (index : Index) (value : Digest) :
    StateValid (state.install index value) := by
  intro candidate candidateValue hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [AdaptiveRevealMonitor.State.install]
  · have hvalue' : state.revealed candidate = some candidateValue := by
      simpa [AdaptiveRevealMonitor.State.install,
        Function.update_of_ne heq] using hvalue
    have hpending := hvalid candidate candidateValue hvalue'
    simpa [AdaptiveRevealMonitor.State.install,
      Function.update_of_ne heq] using hpending

omit [Fintype Index] in
theorem StateAgrees.install
    {table : Index → Digest} {state : AdaptiveRevealMonitor.State Index}
    (hagrees : StateAgrees table state) (index : Index) :
    StateAgrees table (state.install index (table index)) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simpa [AdaptiveRevealMonitor.State.install] using hvalue
  · have hvalue' : state.revealed candidate = some value := by
      simpa [AdaptiveRevealMonitor.State.install,
        Function.update_of_ne heq] using hvalue
    exact hagrees candidate value hvalue'

def extendTable
    (state : AdaptiveRevealMonitor.State Index)
    (base : Index → Digest) : Index → Digest :=
  fun index => (state.revealed index).getD (base index)

omit [Fintype Index] in
theorem extendTable_update_eq_install
    (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (value : Digest) (base : Index → Digest)
    (hhidden : state.revealed index = none) :
    extendTable state (Function.update base index value) =
      extendTable (state.install index value) base := by
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp [extendTable, AdaptiveRevealMonitor.State.install, hhidden]
  · simp [extendTable, AdaptiveRevealMonitor.State.install,
      Function.update_of_ne heq]

def tableHits
    (state : AdaptiveRevealMonitor.State Index)
    (table : Index → Digest) : Bool :=
  decide (∃ index, table index ∈ state.pending index)

def runObserved
    (table : Index → Digest) :
    AdaptiveRevealMonitor.State Index → ActionTrace Index → Bool
  | state, [] => tableHits state table
  | state, .probe index target :: rest =>
      match state.revealed index with
      | some _ => runObserved table state rest
      | none => runObserved table (state.addPending index target) rest
  | state, .reveal index _ :: rest =>
      match state.revealed index with
      | some _ => runObserved table state rest
      | none =>
          let value := table index
          if value ∈ state.pending index then true
          else runObserved table (state.install index value) rest

def ObservedHit
    (result : (Index → Digest) × (α × ActionTrace Index)) : Prop :=
  runObserved result.1 AdaptiveRevealMonitor.State.empty result.2.2 = true

omit [DecidableEq Index] in
theorem tableHits_extendTable_eq_true_iff
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state)
    (base : Index → Digest) :
    tableHits state (extendTable state base) = true ↔
      ∃ index ∈ (Finset.univ : Finset Index),
        ∃ target ∈ state.pending index, base index = target := by
  simp only [tableHits, decide_eq_true_eq, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, hmem⟩
    have hhidden : state.revealed index = none := by
      cases hvalue : state.revealed index with
      | none => rfl
      | some value =>
          have hempty := hvalid index value hvalue
          rw [hempty] at hmem
          simp at hmem
    refine ⟨index, ⟨extendTable state base index, hmem, ?_⟩⟩
    simp [extendTable, hhidden]
  · rintro ⟨index, target, htarget, heq⟩
    have hhidden : state.revealed index = none := by
      cases hvalue : state.revealed index with
      | none => rfl
      | some value =>
          have hempty := hvalid index value hvalue
          rw [hempty] at htarget
          simp at htarget
    exact ⟨index, by simpa [extendTable, hhidden, heq] using htarget⟩

theorem eagerFinalize_true_probability_le
    (state : AdaptiveRevealMonitor.State Index) (hvalid : StateValid state) :
    Pr[(fun hit : Bool => hit = true) |
      (fun base : Index → Digest => tableHits state (extendTable state base)) <$>
        ($ᵗ (Index → Digest))] ≤
      (state.pendingCount : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_map]
  change Pr[(fun base : Index → Digest =>
    tableHits state (extendTable state base) = true) |
      $ᵗ (Index → Digest)] ≤ _
  have hevent :
      (fun base : Index → Digest =>
        tableHits state (extendTable state base) = true) =
      (fun base : Index → Digest =>
        ∃ index ∈ (Finset.univ : Finset Index),
          ∃ target ∈ state.pending index, base index = target) := by
    funext base
    exact propext (tableHits_extendTable_eq_true_iff state hvalid base)
  rw [hevent]
  calc
    Pr[fun base : Index → Digest =>
          ∃ index ∈ (Finset.univ : Finset Index),
            ∃ target ∈ state.pending index, base index = target |
        $ᵗ (Index → Digest)] ≤
      ∑ index ∈ (Finset.univ : Finset Index),
        Pr[fun base : Index → Digest =>
            ∃ target ∈ state.pending index, base index = target |
          $ᵗ (Index → Digest)] :=
        probEvent_exists_finset_le_sum Finset.univ ($ᵗ (Index → Digest))
          (fun index base =>
            ∃ target ∈ state.pending index, base index = target)
    _ ≤ ∑ index ∈ (Finset.univ : Finset Index),
        ((state.pending index).card : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro index _hindex
      calc
        Pr[fun base : Index → Digest =>
              ∃ target ∈ state.pending index, base index = target |
            $ᵗ (Index → Digest)] ≤
          ∑ target ∈ state.pending index,
            Pr[fun base : Index → Digest => base index = target |
              $ᵗ (Index → Digest)] :=
            probEvent_exists_finset_le_sum (state.pending index)
              ($ᵗ (Index → Digest))
              (fun target base => base index = target)
        _ = ∑ _target ∈ state.pending index,
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_congr rfl
          intro target _htarget
          exact IndexedHiddenValue.uniform_table_coordinate_probability index target
        _ = ((state.pending index).card : ℝ≥0∞) *
            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (state.pendingCount : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul]
      congr 1
      simp [AdaptiveRevealMonitor.State.pendingCount]

theorem uniformDigest_mem_finset_le (targets : Finset Digest) :
    Pr[(fun value : Digest => value ∈ targets) | $ᵗ Digest] ≤
      (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    Pr[(fun value : Digest => value ∈ targets) | $ᵗ Digest] =
      Pr[(fun value : Digest => ∃ target ∈ targets, value = target) |
        $ᵗ Digest] := by
      apply probEvent_congr' (fun value _ => by simp) rfl
    _ ≤ ∑ target ∈ targets,
        Pr[(fun value : Digest => value = target) | $ᵗ Digest] :=
      probEvent_exists_finset_le_sum targets ($ᵗ Digest)
        (fun target value => value = target)
    _ = ∑ _target ∈ targets,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [probEvent_uniformSample]
      have hfilter :
          (Finset.univ.filter (fun value : Digest => value = target)) =
            {target} := by
        ext value
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
      rw [hfilter, Finset.card_singleton, HiddenValue.card_digest]
      simp only [Nat.cast_one, one_div]
    _ = (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem evalDist_uniformTable_eq_bind_update
    (index : Index) (continuation : (Index → Digest) → ProbComp α) :
    𝒟[($ᵗ (Index → Digest)) >>= continuation] =
      𝒟[do
        let value ← $ᵗ Digest
        let base ← $ᵗ (Index → Digest)
        continuation (Function.update base index value)] := by
  calc
    𝒟[($ᵗ (Index → Digest)) >>= continuation] =
        𝒟[(do
          let value ← $ᵗ Digest
          let base ← $ᵗ (Index → Digest)
          pure (Function.update base index value)) >>= continuation] := by
      rw [evalDist_bind, evalDist_bind, evalDist_uniformSample_bind_update index]
    _ = _ := by simp [bind_assoc]

set_option maxRecDepth 100000 in
def observedProbeCount : ActionTrace Index → Nat
  | [] => 0
  | .probe _ _ :: rest => (observedProbeCount rest).succ
  | .reveal _ _ :: rest => observedProbeCount rest

def emitObservedTrace : ActionTrace Index → OracleComp (World Index) Unit
  | [] => pure ()
  | .probe index target :: rest => do
      probeQuery index target
      emitObservedTrace rest
  | .reveal index _value :: rest => do
      let _actualValue ← revealQuery index
      emitObservedTrace rest

def TraceAgrees (table : Index → Digest) : ActionTrace Index → Prop
  | [] => True
  | .probe _ _ :: rest => TraceAgrees table rest
  | .reveal index value :: rest => table index = value ∧ TraceAgrees table rest

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

end XmssSecurity.RevealProbeOracleSimulation
