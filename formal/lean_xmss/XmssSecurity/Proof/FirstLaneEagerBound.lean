import XmssSecurity.Proof.FirstLaneEagerSimulation
import VCVio.ProgramLogic.Relational.Quantitative

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
@[simp] theorem eagerTraceImpl_run
    (table : Index → Digest) (input : (World Index).Domain) :
    (eagerTraceImpl table input).run =
      (fun output => (output, traceFragment input output)) <$>
        eagerImpl table input := by
  simp [eagerTraceImpl, QueryImpl.withTraceAppend_apply]

omit [Fintype Index] [DecidableEq Index] in
theorem eagerTrace_query_bind_run
    (table : Index → Digest) (input : (World Index).Domain)
    (next : (World Index).Range input → OracleComp (World Index) α) :
    (simulateQ (eagerTraceImpl table)
      ((liftM (OracleSpec.query input) :
        OracleComp (World Index) ((World Index).Range input)) >>= next)).run = (do
      let output ← eagerImpl table input
      let tail ← (simulateQ (eagerTraceImpl table) (next output)).run
      pure (tail.1, traceFragment input output ++ tail.2)) := by
  rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
  simp only [eagerTraceImpl_run]
  simp [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro output
  apply bind_congr
  intro tail
  rfl

inductive EncodingRequest where
  | query (leafIndex : LeafIndex)
  | sign (leafIndex : LeafIndex)

def EncodingRequest.observed
    (request : EncodingRequest) (output : HashOutput) :
    EncodingMonitor.ObservedAction :=
  match request with
  | .query leafIndex => .query leafIndex output
  | .sign leafIndex => .sign leafIndex output

def EncodingRequest.cost : EncodingRequest → Nat
  | .query _ => 1
  | .sign _ => 0

noncomputable def applyEncodingRequest
    (request : EncodingRequest)
    (resume : HashOutput → Option EncodingMonitor.State → ProbComp Bool) :
    Option EncodingMonitor.State → ProbComp Bool
  | none => uniformHashOutput >>= fun output => resume output none
  | some state => uniformHashOutput >>= fun output =>
      match CappedEncodingMonitor.State.applyObserved state
        (request.observed output) with
      | none => resume output none
      | some (nextState, hit) =>
          if hit then pure true else resume output (some nextState)

theorem evalDist_sample_applyEncodingRequest
    (sample : ProbComp β) (hmass : Pr[⊥ | sample] = 0)
    (request : EncodingRequest)
    (resume : β → HashOutput → Option EncodingMonitor.State → ProbComp Bool)
    (state : Option EncodingMonitor.State) :
    evalDist (sample >>= fun seed =>
      applyEncodingRequest request (resume seed) state) =
      evalDist (applyEncodingRequest request
        (fun output nextState => sample >>= fun seed =>
          resume seed output nextState) state) := by
  cases state with
  | none =>
      unfold applyEncodingRequest
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  | some state =>
      unfold applyEncodingRequest
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      cases happly : CappedEncodingMonitor.State.applyObserved state
        (request.observed output) with
      | none => rfl
      | some result =>
          rcases result with ⟨nextState, hit⟩
          cases hit with
          | false => rfl
          | true =>
              exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                sample hmass (pure true)

noncomputable def runEagerQuery
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (input : Query Index)
    (resume : (World Index).Range input → Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → Nat → ProbComp Bool) :
    ProbComp Bool :=
  match input with
  | .uniform n => do
      let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      resume output encodingState chainState fuel
  | .encodingQuery leafIndex =>
      match fuel with
      | 0 => pure (RevealProbeOracleSimulation.tableHits chainState table)
      | remaining + 1 =>
          applyEncodingRequest (.query leafIndex)
            (fun output nextState =>
              resume output nextState chainState remaining)
            encodingState
  | .encodingSignAttempt leafIndex =>
      applyEncodingRequest (.sign leafIndex)
        (fun output nextState => resume output nextState chainState fuel)
        encodingState
  | .probe index target =>
      match fuel with
      | 0 => pure (RevealProbeOracleSimulation.tableHits chainState table)
      | remaining + 1 =>
          match chainState.revealed index with
          | some _ => resume () encodingState chainState remaining
          | none => resume () encodingState
              (chainState.addPending index target) remaining
  | .reveal index =>
      match chainState.revealed index with
      | some _ => resume (table index) encodingState chainState fuel
      | none =>
          let value := table index
          if value ∈ chainState.pending index then pure true
          else resume value encodingState (chainState.install index value) fuel

noncomputable def encodingPendingRisk : Option EncodingMonitor.State → ENNReal
  | none => 0
  | some state => CappedEncodingMonitor.State.pendingRisk state

noncomputable def potential
    (fuel : Nat) (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index) : ENNReal :=
  ((fuel + chainState.pendingCount : Nat) : ENNReal) *
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
    encodingPendingRisk encodingState

theorem applyEncodingRequest_true_probability_le
    (request : EncodingRequest)
    (resume : HashOutput → Option EncodingMonitor.State → ProbComp Bool)
    (state : Option EncodingMonitor.State) (fuel : Nat)
    (hresume : ∀ output nextState,
      Pr[(· = true) | resume output nextState] ≤
        (fuel : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          encodingPendingRisk nextState) :
    Pr[(· = true) | applyEncodingRequest request resume state] ≤
      ((fuel + request.cost : Nat) : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        encodingPendingRisk state := by
  cases request with
  | query leafIndex =>
      cases state with
      | none =>
          unfold applyEncodingRequest EncodingRequest.cost encodingPendingRisk
          refine (probEvent_bind_le_of_forall_le fun output _ =>
            hresume output none).trans ?_
          simp only [encodingPendingRisk, add_zero]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact le_add_right le_rfl
      | some state =>
          let activeResume := fun output nextState =>
            resume output (some nextState)
          have hdirect :
              applyEncodingRequest (.query leafIndex) resume (some state) =
                CappedEncodingMonitor.applyHashOutputQueryMonitor leafIndex
                  activeResume state := by
            rw [CappedEncodingMonitor.applyHashOutputQueryMonitor_eq_observed]
            unfold applyEncodingRequest EncodingRequest.observed activeResume
            apply bind_congr
            intro output
            cases hsigned : state.signed leafIndex with
            | none =>
                by_cases hvalid :
                    TargetSum.ValidDigest (truncateHash output) <;>
                  simp [CappedEncodingMonitor.State.applyObserved, hsigned,
                    hvalid]
            | some target =>
                simp [CappedEncodingMonitor.State.applyObserved, hsigned]
          have hdist :
              evalDist (applyEncodingRequest (.query leafIndex) resume (some state)) =
                evalDist (CappedEncodingMonitor.applyProgrammedQueryMonitor leafIndex
                  activeResume state) := by
            rw [hdirect]
            exact
              CappedEncodingMonitor.applyProgrammedQueryMonitor_evalDist_eq
                leafIndex activeResume state |>.symm
          refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
          simpa [EncodingRequest.cost, encodingPendingRisk, Nat.cast_add,
            HiddenValue.card_digest] using
            CappedEncodingMonitor.applyProgrammedQueryMonitor_true_probability_le
              leafIndex activeResume state fuel fun output nextState => by
                simpa [activeResume, encodingPendingRisk,
                  HiddenValue.card_digest] using
                  hresume output (some nextState)
  | sign leafIndex =>
      cases state with
      | none =>
          unfold applyEncodingRequest EncodingRequest.cost encodingPendingRisk
          exact probEvent_bind_le_of_forall_le fun output _ =>
            hresume output none
      | some state =>
          cases hsigned : state.signed leafIndex with
          | none =>
              let activeResume := fun output nextState =>
                resume output (some nextState)
              have hdirect :
                  applyEncodingRequest (.sign leafIndex) resume (some state) =
                    CappedEncodingMonitor.applyHashOutputSignAttemptMonitor leafIndex
                      activeResume state := by
                rw [CappedEncodingMonitor.applyHashOutputSignAttemptMonitor_eq_observed]
                unfold applyEncodingRequest EncodingRequest.observed activeResume
                apply bind_congr
                intro output
                by_cases hvalid :
                    TargetSum.ValidDigest (truncateHash output) <;>
                  simp [CappedEncodingMonitor.State.applyObserved, hsigned,
                    hvalid]
              have hdist :
                  evalDist
                      (applyEncodingRequest (.sign leafIndex) resume (some state)) =
                    evalDist
                      (CappedEncodingMonitor.applyProgrammedSignAttemptMonitor
                        leafIndex activeResume state) := by
                rw [hdirect]
                exact
                  CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_evalDist_eq
                    leafIndex activeResume state |>.symm
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
              simpa [EncodingRequest.cost, encodingPendingRisk,
                HiddenValue.card_digest] using
                CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_true_probability_le
                  leafIndex activeResume state fuel fun output nextState => by
                    simpa [activeResume, encodingPendingRisk,
                      HiddenValue.card_digest] using
                      hresume output (some nextState)
          | some target =>
              unfold applyEncodingRequest EncodingRequest.observed
              refine (probEvent_bind_le_of_forall_le
                (ε := (fuel : ENNReal) *
                    ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                  encodingPendingRisk (some state))
                fun output _ => ?_).trans ?_
              · by_cases hvalid : TargetSum.ValidDigest (truncateHash output)
                · rw [show CappedEncodingMonitor.State.applyObserved state
                      (.sign leafIndex output) = none by
                    simp [CappedEncodingMonitor.State.applyObserved, hsigned,
                      hvalid]]
                  exact (hresume output none).trans (by simp [encodingPendingRisk])
                · rw [show CappedEncodingMonitor.State.applyObserved state
                      (.sign leafIndex output) =
                        some (state, false) by
                    simp [CappedEncodingMonitor.State.applyObserved, hvalid]]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact hresume output (some state)
              · simp [EncodingRequest.cost]

noncomputable def applyRevealRequest
    (state : AdaptiveRevealMonitor.State Index) (index : Index)
    (resume : Digest → AdaptiveRevealMonitor.State Index → ProbComp Bool) :
    ProbComp Bool := do
  let value ← $ᵗ Digest
  if value ∈ state.pending index then pure true
  else resume value (state.install index value)

theorem applyRevealRequest_true_probability_le
    (state : AdaptiveRevealMonitor.State Index) (index : Index)
    (resume : Digest → AdaptiveRevealMonitor.State Index → ProbComp Bool)
    (fuel : Nat) (offset : ENNReal)
    (hresume : ∀ value,
      Pr[(· = true) | resume value (state.install index value)] ≤
        ((fuel + (state.install index value).pendingCount : Nat) : ENNReal) *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset) :
    Pr[(· = true) | applyRevealRequest state index resume] ≤
      ((fuel + state.pendingCount : Nat) : ENNReal) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset := by
  let installedCount := (state.install index 0).pendingCount
  refine (probEvent_bind_le_probEvent_add
    (mx := ($ᵗ Digest))
    (my := fun value =>
      if value ∈ state.pending index then pure true
      else resume value (state.install index value))
    (q := fun hit : Bool => hit = true)
    (p := fun value : Digest => value ∈ state.pending index)
    (ε := ((fuel + installedCount : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset) ?_).trans ?_
  · intro value _hvalue hmiss
    simp only [hmiss, ↓reduceIte]
    have hcount :
        (state.install index value).pendingCount = installedCount := rfl
    simpa [hcount] using hresume value
  · refine add_le_add
      (RevealProbeOracleSimulation.uniformDigest_mem_finset_le
        (state.pending index)) le_rfl |>.trans ?_
    have hconserve := state.pendingCount_install_add index 0
    calc
      ((state.pending index).card : ENNReal) *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
          (((fuel + installedCount : Nat) : ENNReal) *
              ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset) =
        ((((state.pending index).card + fuel + installedCount : Nat) :
              ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
            offset) := by
          push_cast
          ring
      _ = ((fuel + state.pendingCount : Nat) : ENNReal) *
              ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset := by
            rw [show
              (state.pending index).card + fuel + installedCount =
                fuel + state.pendingCount by omega]
      _ ≤ ((fuel + state.pendingCount : Nat) : ENNReal) *
              ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + offset := le_rfl

theorem evalDist_eagerTableSample_applyRevealRequest
    (chainState : AdaptiveRevealMonitor.State Index)
    (index : Index) (hrevealed : chainState.revealed index = none)
    (resume : (Index → Digest) → Digest →
      AdaptiveRevealMonitor.State Index → ProbComp Bool) :
    evalDist (RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
      let table := RevealProbeOracleSimulation.extendTable chainState base
      let value := table index
      if value ∈ chainState.pending index then pure true
      else resume table value (chainState.install index value)) =
      evalDist (applyRevealRequest chainState index fun value nextState =>
        RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
          resume (RevealProbeOracleSimulation.extendTable nextState base)
            value nextState) := by
  let continuation := fun (base : Index → Digest) =>
    let table := RevealProbeOracleSimulation.extendTable chainState base
    let value := table index
    if value ∈ chainState.pending index then pure true
    else resume table value (chainState.install index value)
  calc
    _ = evalDist (do
          let value ← $ᵗ Digest
          let base ← RevealProbeOracleSimulation.eagerTableSample
          if value ∈ chainState.pending index then pure true
          else
            resume
              (RevealProbeOracleSimulation.extendTable
                (chainState.install index value) base)
              value (chainState.install index value)) := by
        unfold RevealProbeOracleSimulation.eagerTableSample
        rw [RevealProbeOracleSimulation.evalDist_uniformTable_eq_bind_update
          index continuation]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro value
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro base
        simp only [continuation]
        rw [RevealProbeOracleSimulation.extendTable_update_eq_install
          chainState index value base hrevealed]
        have hinstalled :
            RevealProbeOracleSimulation.extendTable
              (chainState.install index value) base index = value := by
          simp [RevealProbeOracleSimulation.extendTable,
            AdaptiveRevealMonitor.State.install]
        rw [hinstalled]
    _ = _ := by
      unfold applyRevealRequest
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      by_cases hhit : value ∈ chainState.pending index
      · simp only [hhit, ↓reduceIte]
        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          RevealProbeOracleSimulation.eagerTableSample
          (by simp [RevealProbeOracleSimulation.eagerTableSample]) (pure true)
      · simp [hhit]

noncomputable def runObserved
    (table : Index → Digest) :
    Option EncodingMonitor.State → AdaptiveRevealMonitor.State Index →
      ActionTrace Index → Bool
  | _encodingState, chainState, [] =>
      RevealProbeOracleSimulation.tableHits chainState table
  | encodingState, chainState, .encoding action :: rest =>
      match encodingState with
      | none => runObserved table none chainState rest
      | some state =>
          match CappedEncodingMonitor.State.applyObserved state action with
          | none => runObserved table none chainState rest
          | some (nextState, hit) =>
              hit || runObserved table (some nextState) chainState rest
  | encodingState, chainState, .chain (.probe index target) :: rest =>
      match chainState.revealed index with
      | some _ => runObserved table encodingState chainState rest
      | none => runObserved table encodingState
          (chainState.addPending index target) rest
  | encodingState, chainState, .chain (.reveal index _value) :: rest =>
      match chainState.revealed index with
      | some _ => runObserved table encodingState chainState rest
      | none =>
          let value := table index
          if value ∈ chainState.pending index then true
          else runObserved table encodingState
            (chainState.install index value) rest

theorem runObserved_eq_projected
    (table : Index → Digest) (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (trace : ActionTrace Index) :
    runObserved table encodingState chainState trace =
      ((match encodingState with
        | none => false
        | some state => CappedEncodingMonitor.runObserved state
            trace.encodingActions) ||
        RevealProbeOracleSimulation.runObserved table chainState
          trace.chainActions) := by
  induction trace generalizing encodingState chainState with
  | nil =>
      cases encodingState <;>
        simp [runObserved, ActionTrace.encodingActions,
          ActionTrace.chainActions, CappedEncodingMonitor.runObserved,
          RevealProbeOracleSimulation.runObserved]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases encodingState with
          | none =>
              simpa [runObserved, ActionTrace.encodingActions,
                ActionTrace.chainActions] using ih none chainState
          | some state =>
              cases happly :
                CappedEncodingMonitor.State.applyObserved state action with
              | none =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    CappedEncodingMonitor.runObserved, happly] using
                    ih none chainState
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit <;>
                    simp [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      CappedEncodingMonitor.runObserved, happly,
                      ih (some nextState) chainState]
      | chain action =>
          cases action with
          | probe index target =>
              cases hrevealed : chainState.revealed index with
              | none =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState (chainState.addPending index target)
              | some value =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState chainState
          | reveal index value =>
              cases hrevealed : chainState.revealed index with
              | some revealed =>
                  simpa [runObserved, ActionTrace.encodingActions,
                    ActionTrace.chainActions,
                    RevealProbeOracleSimulation.runObserved, hrevealed] using
                    ih encodingState chainState
              | none =>
                  by_cases hhit : table index ∈ chainState.pending index
                  · simp [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      RevealProbeOracleSimulation.runObserved, hrevealed, hhit]
                  · simpa [runObserved, ActionTrace.encodingActions,
                      ActionTrace.chainActions,
                      RevealProbeOracleSimulation.runObserved, hrevealed,
                      hhit] using ih encodingState
                        (chainState.install index (table index))

theorem runObserved_empty_eq_combinedHit
    (table : Index → Digest) (trace : ActionTrace Index) :
    runObserved table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty trace = true ↔
      CombinedHit table trace := by
  rw [runObserved_eq_projected]
  simp only [Bool.or_eq_true]
  rfl

noncomputable def runStructural
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => Option EncodingMonitor.State →
      AdaptiveRevealMonitor.State Index → Nat → ProbComp Bool)
    (fun _ _encodingState chainState _fuel =>
      pure (RevealProbeOracleSimulation.tableHits chainState table))
    (fun input _next recursivelyRun encodingState chainState fuel =>
      runEagerQuery table encodingState chainState fuel input recursivelyRun)
    computation encodingState chainState fuel

theorem runStructural_query_bind
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (input : (World Index).Domain)
    (next : (World Index).Range input → OracleComp (World Index) α) :
    runStructural table encodingState chainState fuel
        ((liftM (OracleSpec.query input) :
          OracleComp (World Index) ((World Index).Range input)) >>= next) =
      runEagerQuery table encodingState chainState fuel input fun output
        nextEncoding nextChain nextFuel =>
          runStructural table nextEncoding nextChain nextFuel (next output) := by
  rw [runStructural, OracleComp.construct_query_bind]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem evalDist_runObserved_eagerTrace_eq_runStructural
    (table : Index → Digest)
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    evalDist ((fun result => runObserved table encodingState chainState result.2) <$>
      (simulateQ (eagerTraceImpl table) computation).run) =
    evalDist (runStructural table encodingState chainState fuel computation) := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState fuel with
  | pure result =>
      simp [eagerTraceImpl, runObserved, runStructural]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [eagerTrace_query_bind_run, runStructural_query_bind]
          simp only [eagerImpl, traceFragment, map_bind, runEagerQuery]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          simpa [runObserved] using
            ih output encodingState chainState fuel
              (by simpa [IsHazardQuery] using hbound.2 output)
      | encodingQuery leafIndex =>
          cases fuel with
          | zero => simp [IsHazardQuery] at hbound
          | succ remaining =>
              rw [eagerTrace_query_bind_run, runStructural_query_bind]
              simp only [eagerImpl, traceFragment, map_bind, runEagerQuery,
                applyEncodingRequest, EncodingRequest.observed]
              cases encodingState with
              | none =>
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro output
                  simpa [runObserved] using
                    ih output none chainState remaining
                      (by simpa [IsHazardQuery] using hbound.2 output)
              | some state =>
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro output
                  cases happly : CappedEncodingMonitor.State.applyObserved state
                    (.query leafIndex output) with
                  | none =>
                      simpa [runObserved, happly] using
                        ih output none chainState remaining
                          (by simpa [IsHazardQuery] using hbound.2 output)
                  | some result =>
                      rcases result with ⟨nextState, hit⟩
                      cases hit with
                      | false =>
                          simpa [runObserved, happly] using
                            ih output (some nextState) chainState remaining
                              (by simpa [IsHazardQuery] using hbound.2 output)
                      | true =>
                          simp [runObserved, happly]
                          apply OracleComp.ProgramLogic.Relational.spmf_map_const_of_no_failure
                          exact probFailure_of_liftM_PMF _
      | encodingSignAttempt leafIndex =>
          rw [eagerTrace_query_bind_run, runStructural_query_bind]
          simp only [eagerImpl, traceFragment, map_bind, runEagerQuery,
            applyEncodingRequest, EncodingRequest.observed]
          cases encodingState with
          | none =>
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              simpa [runObserved] using
                ih output none chainState fuel
                  (by simpa [IsHazardQuery] using hbound.2 output)
          | some state =>
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              cases happly : CappedEncodingMonitor.State.applyObserved state
                (.sign leafIndex output) with
              | none =>
                  simpa [runObserved, happly] using
                    ih output none chainState fuel
                      (by simpa [IsHazardQuery] using hbound.2 output)
              | some result =>
                  rcases result with ⟨nextState, hit⟩
                  cases hit with
                  | false =>
                      simpa [runObserved, happly] using
                        ih output (some nextState) chainState fuel
                          (by simpa [IsHazardQuery] using hbound.2 output)
                  | true =>
                      simp [runObserved, happly]
                      apply OracleComp.ProgramLogic.Relational.spmf_map_const_of_no_failure
                      exact probFailure_of_liftM_PMF _
      | probe index target =>
          cases fuel with
          | zero => simp [IsHazardQuery] at hbound
          | succ remaining =>
              rw [eagerTrace_query_bind_run, runStructural_query_bind]
              simp only [eagerImpl, traceFragment, map_bind, runEagerQuery]
              cases hrevealed : chainState.revealed index with
              | none =>
                  simpa [runObserved, hrevealed] using
                    ih () encodingState (chainState.addPending index target)
                      remaining
                      (by simpa [IsHazardQuery] using hbound.2 ())
              | some value =>
                  simpa [runObserved, hrevealed] using
                    ih () encodingState chainState remaining
                      (by simpa [IsHazardQuery] using hbound.2 ())
      | reveal index =>
          rw [eagerTrace_query_bind_run, runStructural_query_bind]
          simp only [eagerImpl, traceFragment, map_bind, runEagerQuery]
          cases hrevealed : chainState.revealed index with
          | some value =>
              simpa [runObserved, hrevealed] using
                ih (table index) encodingState chainState fuel
                  (by simpa [IsHazardQuery] using hbound.2 (table index))
          | none =>
              by_cases hhit : table index ∈ chainState.pending index
              · simp [runObserved, hrevealed, hhit]
                apply OracleComp.ProgramLogic.Relational.spmf_map_const_of_no_failure
                exact probFailure_of_liftM_PMF _
              · simpa [runObserved, hrevealed, hhit] using
                  ih (table index) encodingState
                    (chainState.install index (table index)) fuel
                    (by simpa [IsHazardQuery] using hbound.2 (table index))

noncomputable def structuralExperiment
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (computation : OracleComp (World Index) α) : ProbComp Bool := do
  let base ← RevealProbeOracleSimulation.eagerTableSample
  runStructural (RevealProbeOracleSimulation.extendTable chainState base)
    encodingState chainState fuel computation

theorem structuralExperiment_query_bind
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (fuel : Nat) (input : (World Index).Domain)
    (next : (World Index).Range input → OracleComp (World Index) α) :
    structuralExperiment encodingState chainState fuel
        ((liftM (OracleSpec.query input) :
          OracleComp (World Index) ((World Index).Range input)) >>= next) =
      RevealProbeOracleSimulation.eagerTableSample >>= fun base =>
        runEagerQuery
          (RevealProbeOracleSimulation.extendTable chainState base)
          encodingState chainState fuel input fun output nextEncoding nextChain
            nextFuel =>
              runStructural
                (RevealProbeOracleSimulation.extendTable chainState base)
                nextEncoding nextChain nextFuel (next output) := by
  unfold structuralExperiment
  apply bind_congr
  intro base
  exact runStructural_query_bind _ _ _ _ _ _


theorem eagerFinalize_true_probability_le
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState)
    (fuel : Nat) :
    Pr[(fun hit : Bool => hit = true) |
      (fun base : Index → Digest =>
        RevealProbeOracleSimulation.tableHits chainState
          (RevealProbeOracleSimulation.extendTable chainState base)) <$>
        RevealProbeOracleSimulation.eagerTableSample] ≤
      potential fuel encodingState chainState := by
  refine (RevealProbeOracleSimulation.eagerFinalize_true_probability_le
    chainState hvalid).trans ?_
  unfold potential
  apply le_add_right
  gcongr
  omega

set_option maxRecDepth 100000 in
theorem structuralExperiment_true_probability_le
    (encodingState : Option EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid chainState)
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment encodingState chainState fuel computation] ≤
      potential fuel encodingState chainState := by
  induction computation using OracleComp.inductionOn generalizing
      encodingState chainState fuel with
  | pure result =>
      change Pr[(fun hit : Bool => hit = true) |
        (fun base : Index → Digest =>
          RevealProbeOracleSimulation.tableHits chainState
            (RevealProbeOracleSimulation.extendTable chainState base)) <$>
          RevealProbeOracleSimulation.eagerTableSample] ≤ _
      exact eagerFinalize_true_probability_le encodingState chainState hvalid fuel
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          have hdist :
              evalDist (structuralExperiment encodingState chainState fuel
                ((liftM (OracleSpec.query (spec := World Index) (.uniform n)) :
                  OracleComp (World Index) _) >>= next)) =
                evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                  structuralExperiment encodingState chainState fuel
                    (next output)) := by
            rw [structuralExperiment_query_bind]
            simp only [runEagerQuery]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          refine (probEvent_congr'
            (oa' := (liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
              structuralExperiment encodingState chainState fuel (next output))
            (fun _ _ => Iff.rfl) hdist).le.trans ?_
          exact probEvent_bind_le_of_forall_le fun output _ =>
            ih output encodingState chainState hvalid fuel
      | encodingQuery leafIndex =>
          cases fuel with
          | zero =>
              rw [structuralExperiment_query_bind]
              simp only [runEagerQuery]
              exact eagerFinalize_true_probability_le encodingState chainState
                hvalid 0
          | succ remaining =>
              let resume := fun output nextState =>
                structuralExperiment nextState chainState remaining (next output)
              have hdist :
                  evalDist (structuralExperiment encodingState chainState
                    (remaining + 1)
                    ((liftM (OracleSpec.query (spec := World Index)
                      (.encodingQuery leafIndex)) :
                      OracleComp (World Index) _) >>= next)) =
                    evalDist
                      (applyEncodingRequest (.query leafIndex) resume encodingState) := by
                rw [structuralExperiment_query_bind]
                simp only [runEagerQuery]
                simpa [resume, structuralExperiment] using
                  evalDist_sample_applyEncodingRequest
                    RevealProbeOracleSimulation.eagerTableSample
                    (by simp [RevealProbeOracleSimulation.eagerTableSample])
                    (.query leafIndex)
                    (fun base output nextState =>
                      runStructural
                        (RevealProbeOracleSimulation.extendTable chainState base)
                        nextState chainState remaining (next output))
                    encodingState
              refine (probEvent_congr'
                (oa' := applyEncodingRequest (.query leafIndex) resume encodingState)
                (fun _ _ => Iff.rfl) hdist).le.trans ?_
              simpa [resume, potential, EncodingRequest.cost,
                HiddenValue.card_digest, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                applyEncodingRequest_true_probability_le (.query leafIndex) resume
                  encodingState (remaining + chainState.pendingCount)
                  (fun output nextState => by
                    simpa [resume, potential, HiddenValue.card_digest] using
                      ih output nextState chainState hvalid remaining)
      | encodingSignAttempt leafIndex =>
          let resume := fun output nextState =>
            structuralExperiment nextState chainState fuel (next output)
          have hdist :
              evalDist (structuralExperiment encodingState chainState fuel
                ((liftM (OracleSpec.query (spec := World Index)
                  (.encodingSignAttempt leafIndex)) :
                  OracleComp (World Index) _) >>= next)) =
                evalDist
                  (applyEncodingRequest (.sign leafIndex) resume encodingState) := by
            rw [structuralExperiment_query_bind]
            simp only [runEagerQuery]
            simpa [resume, structuralExperiment] using
              evalDist_sample_applyEncodingRequest
                RevealProbeOracleSimulation.eagerTableSample
                (by simp [RevealProbeOracleSimulation.eagerTableSample])
                (.sign leafIndex)
                (fun base output nextState =>
                  runStructural
                    (RevealProbeOracleSimulation.extendTable chainState base)
                    nextState chainState fuel (next output))
                encodingState
          refine (probEvent_congr'
            (oa' := applyEncodingRequest (.sign leafIndex) resume encodingState)
            (fun _ _ => Iff.rfl) hdist).le.trans ?_
          simpa [resume, potential, EncodingRequest.cost,
            HiddenValue.card_digest] using
            applyEncodingRequest_true_probability_le (.sign leafIndex) resume
              encodingState (fuel + chainState.pendingCount)
              (fun output nextState => by
                simpa [resume, potential, HiddenValue.card_digest] using
                  ih output nextState chainState hvalid fuel)
      | probe index target =>
          cases fuel with
          | zero =>
              rw [structuralExperiment_query_bind]
              simp only [runEagerQuery]
              exact eagerFinalize_true_probability_le encodingState chainState
                hvalid 0
          | succ remaining =>
              cases hrevealed : chainState.revealed index with
              | some value =>
                  rw [structuralExperiment_query_bind]
                  simp only [runEagerQuery, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    structuralExperiment encodingState chainState remaining
                      (next ())] ≤ _
                  refine (ih () encodingState chainState hvalid remaining).trans ?_
                  unfold potential
                  gcongr
                  omega
              | none =>
                  rw [structuralExperiment_query_bind]
                  simp only [runEagerQuery, hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    structuralExperiment encodingState
                      (chainState.addPending index target) remaining
                        (next ())] ≤ _
                  refine (ih () encodingState
                    (chainState.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining).trans ?_
                  unfold potential
                  have hnat : remaining +
                      (chainState.addPending index target).pendingCount ≤
                    remaining + 1 + chainState.pendingCount := by
                      have := chainState.pendingCount_addPending_le index target
                      omega
                  exact add_le_add
                    (mul_le_mul_left
                      (by exact_mod_cast hnat :
                        ((remaining +
                          (chainState.addPending index target).pendingCount : Nat) :
                            ENNReal) ≤
                          ((remaining + 1 + chainState.pendingCount : Nat) :
                            ENNReal)) _)
                    le_rfl
      | reveal index =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              rw [structuralExperiment_query_bind]
              simp only [runEagerQuery, hrevealed]
              simp only [RevealProbeOracleSimulation.extendTable, hrevealed,
                Option.getD_some]
              change Pr[(fun hit : Bool => hit = true) |
                structuralExperiment encodingState chainState fuel
                  (next value)] ≤ _
              exact ih value encodingState chainState hvalid fuel
          | none =>
              let resume := fun value nextState =>
                structuralExperiment encodingState nextState fuel (next value)
              have hdist :
                  evalDist (structuralExperiment encodingState chainState fuel
                    ((liftM (OracleSpec.query (spec := World Index)
                      (.reveal index)) :
                      OracleComp (World Index) _) >>= next)) =
                    evalDist (applyRevealRequest chainState index resume) := by
                rw [structuralExperiment_query_bind]
                simp only [runEagerQuery, hrevealed]
                simpa [resume, structuralExperiment] using
                  evalDist_eagerTableSample_applyRevealRequest chainState index
                    hrevealed fun table value nextState =>
                      runStructural table encodingState nextState fuel
                        (next value)
              refine (probEvent_congr'
                (oa' := applyRevealRequest chainState index resume)
                (fun _ _ => Iff.rfl) hdist).le.trans ?_
              simpa [resume, potential] using
                applyRevealRequest_true_probability_le chainState index resume
                  fuel (encodingPendingRisk encodingState) fun value => by
                    exact ih value encodingState
                      (chainState.install index value)
                      (hvalid.install index value) fuel

theorem combinedHit_probability_eq_structuralExperiment
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    Pr[fun result : (Index → Digest) × (α × ActionTrace Index) =>
        CombinedHit result.1 result.2.2 |
      eagerExperiment computation] =
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation] := by
  unfold eagerExperiment structuralExperiment
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  congr 1
  rw [show (do
      let result ← (simulateQ (eagerTraceImpl table) computation).run
      pure (table, result)) =
    Prod.mk table <$> (simulateQ (eagerTraceImpl table) computation).run by rfl]
  rw [probEvent_map]
  change Pr[(fun result => CombinedHit table result.2) |
      (simulateQ (eagerTraceImpl table) computation).run] =
    Pr[(fun hit : Bool => hit = true) |
      runStructural table (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation]
  calc
    _ = Pr[(fun hit : Bool => hit = true) |
        (runObserved table (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty ∘ Prod.snd) <$>
            (simulateQ (eagerTraceImpl table) computation).run] := by
      rw [probEvent_map]
      apply probEvent_congr' (oa' :=
        (simulateQ (eagerTraceImpl table) computation).run)
      · intro result _
        exact (runObserved_empty_eq_combinedHit table result.2).symm
      · rfl
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_runObserved_eagerTrace_eq_runStructural table
        (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation hbound)

theorem structuralExperiment_empty_true_probability_le
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(fun hit : Bool => hit = true) |
      structuralExperiment (some EncodingMonitor.State.empty)
        AdaptiveRevealMonitor.State.empty fuel computation] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  simpa [potential, encodingPendingRisk,
    AdaptiveRevealMonitor.State.pendingCount_empty,
    CappedEncodingMonitor.State.pendingRisk_empty, div_eq_mul_inv] using
      structuralExperiment_true_probability_le
        (some EncodingMonitor.State.empty)
        (AdaptiveRevealMonitor.State.empty :
          AdaptiveRevealMonitor.State Index)
        RevealProbeOracleSimulation.stateValid_empty fuel computation

end XmssSecurity.FirstLaneOracleSimulation
