import XmssSecurity.Proof.CappedGlobalChainHighReduction
import XmssSecurity.Proof.FirstLaneOracleSimulation
import XmssSecurity.Proof.CappedEncodingActionTrace
import XmssSecurity.Proof.FirstLaneEagerSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

abbrev GlobalFirstLaneWorld :=
  FirstLaneOracleSimulation.World GlobalChainValueIndex

def globalFirstLaneRevealProbeImpl :
    QueryImpl (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (OracleComp GlobalFirstLaneWorld) := fun input =>
  match input with
  | .uniform n => FirstLaneOracleSimulation.uniformQuery n
  | .probe index target => FirstLaneOracleSimulation.probeQuery index target
  | .reveal index => FirstLaneOracleSimulation.revealQuery index

def globalFirstLaneLiftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    OracleComp GlobalFirstLaneWorld α :=
  simulateQ globalFirstLaneRevealProbeImpl computation

noncomputable def globalFirstLaneFreshEncodingQuery
    (kind : EncodingSampleKind) (leafIndex : LeafIndex) (input : HashInput)
    (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) := do
  let output ← match kind with
    | .query => FirstLaneOracleSimulation.encodingQuery leafIndex
    | .sign => FirstLaneOracleSimulation.encodingSignAttemptQuery leafIndex
    | .side => FirstLaneOracleSimulation.liftProbComp uniformHashOutput
  pure (output, state.setCache (state.cache.cacheQuery input output))

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryAtLeafIndex
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (leafIndex : LeafIndex) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  let recorded := globalCausalRecordedState secretKey input state
  match state.cache input with
  | some output => pure (output, recorded)
  | none => globalFirstLaneFreshEncodingQuery .query leafIndex input recorded

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryByLeafIndex
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : Option LeafIndex →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState)
  | some leafIndex => globalFirstLaneAttackerHashQueryAtLeafIndex secretKey input state leafIndex
  | none =>
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)

@[irreducible]
noncomputable def globalFirstLaneAttackerHashQueryFromHighRun
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  fun state => globalFirstLaneAttackerHashQueryByLeafIndex high secretKey input state
    (encodingInputLeafIndex? secretKey.parameter input)

theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_some
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (leafIndex : LeafIndex)
    (hleafIndex : encodingInputLeafIndex? secretKey.parameter input = some leafIndex) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneAttackerHashQueryAtLeafIndex secretKey input state leafIndex := by
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  rw [hleafIndex]
  unfold globalFirstLaneAttackerHashQueryByLeafIndex
  rfl

theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_none
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hleafIndex : encodingInputLeafIndex? secretKey.parameter input = none) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state) := by
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  rw [hleafIndex]
  unfold globalFirstLaneAttackerHashQueryByLeafIndex
  rfl

theorem globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (leafIndex : LeafIndex) (output : HashOutput)
    (hcache : state.cache input = some output) :
    globalFirstLaneAttackerHashQueryAtLeafIndex secretKey input state leafIndex =
      pure (output, globalCausalRecordedState secretKey input state) := by
  unfold globalFirstLaneAttackerHashQueryAtLeafIndex
  rw [hcache]

theorem globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (leafIndex : LeafIndex)
    (hcache : state.cache input = none) :
    globalFirstLaneAttackerHashQueryAtLeafIndex secretKey input state leafIndex =
      globalFirstLaneFreshEncodingQuery .query leafIndex input
        (globalCausalRecordedState secretKey input state) := by
  unfold globalFirstLaneAttackerHashQueryAtLeafIndex
  rw [hcache]

noncomputable def globalFirstLaneEncodingHashQuery
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld (HashOutput × GlobalCausalHashState) :=
  let input := Concrete.CacheView.encodingInput secretKey.parameter leafIndex
    (message, randomness)
  match state.cache input with
  | some output => pure (output, state)
  | none => globalFirstLaneFreshEncodingQuery .sign leafIndex input state

noncomputable def globalFirstLaneSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState) := do
  let encoded ← globalFirstLaneEncodingHashQuery keyView.secretKey
    request.leafIndex request.message randomness state
  match TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← globalFirstLaneLiftRevealProbe
        ((revealGlobalSignature keyView.secretKey.topSigned request encoding
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.leafIndex randomness encoding)).run encoded.2)
      pure (some result.1, result.2)

noncomputable def globalFirstLaneSignBoundedAttempts
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest) (base : Randomness) :
    Nat → Nat → GlobalCausalHashState →
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState)
  | 0, _trial, state => pure (none, state)
  | attempts + 1, trial, state => do
      let result ← globalFirstLaneSigningAttempt keyView request
        (base + BitVec.ofNat randomnessBits trial) state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFirstLaneSignBoundedAttempts keyView request base attempts (trial + 1) result.2

noncomputable def globalFirstLaneSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (Option Signature × GlobalCausalHashState) := do
  let base ← FirstLaneOracleSimulation.liftProbComp Concrete.signingRandomness
  let result ← globalFirstLaneSignBoundedAttempts keyView request base signingAttemptLimit 0
    state
  pure (topSignedResult keyView request result)

def globalFirstLaneUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) := fun n state => do
  let output ← FirstLaneOracleSimulation.uniformQuery n
  pure (output, state)

noncomputable abbrev globalFirstLaneHashFromHighImpl
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input state =>
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state

noncomputable abbrev globalFirstLaneHashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneHashFromHighImpl
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey

noncomputable def globalFirstLaneOracleExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    OracleComp GlobalFirstLaneWorld
      (OracleWorld.Range input × GlobalCausalHashState) :=
  match input with
  | .inl n => (globalFirstLaneUniformImpl n).run state
  | .inr hashInput =>
      globalFirstLaneAttackerHashQueryFromHighRun
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
          state

noncomputable def globalFirstLaneOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input state => globalFirstLaneOracleExecution keyView edgeHigh input state

noncomputable def globalFirstLaneSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneSigningQuery keyView

noncomputable def globalFirstLaneVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneOracleImpl keyView edgeHigh


set_option maxRecDepth 1000000

theorem globalFirstLaneUniformQuery_hazardBound (n : Nat) :
    (FirstLaneOracleSimulation.uniformQuery
      (Index := GlobalChainValueIndex) n).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.uniformQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneEncodingQuery_hazardBound (leafIndex : LeafIndex) :
    (FirstLaneOracleSimulation.encodingQuery
      (Index := GlobalChainValueIndex) leafIndex).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 1 := by
  rw [FirstLaneOracleSimulation.encodingQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneEncodingSignAttemptQuery_hazardBound (leafIndex : LeafIndex) :
    (FirstLaneOracleSimulation.encodingSignAttemptQuery
      (Index := GlobalChainValueIndex) leafIndex).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.encodingSignAttemptQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneProbeQuery_hazardBound
    (index : GlobalChainValueIndex) (target : Digest) :
    (FirstLaneOracleSimulation.probeQuery index target).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 1 := by
  rw [FirstLaneOracleSimulation.probeQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneRevealQuery_hazardBound
    (index : GlobalChainValueIndex) :
    (FirstLaneOracleSimulation.revealQuery index).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.revealQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneLiftProbComp_hazardBound
    (computation : ProbComp α) :
    (FirstLaneOracleSimulation.liftProbComp
      (Index := GlobalChainValueIndex) computation).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold FirstLaneOracleSimulation.liftProbComp
  apply OracleComp.IsQueryBoundP.simulateQ_of_step
    (p := fun _ : unifSpec.Domain => False)
    (q := FirstLaneOracleSimulation.IsHazardQuery)
    (OracleComp.isQueryBoundP_false computation 0)
  · intro input hfalse
    exact hfalse.elim
  · intro input _
    exact globalFirstLaneUniformQuery_hazardBound input

theorem globalFirstLaneLiftRevealProbe_hazardBound
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery fuel) :
    (globalFirstLaneLiftRevealProbe computation).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalFirstLaneLiftRevealProbe
  apply OracleComp.IsQueryBoundP.simulateQ_of_step hbound
  · intro input hprobe
    cases input with
    | uniform n => simp [RevealProbeOracleSimulation.IsProbeQuery] at hprobe
    | probe index target => exact globalFirstLaneProbeQuery_hazardBound index target
    | reveal index => simp [RevealProbeOracleSimulation.IsProbeQuery] at hprobe
  · intro input hnotProbe
    cases input with
    | uniform n => exact globalFirstLaneUniformQuery_hazardBound n
    | probe index target =>
        simp [RevealProbeOracleSimulation.IsProbeQuery] at hnotProbe
    | reveal index => exact globalFirstLaneRevealQuery_hazardBound index

theorem globalFirstLaneFreshEncodingQuery_hazardBound
    (kind : EncodingSampleKind) (leafIndex : LeafIndex) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalFirstLaneFreshEncodingQuery kind leafIndex input state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery
        (if kind = .query then 1 else 0) := by
  unfold globalFirstLaneFreshEncodingQuery
  cases kind with
  | side =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneLiftProbComp_hazardBound uniformHashOutput)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | query =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (globalFirstLaneEncodingQuery_hazardBound leafIndex)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | sign =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneEncodingSignAttemptQuery_hazardBound leafIndex)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneAttackerHashQueryFromHigh_hazardBound
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 1 := by
  cases hleafIndex : encodingInputLeafIndex? secretKey.parameter input with
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey
        input state hleafIndex]
      exact globalFirstLaneLiftRevealProbe_hazardBound
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state) 1
        (globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP high secretKey
          input state)
  | some leafIndex =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
        input state leafIndex hleafIndex]
      cases hcache : state.cache input with
      | none =>
          rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh secretKey input
            state leafIndex hcache]
          exact globalFirstLaneFreshEncodingQuery_hazardBound .query leafIndex
            input (globalCausalRecordedState secretKey input state)
      | some output =>
          rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached secretKey input
            state leafIndex output hcache]
          exact (OracleComp.isQueryBoundP_pure
            (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0).mono (by omega)

theorem globalFirstLaneEncodingHashQuery_hazardBound
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    (globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneEncodingHashQuery
  let input := Concrete.CacheView.encodingInput secretKey.parameter leafIndex
    (message, randomness)
  change (match state.cache input with
    | some output => pure (output, state)
    | none => globalFirstLaneFreshEncodingQuery .sign leafIndex input state
    ).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0
  cases hcache : state.cache input with
  | none =>
      exact globalFirstLaneFreshEncodingQuery_hazardBound .sign leafIndex input state
  | some output =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSigningAttempt_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    (globalFirstLaneSigningAttempt keyView request randomness state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneSigningAttempt
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneEncodingHashQuery_hazardBound keyView.secretKey
      request.leafIndex request.message randomness state)
  intro encoded _
  cases hdecode : TargetSum.decodeDigest (truncateHash encoded.1) with
  | none =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | some encoding =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      · apply globalFirstLaneLiftRevealProbe_hazardBound
        exact revealGlobalSignature_run_isProbeQueryBoundP keyView.secretKey.topSigned request
          encoding (Concrete.CacheReplay.signWithEncoding keyView.cache
            keyView.secretKey request.leafIndex randomness encoding) encoded.2
      · intro result _
        exact OracleComp.isQueryBoundP_pure
          (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSignBoundedAttempts_hazardBound
    (attempts trial : Nat) (base : Randomness) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFirstLaneSignBoundedAttempts keyView request base attempts trial state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  induction attempts generalizing trial state with
  | zero =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneSigningAttempt_hazardBound keyView request _ state)
      intro result _
      cases hsignature : result.1 with
      | none =>
          exact ih (trial + 1) result.2
      | some signature =>
          exact OracleComp.isQueryBoundP_pure
            (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSigningQuery_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFirstLaneSigningQuery keyView request state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneSigningQuery
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneLiftProbComp_hazardBound Concrete.signingRandomness)
  intro base _
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneSignBoundedAttempts_hazardBound signingAttemptLimit 0 base
      keyView request state)
  intro result _
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneUniformImpl_hazardBound
    (n : Nat) (state : GlobalCausalHashState) :
    ((globalFirstLaneUniformImpl n).run state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneUniformImpl
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneUniformQuery_hazardBound n)
  intro output _
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneOracleExecution_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    (globalFirstLaneOracleExecution keyView edgeHigh input state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  cases input with
  | inl n =>
      exact globalFirstLaneUniformImpl_hazardBound n state
  | inr input =>
      exact globalFirstLaneAttackerHashQueryFromHigh_hazardBound
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input state

theorem globalFirstLaneOracleImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    ((globalFirstLaneOracleImpl keyView edgeHigh input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  exact globalFirstLaneOracleExecution_hazardBound keyView edgeHigh input state

theorem globalFirstLaneSigningImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SigningSpec.Domain) (state : GlobalCausalHashState) :
    ((globalFirstLaneSigningImpl keyView request).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  exact globalFirstLaneSigningQuery_hazardBound keyView request state


noncomputable def globalFirstLaneEraseImpl :
    QueryImpl GlobalFirstLaneWorld
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex)) := fun input =>
  match input with
  | .uniform n => RevealProbeOracleSimulation.uniformQuery n
  | .encodingQuery _ =>
      RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  | .encodingSignAttempt _ =>
      RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  | .probe index target => RevealProbeOracleSimulation.probeQuery index target
  | .reveal index => RevealProbeOracleSimulation.revealQuery index

noncomputable def globalFirstLaneErase
    (computation : OracleComp GlobalFirstLaneWorld α) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) α :=
  simulateQ globalFirstLaneEraseImpl computation

abbrev GlobalFirstLaneErases
    (source : OracleComp GlobalFirstLaneWorld α)
    (target : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) : Prop :=
  globalFirstLaneErase source = target

theorem GlobalFirstLaneErases.bind
    (hsource : GlobalFirstLaneErases source target)
    (hnext : ∀ result, GlobalFirstLaneErases (nextSource result)
      (nextTarget result)) :
    GlobalFirstLaneErases (source >>= nextSource) (target >>= nextTarget) := by
  change globalFirstLaneErase (source >>= nextSource) = target >>= nextTarget
  rw [globalFirstLaneErase, simulateQ_bind]
  change globalFirstLaneErase source >>= _ = _
  rw [hsource]
  apply bind_congr
  exact hnext

theorem GlobalFirstLaneErases.pure (result : α) :
    GlobalFirstLaneErases (pure result) (pure result) := by
  unfold GlobalFirstLaneErases
  simp [globalFirstLaneErase]

theorem globalFirstLaneErases_simulateQ_run
    (sourceImpl : QueryImpl spec
      (StateT stateType (OracleComp GlobalFirstLaneWorld)))
    (targetImpl : QueryImpl spec
      (StateT stateType
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (himpl : ∀ input state,
      GlobalFirstLaneErases ((sourceImpl input).run state)
        ((targetImpl input).run state))
    (computation : OracleComp spec α) (state : stateType) :
    GlobalFirstLaneErases
      ((simulateQ sourceImpl computation).run state)
      ((simulateQ targetImpl computation).run state) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => exact GlobalFirstLaneErases.pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply (himpl input state).bind
      intro result
      exact ih result.1 result.2

theorem globalFirstLaneErase_liftProbComp (computation : ProbComp α) :
    globalFirstLaneErase
      (FirstLaneOracleSimulation.liftProbComp
        (Index := GlobalChainValueIndex) computation) =
    RevealProbeOracleSimulation.liftProbComp computation := by
  unfold globalFirstLaneErase FirstLaneOracleSimulation.liftProbComp
    RevealProbeOracleSimulation.liftProbComp
  rw [← QueryImpl.simulateQ_compose]
  congr 1

theorem globalFirstLaneErases_liftProbComp (computation : ProbComp α) :
    GlobalFirstLaneErases
      (FirstLaneOracleSimulation.liftProbComp
        (Index := GlobalChainValueIndex) computation)
      (RevealProbeOracleSimulation.liftProbComp computation) :=
  globalFirstLaneErase_liftProbComp computation

theorem globalFirstLaneErases_uniformQuery (n : Nat) :
    GlobalFirstLaneErases
      (FirstLaneOracleSimulation.uniformQuery
        (Index := GlobalChainValueIndex) n)
      (RevealProbeOracleSimulation.uniformQuery
        (Index := GlobalChainValueIndex) n) := by
  unfold GlobalFirstLaneErases
  simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
    FirstLaneOracleSimulation.uniformQuery,
    RevealProbeOracleSimulation.uniformQuery]

theorem globalFirstLaneErase_liftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    globalFirstLaneErase (globalFirstLaneLiftRevealProbe computation) =
      computation := by
  unfold globalFirstLaneErase globalFirstLaneLiftRevealProbe
  rw [← QueryImpl.simulateQ_compose]
  have himpl : globalFirstLaneEraseImpl ∘ₛ globalFirstLaneRevealProbeImpl =
      QueryImpl.id'
        (RevealProbeOracleSimulation.World GlobalChainValueIndex) := by
    funext input
    cases input <;>
      simp [globalFirstLaneEraseImpl, globalFirstLaneRevealProbeImpl,
        FirstLaneOracleSimulation.uniformQuery,
        RevealProbeOracleSimulation.uniformQuery,
        FirstLaneOracleSimulation.probeQuery,
        RevealProbeOracleSimulation.probeQuery,
        FirstLaneOracleSimulation.revealQuery,
        RevealProbeOracleSimulation.revealQuery, QueryImpl.id']
  rw [himpl]
  simp

theorem globalFirstLaneErases_liftRevealProbe
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    GlobalFirstLaneErases (globalFirstLaneLiftRevealProbe computation)
      computation :=
  globalFirstLaneErase_liftRevealProbe computation

theorem GlobalFirstLaneErases.of_eq_liftRevealProbe
    (source : OracleComp GlobalFirstLaneWorld α)
    (target : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (hsource : source = globalFirstLaneLiftRevealProbe target) :
    GlobalFirstLaneErases source target := by
  rw [hsource]
  exact globalFirstLaneErases_liftRevealProbe target

noncomputable def globalFirstLaneErasedFreshQuery
    (input : HashInput) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let output ← RevealProbeOracleSimulation.liftProbComp uniformHashOutput
  pure (output, state.setCache (state.cache.cacheQuery input output))

theorem globalFirstLaneErase_freshEncodingQuery
    (kind : EncodingSampleKind) (leafIndex : LeafIndex) (input : HashInput)
    (state : GlobalCausalHashState) :
    globalFirstLaneErase
      (globalFirstLaneFreshEncodingQuery kind leafIndex input state) =
      globalFirstLaneErasedFreshQuery input state := by
  unfold globalFirstLaneErasedFreshQuery
  unfold globalFirstLaneFreshEncodingQuery
  cases kind with
  | side =>
      change globalFirstLaneErase
        (FirstLaneOracleSimulation.liftProbComp uniformHashOutput >>= fun output =>
          pure (output,
            state.setCache (state.cache.cacheQuery input output))) = _
      rw [globalFirstLaneErase, simulateQ_bind]
      change globalFirstLaneErase
          (FirstLaneOracleSimulation.liftProbComp uniformHashOutput) >>= _ = _
      rw [globalFirstLaneErase_liftProbComp]
      simp
  | query =>
      simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
        FirstLaneOracleSimulation.encodingQuery]
  | sign =>
      simp [globalFirstLaneErase, globalFirstLaneEraseImpl,
        FirstLaneOracleSimulation.encodingSignAttemptQuery]

@[simp]
theorem globalFirstLane_globalLeafInputData_encodingInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (payload : Message × Randomness) :
    globalLeafInputData? parameter
      (Concrete.CacheView.encodingInput parameter leafIndex payload) = none := by
  unfold globalLeafInputData?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata.symm
    generalize data.leafIndex = key at hdomain
    cases key <;> cases hdomain
  · rfl

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_cached
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
        some output) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state) =
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          ).run state) := by
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
    (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) state
    leafIndex (encodingInputLeafIndex?_encodingInput secretKey.parameter leafIndex payload)]
  rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcache]
  have hplan : globalFilteredCausalAttackerHashPlan secretKey
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
        state = .cached output := by
    rw [globalFilteredCausalAttackerHashPlan, hcache]
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan]
  change globalFirstLaneErase
      (pure (output, globalCausalRecordedState secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state)) = _
  simp [globalFirstLaneErase]

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_source
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
        none) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state) = globalFirstLaneErasedFreshQuery
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
        (globalCausalRecordedState secretKey
          (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
            state) := by
  rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some high secretKey
    (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) state
    leafIndex (encodingInputLeafIndex?_encodingInput secretKey.parameter leafIndex payload)]
  rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcache]
  rw [globalFirstLaneErase_freshEncodingQuery]

theorem globalCausalHashQuery_eq_globalFirstLaneErasedFreshQuery
    (input : HashInput) (state : GlobalCausalHashState)
    (hcache : state.cache input = none) :
    (globalCausalHashQuery input).run state =
      globalFirstLaneErasedFreshQuery input state := by
  rw [globalCausalHashQuery_run,
    randomOracle_run_none_eq_uniformHashOutput _ _ hcache]
  unfold globalFirstLaneErasedFreshQuery
  simp [RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
    Functor.map_map]

theorem globalCausalAttackerHashQueryFromHigh_fresh_eq_hashQuery
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      (globalCausalHashQuery input).run
        (globalCausalRecordedState secretKey input state) := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan]

theorem globalCausalAttackerHashQueryFromHigh_fresh_eq_erasedFresh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh)
    (hcache : state.cache input = none) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      globalFirstLaneErasedFreshQuery input
        (globalCausalRecordedState secretKey input state) :=
  (globalCausalAttackerHashQueryFromHigh_fresh_eq_hashQuery high secretKey input
    state hplan).trans
      (globalCausalHashQuery_eq_globalFirstLaneErasedFreshQuery input
        (globalCausalRecordedState secretKey input state) (by simpa using hcache))

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_target
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
        none) :
    ((globalCausalAttackerHashQueryFromHigh high secretKey
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
        ).run state) = globalFirstLaneErasedFreshQuery
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
      (globalCausalRecordedState secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state) := by
  let input := Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload
  change (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
    globalFirstLaneErasedFreshQuery input
      (globalCausalRecordedState secretKey input state)
  have hcache' : state.cache input = none := by simpa [input] using hcache
  have hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh := by
    apply globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh secretKey state
      input hcache'
    · simp [input]
    · simp [input]
  exact globalCausalAttackerHashQueryFromHigh_fresh_eq_erasedFresh high secretKey
    input state hplan hcache'

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (state : GlobalCausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
        none) :
    globalFirstLaneErase
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state) =
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          ).run state) := by
  rw [globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_source
    high secretKey leafIndex payload state hcache]
  exact (globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh_target
    high secretKey leafIndex payload state hcache).symm

theorem globalFirstLaneErase_attackerHashQueryFromHigh_encoding
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          state)
      ((globalCausalAttackerHashQueryFromHigh high secretKey
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload)
          ).run state) := by
  unfold GlobalFirstLaneErases
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) with
  | some output =>
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding_cached
        high secretKey leafIndex payload state output hcache
  | none =>
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding_fresh
        high secretKey leafIndex payload state hcache

noncomputable def globalFirstLaneErasedEncodingHashQuery
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let input := Concrete.CacheView.encodingInput secretKey.parameter leafIndex
    (message, randomness)
  let result ← RevealProbeOracleSimulation.liftProbComp
    ((randomOracle input).run state.cache)
  pure (result.1, state.setCache result.2)

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_encodingHashQuery
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)
      (globalFirstLaneErasedEncodingHashQuery secretKey leafIndex message randomness
        state) := by
  unfold GlobalFirstLaneErases
  unfold globalFirstLaneEncodingHashQuery
  unfold globalFirstLaneErasedEncodingHashQuery
  dsimp only
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness)) with
  | some output =>
      simp [hcache, randomOracle, globalFirstLaneErase,
        RevealProbeOracleSimulation.liftProbComp,
        GlobalCausalHashState.setCache]
  | none =>
      simp only
      rw [globalFirstLaneErase_freshEncodingQuery]
      unfold globalFirstLaneErasedFreshQuery
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcache]
      simp [RevealProbeOracleSimulation.liftProbComp, simulateQ_map,
        Functor.map_map, GlobalCausalHashState.setCache]

noncomputable def globalFirstLaneErasedEncodingDigestQuery
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Digest × GlobalCausalHashState) := do
  let result ← globalFirstLaneErasedEncodingHashQuery secretKey leafIndex message
    randomness state
  pure (truncateHash result.1, result.2)

noncomputable def globalFirstLaneOriginalEncodingDigestQuery
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Digest × GlobalCausalHashState) := do
  let result ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash secretKey.parameter leafIndex message randomness)).run
        state.cache)
  pure (result.1, state.setCache result.2)

theorem globalFirstLaneErasedEncodingDigestQuery_eq_original
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    globalFirstLaneErasedEncodingDigestQuery secretKey leafIndex message randomness
      state =
    globalFirstLaneOriginalEncodingDigestQuery secretKey leafIndex message randomness
      state := by
  simp [globalFirstLaneErasedEncodingDigestQuery,
    globalFirstLaneErasedEncodingHashQuery,
    globalFirstLaneOriginalEncodingDigestQuery, Concrete.encodingHash,
    Concrete.tweakableHash, Concrete.oracleHash, Concrete.CacheView.encodingInput,
    RevealProbeOracleSimulation.liftProbComp,
    map_eq_bind_pure_comp, GlobalCausalHashState.setCache]

theorem globalFirstLaneOriginalEncodingDigestQuery_bind
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (next : Digest × GlobalCausalHashState →
      OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    globalFirstLaneOriginalEncodingDigestQuery secretKey leafIndex message
        randomness state >>= next =
      RevealProbeOracleSimulation.liftProbComp
          ((simulateQ randomOracle
            (Concrete.encodingHash secretKey.parameter leafIndex message
              randomness)).run state.cache) >>= fun encoded =>
        next (encoded.1, state.setCache encoded.2) := by
  simp [globalFirstLaneOriginalEncodingDigestQuery]

noncomputable def globalFirstLaneErasedSigningAttemptRaw
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let encoded ← globalFirstLaneErasedEncodingHashQuery keyView.secretKey
    request.leafIndex request.message randomness state
  match TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← (revealGlobalSignature keyView.secretKey.topSigned request encoding
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.leafIndex randomness encoding)).run encoded.2
      pure (some result.1, result.2)

set_option maxRecDepth 1000000 in
theorem globalFirstLaneErase_signingAttempt_raw
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningAttempt keyView request randomness state)
      (globalFirstLaneErasedSigningAttemptRaw keyView request randomness state) := by
  unfold globalFirstLaneSigningAttempt
  unfold globalFirstLaneErasedSigningAttemptRaw
  apply (globalFirstLaneErase_encodingHashQuery keyView.secretKey request.leafIndex
    request.message randomness state).bind
  intro encoded
  cases hdecode : TargetSum.decodeDigest (truncateHash encoded.1) with
  | none => exact GlobalFirstLaneErases.pure _
  | some encoding =>
      apply (globalFirstLaneErases_liftRevealProbe
        ((revealGlobalSignature keyView.secretKey.topSigned request encoding
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.leafIndex randomness encoding)).run encoded.2)).bind
      exact fun result => GlobalFirstLaneErases.pure _

noncomputable def globalFirstLaneErasedSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let encoded ← globalFirstLaneErasedEncodingDigestQuery keyView.secretKey
    request.leafIndex request.message randomness state
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encoded.2)
  | some encoding => do
      let result ← (revealGlobalSignature keyView.secretKey.topSigned request encoding
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.leafIndex randomness encoding)).run encoded.2
      pure (some result.1, result.2)

theorem globalFirstLaneErasedSigningAttemptRaw_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    globalFirstLaneErasedSigningAttemptRaw keyView request randomness state =
      globalFirstLaneErasedSigningAttempt keyView request randomness state := by
  simp [globalFirstLaneErasedSigningAttemptRaw,
    globalFirstLaneErasedSigningAttempt,
    globalFirstLaneErasedEncodingDigestQuery]

theorem globalFirstLaneErasedSigningAttempt_eq_original
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    globalFirstLaneErasedSigningAttempt keyView request randomness state =
      globalFilteredCausalSigningAttempt keyView request randomness state := by
  unfold globalFirstLaneErasedSigningAttempt
  unfold globalFilteredCausalSigningAttempt
  rw [globalFirstLaneErasedEncodingDigestQuery_eq_original]
  rw [globalFirstLaneOriginalEncodingDigestQuery_bind]
  rfl

theorem globalFirstLaneErase_signingAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningAttempt keyView request randomness state)
      (globalFilteredCausalSigningAttempt keyView request randomness state) := by
  unfold GlobalFirstLaneErases
  rw [globalFirstLaneErase_signingAttempt_raw keyView request randomness state,
    globalFirstLaneErasedSigningAttemptRaw_eq,
    globalFirstLaneErasedSigningAttempt_eq_original]

theorem globalFirstLaneErase_signBoundedAttempts
    (attempts trial : Nat) (base : Randomness) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSignBoundedAttempts keyView request base attempts trial state)
      (globalFilteredCausalSignBoundedAttempts keyView request base attempts trial state) := by
  induction attempts generalizing trial state with
  | zero => exact GlobalFirstLaneErases.pure _
  | succ attempts ih =>
      unfold globalFirstLaneSignBoundedAttempts
      unfold globalFilteredCausalSignBoundedAttempts
      apply (globalFirstLaneErase_signingAttempt keyView request _ state).bind
      intro result
      cases result.1 with
      | none => exact ih (trial + 1) result.2
      | some signature => exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_signingQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      (globalFirstLaneSigningQuery keyView request state)
      (globalFilteredCausalSigningQuery keyView request state) := by
  unfold globalFirstLaneSigningQuery globalFilteredCausalSigningQuery
  apply (globalFirstLaneErases_liftProbComp Concrete.signingRandomness).bind
  intro base
  apply (globalFirstLaneErase_signBoundedAttempts signingAttemptLimit 0 base keyView
    request state).bind
  exact fun result => GlobalFirstLaneErases.pure _

set_option maxRecDepth 1000000 in
theorem globalFirstLaneAttackerHashQueryFromHighRun_eq_lift_of_none
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hleafIndex : encodingInputLeafIndex? secretKey.parameter input = none) :
    globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state =
      globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state) := by
  exact globalFirstLaneAttackerHashQueryFromHighRun_eq_none high secretKey input
    state hleafIndex

set_option maxRecDepth 100000 in
theorem globalFirstLaneErase_attackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    GlobalFirstLaneErases (α := HashOutput × GlobalCausalHashState)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
        state) := by
  cases hleafIndex : encodingInputLeafIndex? secretKey.parameter input with
  | none =>
      apply GlobalFirstLaneErases.of_eq_liftRevealProbe
      exact globalFirstLaneAttackerHashQueryFromHighRun_eq_lift_of_none high
        secretKey input state hleafIndex
  | some leafIndex =>
      obtain ⟨payload, hinput⟩ :=
        exists_encodingInput_of_encodingInputLeafIndex?_eq_some secretKey.parameter
          input leafIndex hleafIndex
      subst input
      exact globalFirstLaneErase_attackerHashQueryFromHigh_encoding high
        secretKey leafIndex payload state

theorem globalFirstLaneErase_uniformImpl
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneUniformImpl n).run state)
      ((globalCausalUniformImpl n).run state) := by
  unfold globalFirstLaneUniformImpl
  unfold globalCausalUniformImpl
  apply (globalFirstLaneErases_uniformQuery n).bind
  exact fun output => GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_signingImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneSigningImpl keyView request).run state)
      (globalFilteredCausalSigningQuery keyView request state) := by
  exact globalFirstLaneErase_signingQuery keyView request state

theorem globalFirstLaneErase_directUniformImpl
    (n : Nat) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneUniformImpl n).run state)
      ((globalHighDirectUniformImpl n).run state) := by
  unfold globalHighDirectUniformImpl
  exact globalFirstLaneErase_uniformImpl n state

theorem globalFirstLaneErase_directSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    GlobalFirstLaneErases
      ((globalFirstLaneSigningImpl keyView request).run state)
      ((globalHighDirectSigningImpl keyView request).run state) := by
  unfold globalHighDirectSigningImpl
  exact globalFirstLaneErase_signingImpl keyView request state

abbrev GlobalFirstLaneOracleErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) : Prop :=
  ∀ input state, GlobalFirstLaneErases
    (globalFirstLaneOracleExecution keyView edgeHigh input state)
    (globalHighDirectOracleExecution keyView edgeHigh input state)

theorem globalFirstLaneOracleErasure
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    GlobalFirstLaneOracleErasure keyView edgeHigh := by
  intro input state
  cases input with
  | inl n =>
      unfold globalFirstLaneOracleExecution globalHighDirectOracleExecution
      exact globalFirstLaneErase_directUniformImpl n state
  | inr hashInput =>
      unfold globalFirstLaneOracleExecution globalHighDirectOracleExecution
      exact globalFirstLaneErase_attackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
          state

theorem globalFirstLaneVerifierImpl_hash
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : HashInput) :
    globalFirstLaneVerifierImpl keyView edgeHigh (.inr input) =
      globalFirstLaneHashImpl keyView edgeHigh input := by
  unfold globalFirstLaneVerifierImpl globalFirstLaneOracleImpl
    globalFirstLaneOracleExecution
  rfl


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def appendAttackerActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (trace : AttackerActionTrace) : AttackerActionTrace :=
  trace ++ attackerActionFragment input output

noncomputable def cappedBothTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace)) ProbComp) :=
  QueryImpl.extendState
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      appendAttackerActionTrace

theorem cappedBothTracedMappedAdversaryImpl_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState := by
  exact OracleComp.extendState_run_proj_eq
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    appendAttackerActionTrace computation initialState initialTrace

theorem cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedUnloggedMappedAdversaryImpl publicKey secretKey =
      sourceDirectMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput => rfl
  | inr request => rfl

theorem cappedEncodingTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) :
    Prod.map id (fun state => state.1.1) <$>
        (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ (sourceDirectMappedAdversaryImpl publicKey secretKey)
        computation).run initialState.1.1 := by
  calc
    _ = Prod.map id Prod.fst <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1 := by
      rw [← cappedEncodingTracedMappedAdversaryImpl_projection publicKey
        secretKey computation initialState.1 initialState.2]
      simp only [Functor.map_map]
      rfl
    _ = (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1.1 :=
      cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey
        computation initialState.1.1 initialState.1.2
    _ = _ := by
      rw [cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl]

theorem cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedBothTracedMappedAdversaryImpl publicKey secretKey =
      actionTracedStateImpl
        (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        attackerActionFragment := by
  funext input
  unfold cappedBothTracedMappedAdversaryImpl appendAttackerActionTrace
    QueryImpl.extendState actionTracedStateImpl
  rfl

theorem cappedBothTracedMappedAdversaryImpl_query_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  rw [cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, encodingState⟩, hencoding, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [cappedEncodingTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, mem_support_bind_iff] at hencoding
  obtain ⟨⟨cacheOutput, finalState⟩, hbase, hencodingPure⟩ := hencoding
  simp only [support_pure, Set.mem_singleton_iff] at hencodingPure
  have houtput : output = cacheOutput := congrArg Prod.fst hencodingPure
  have hstate : encodingState =
      (finalState,
        encodingActionTraceUpdate secretKey input initialState.1.1 cacheOutput
          finalState initialState.1.2) :=
    congrArg Prod.snd hencodingPure
  subst output
  subst encodingState
  have htraceEq :=
    cappedCacheTracedMappedAdversaryImpl_query_signingTrace_eq
      publicKey secretKey input initialState.1.1 (cacheOutput, finalState) hbase
  have htraceEq' : finalState.2 = signingCacheTraceUpdate input
      initialState.1.1.1 cacheOutput finalState.1 initialState.1.1.2 := by
    simpa using htraceEq
  change finalState.2.toSigningLog =
    (initialState.2 ++ attackerActionFragment input cacheOutput).toSigningLog
  rw [htraceEq', signingCacheTraceUpdate_toSigningLog,
    signingLogUpdate, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment_toSigningLog, hlogs]

theorem cappedBothTracedMappedAdversaryImpl_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : α × (((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.1.1.2.toSigningLog = state.2.toSigningLog)
    (by
      intro input state hstate result hresult
      exact cappedBothTracedMappedAdversaryImpl_query_logs_eq
        publicKey secretKey input state result hstate hresult)
    computation initialState hlogs result hmem

theorem cappedBothTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id (fun state => (state.1.1.1, state.2)) <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialState.1.1, initialTrace) := by
  rw [cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (actionTracedStateImpl
      (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      attackerActionFragment)
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => (state.1.1.1, state.2))
  intro input state
  have hbase := cappedEncodingTracedMappedAdversaryImpl_actionProjection
    publicKey secretKey
      (liftM (OracleSpec.query input) :
        OracleComp (OracleWorld + SigningSpec) _) state.1
  have hbase' :
      Prod.map id (fun state => state.1.1) <$>
          (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
            state.1 =
        (sourceDirectMappedAdversaryImpl publicKey secretKey input).run
          state.1.1.1 := by
    simpa [simulateQ_query] using hbase
  unfold sourceDirectTracedMappedAdversaryImpl
  unfold actionTracedStateImpl
  simp only [StateT.run_mk, map_bind]
  rw [← hbase']
  simp only [bind_map_left, map_pure]
  rfl

abbrev CappedBothTraceExecution :=
  GameOutcome × (((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace) × AttackerActionTrace)

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace)

noncomputable def cappedDetailedGameAfterKeygenWithBothTraces
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp CappedBothTraceExecution := do
  let result ←
    (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((((initialCache, []), []), []))
  let forgery := result.1
  let state := result.2
  let verified ← (simulateQ romImpl
    (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
      forgery.signature)).run state.1.1.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey
    forgery state.1.1.1 verified.2 state.1.2
  pure (⟨publicKey, secretKey, forgery, state.1.1.2.toSigningLog,
      verified.1⟩,
    (((verified.2, state.1.1.2), finalEncodingTrace), state.2))

theorem cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1.signingLog = result.2.2.toSigningLog := by
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedBothTracedMappedAdversaryImpl_logs_eq publicKey secretKey
    (adversary.main publicKey) ((((initialCache, []), []), []))
      (forgery, adversaryState) rfl hadversary

theorem cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1 = actionTraceOutcome publicKey secretKey
      ((result.1.forgery, result.1.verified), result.2.2) := by
  have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    adversary publicKey secretKey initialCache result hresult
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  simp only [actionTraceOutcome]
  have hlogs' : adversaryState.1.1.2.toSigningLog =
      adversaryState.2.toSigningLog := by
    simpa using hlogs
  rw [hlogs']

theorem cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : CappedBothTraceExecution => (result.1, result.2.1)) <$>
        cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
          secretKey initialCache =
      cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
        secretKey initialCache := by
  let finish : Forgery ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) →
      ProbComp CappedEncodingTraceExecution := fun result => do
    let verified ← (simulateQ romImpl
      (Concrete.scheme.verify publicKey result.1.leafIndex result.1.message
        result.1.signature)).run result.2.1.1
    let finalEncodingTrace := appendVerificationEncodingObservation secretKey
      result.1 result.2.1.1 verified.2 result.2.2
    pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog,
      verified.1⟩, ((verified.2, result.2.1.2), finalEncodingTrace))
  have hprojection := cappedBothTracedMappedAdversaryImpl_projection
    publicKey secretKey (adversary.main publicKey) (((initialCache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish) hprojection
  simpa [cappedDetailedGameAfterKeygenWithBothTraces,
    cappedDetailedGameAfterKeygenWithEncodingTrace, finish, map_bind,
    bind_map_left, bind_assoc, Prod.map] using hbound

abbrev CappedBothTraceGameResult :=
  ((PublicKey × SecretKey) × QueryCache HashSpec) ×
    CappedBothTraceExecution

abbrev CappedActionTraceGameResult :=
  ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
    (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)

def cappedBothEncodingProjection
    (result : CappedBothTraceGameResult) : CappedEncodingTraceExecution :=
  (result.2.1, result.2.2.1)

def cappedBothActionProjection
    (result : CappedBothTraceGameResult) : CappedActionTraceGameResult :=
  ((result.1,
    (actionTraceOutcome result.1.1.1 result.1.1.2
      ((result.2.1.forgery, result.2.1.verified), result.2.2.2),
      result.2.2.1.1.1)), result.2.2.2)

noncomputable def cappedDetailedGameWithKeygenCacheAndBothTraces
    (adversary : Adversary) :
    ProbComp CappedBothTraceGameResult := do
  let keyResult ← (simulateQ romImpl Concrete.scheme.keygen).run ∅
  let execution ← cappedDetailedGameAfterKeygenWithBothTraces adversary
    keyResult.1.1 keyResult.1.2 keyResult.2
  pure (keyResult, execution)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2 ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary result.1.1.1
        result.1.1.2 result.1.2) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact hexecution

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2.1 = (cappedBothActionProjection result).1.2.1 := by
  exact cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    adversary result.1.1.1 result.1.1.2 result.1.2 result.2
      (cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
        adversary result hresult)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection
    (adversary : Adversary) :
    (fun result : CappedBothTraceGameResult =>
        (result.2.1, result.2.2.1)) <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
    cappedDetailedGameWithEncodingTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    adversary keyResult.1.1 keyResult.1.2 keyResult.2]
  simp

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq
    (adversary : Adversary) :
    cappedBothEncodingProjection <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary :=
  cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection adversary


theorem simulate_globalFirstLaneEagerTrace_chainProjection
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    (fun result => (result.1, result.2.chainActions)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          computation).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneErase computation)).run := by
  rw [globalFirstLaneErase, ← QueryImpl.simulateQ_compose]
  change Prod.map id FirstLaneOracleSimulation.ActionTrace.chainActions <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run = _
  apply QueryImpl.mapLog_run_simulateQ_of_query
  · rfl
  · exact FirstLaneOracleSimulation.ActionTrace.chainActions_append
  · intro input
    cases input with
    | encodingQuery leafIndex | encodingSignAttempt leafIndex =>
        simp [globalFirstLaneEraseImpl,
          FirstLaneOracleSimulation.eagerTraceImpl,
          FirstLaneOracleSimulation.eagerImpl,
          FirstLaneOracleSimulation.traceFragment,
          FirstLaneOracleSimulation.ActionTrace.chainActions,
          WriterT.run_tell]
        rw [RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
    | uniform n | probe _ _ | reveal _ =>
        simp [globalFirstLaneEraseImpl,
          FirstLaneOracleSimulation.eagerTraceImpl,
          FirstLaneOracleSimulation.eagerImpl,
          FirstLaneOracleSimulation.traceFragment,
          FirstLaneOracleSimulation.ActionTrace.chainActions,
          RevealProbeOracleSimulation.uniformQuery,
          RevealProbeOracleSimulation.probeQuery,
          RevealProbeOracleSimulation.revealQuery,
          RevealProbeOracleSimulation.eagerTraceImpl,
          RevealProbeOracleSimulation.eagerImpl,
          RevealProbeOracleSimulation.traceFragment,
          WriterT.run_tell]

end XmssSecurity.CappedChain
