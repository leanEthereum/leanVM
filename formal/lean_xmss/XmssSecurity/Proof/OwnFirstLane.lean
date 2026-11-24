module

public import XmssSecurity.Proof.CappedExactFirstLaneBound
public import XmssSecurity.Proof.OwnBudget

@[expose] public section

/-!
# The first lane at the adversary's own budget

`CappedExactFirstLaneBound`'s coupling charges only the adversary's direct hash queries
(`directHashActionCost`); its budget there was the whole game's hash calls. Here the budget is the
adversary's own hash queries plus the final verification's (`verifyHashCalls`), so the first lane's
bound counts no call of the signer.
-/

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

/-- One adversary query spends its cost from the own budget. -/
theorem ownBudget_step (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat)
    (h : verifyHashCalls ≤ remaining ∧
      IsQueryBoundP (liftM ((OracleWorld + SigningSpec).query input) >>= next) IsAdvHashAction
        (remaining - verifyHashCalls))
    (answer : (OracleWorld + SigningSpec).Range input) :
    directHashActionCost input ≤ remaining ∧
      (verifyHashCalls ≤ remaining - directHashActionCost input ∧
        IsQueryBoundP (next answer) IsAdvHashAction
          (remaining - directHashActionCost input - verifyHashCalls)) := by
  obtain ⟨hV, hq⟩ := h
  rw [isQueryBoundP_query_bind_iff] at hq
  obtain ⟨hcan, hnext⟩ := hq
  have hn := hnext answer
  rcases input with (n | hashInput) | request
  · simp only [directHashActionCost, IsAdvHashAction, Nat.sub_zero] at hn ⊢
    exact ⟨Nat.zero_le _, hV, by simpa using hn⟩
  · simp only [directHashActionCost, IsAdvHashAction] at hn hcan ⊢
    simp at hn hcan
    refine ⟨by omega, by omega, ?_⟩
    rwa [Nat.sub_right_comm]
  · simp only [directHashActionCost, IsAdvHashAction, Nat.sub_zero] at hn ⊢
    exact ⟨Nat.zero_le _, hV, by simpa using hn⟩

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hown : IsQueryBoundP (adversary.main left.publicKey) IsAdvHashAction
      (countLimit - verifyHashCalls))
    (hV : verifyHashCalls ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2))) := by
  let secretKey :=
    Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let firstLaneInitial : GlobalHighDirectTracedState :=
    GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, firstLaneInitial,
        globalStateOfFirstLane, sourceExactSigningProjection,
        FirstLaneOracleSimulation.ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel
          hleftSupport hrightSupport
    · simp [sourceInitial,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [CappedEncodingMonitor.validObservedSignLeafIndices,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
  let Budget := fun
    (rest : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat) (_state : SourceExactTracedState) =>
      verifyHashCalls ≤ remaining ∧ IsQueryBoundP rest IsAdvHashAction (remaining - verifyHashCalls)
  let leftFinish := fun (forgery : Forgery)
    (initial : SourceExactTracedState) => do
      let verified ← (simulateQ sourceSigningTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
          forgery.signature)).run (sourceExactSigningProjection initial)
      pure ((forgery, verified.1),
        ((verified.2.1,
          appendVerificationEncodingObservation secretKey forgery
            initial.1.1.1 verified.2.1.1 initial.1.2), verified.2.2))
  let rightFinish := fun (forgery : Forgery)
    (initial : GlobalHighDirectTracedState) => do
      let verified ← (simulateQ
        (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
        (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
          forgery.signature)).run initial
      pure ((forgery, verified.1),
        firstLaneAppendVerificationState right.1.1.secretKey forgery initial
          verified.2)
  have hfullBound : Budget (adversary.main left.publicKey) countLimit sourceInitial := ⟨hV, hown⟩
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    leftFinish rightFinish directHashActionCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) Budget
    (by
      intro input next remaining state result hrest _hresult
      exact ownBudget_step input next remaining hrest result.1)
    (by
      intro spent input state firstState history hstates hprefix hacct
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by
          rw [hgood.2.2.2, hacct]⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro forgery spent remaining state firstState history hremaining
        hstates hcount hacct htotal
      have hverifyBound :
          HashQueryBound (Concrete.scheme.verify left.publicKey forgery.leafIndex forgery.message
            forgery.signature) state.1.1.1 remaining :=
        (verify_hashQueryBound _ _ _ _ _).mono hremaining.1
      have hverifier :=
        relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
          spent remaining left right hrel hleftSupport hrightSupport
            (Concrete.scheme.verify left.publicKey forgery.leafIndex
              forgery.message forgery.signature) state hverifyBound firstState
                history hstates hcount htotal hlimits
      let sourceFinish := fun verified : Bool × SourceExactTracedState =>
        ((forgery, verified.1),
          sourceAppendVerificationState secretKey forgery state verified.2)
      let firstFinish := fun verified :
          ((Bool × GlobalHighDirectTracedState) ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (((forgery, verified.1.1),
          firstLaneAppendVerificationState right.1.1.secretKey forgery
            firstState verified.1.2), verified.2)
      have hlifted : RelTriple
          (sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey forgery.leafIndex
                forgery.message forgery.signature)).run state)
          (firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.leafIndex
                  forgery.message forgery.signature)).run firstState)).run)
          (fun leftResult firstResult =>
            (leftResult.1 = firstResult.1.1 ∧
              SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
                firstResult.1.2 (history ++ firstResult.2) ∧
              FirstLaneOracleSimulation.hazardCount
                (history ++ firstResult.2) ≤ countLimit) ∨
            FirstLaneOracleSimulation.CombinedHit right.1.2
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (history ++ firstResult.2))) := by
        apply relTriple_map
        apply relTriple_post_mono (relTriple_with_support hverifier)
        intro leftVerified firstVerified hvertified
        obtain ⟨hverifiedRelation, hleftVerifiedSupport,
          hfirstVerifiedSupport⟩ := hvertified
        rcases hverifiedRelation with hgood | hhit
        · exact Or.inl ⟨congrArg (Prod.mk forgery) hgood.1,
            SourceFirstLaneExactGoodStateRelation.appendVerification left right
              hrel hleftSupport hrightSupport forgery state leftVerified.2
                firstState firstVerified.1.2 history
                  (history ++ firstVerified.2) hstates hgood.2.1 (by
                    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
                    have hpublicKey : left.publicKey =
                        right.1.1.publicKey := hrel.1.toStable.1.2.1
                    rw [hpublicKey] at hfirstVerifiedSupport
                    have hlocal :=
                      globalFirstLaneExactTracedVerifier_append_trace_sublist
                        right.1.2 right.1.1 right.2 forgery firstState
                          leftVerified.2.1.2
                          (by
                            have hkeyResult :=
                              trajectoryProgrammedGlobalChainKeygen_support_keyResult
                                right.1.1 hrightSupport
                            exact keygen_parameter_eq right.1.1.keyResult
                              hkeyResult)
                          firstVerified hfirstVerifiedSupport
                    have hleftEncoding : leftVerified.2.1.2 = state.1.2 := by
                      rw [sourceExactTracedVerifierImpl_run_eq, support_map]
                        at hleftVerifiedSupport
                      obtain ⟨baseResult, _hbase, heq⟩ := hleftVerifiedSupport
                      subst leftVerified
                      rfl
                    have hencodingInitial := hstates.2.1
                    have hencodingFinal : List.Sublist leftVerified.2.1.2
                        history.encodingActions := by
                      rw [hleftEncoding]
                      exact hencodingInitial
                    exact hlocal.trans
                      (hencodingFinal.append (List.Sublist.refl _))),
            hgood.2.2⟩
        · exact Or.inr hhit
      have hsource : leftFinish forgery state = sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey forgery.leafIndex
              forgery.message forgery.signature)).run state := by
        unfold leftFinish
        rw [sourceExactTracedVerifierImpl_run_eq]
        simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
      have hright :
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (rightFinish forgery firstState)).run =
          firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.leafIndex
                  forgery.message forgery.signature)).run firstState)).run := by
        unfold rightFinish
        rw [simulateQ_bind, WriterT.run_bind']
        simp [firstFinish, firstLaneAppendVerificationState]
      rw [hsource, hright]
      exact hlifted)
    0 countLimit (adversary.main left.publicKey) sourceInitial
      firstLaneInitial hfullBound [] hinitial
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl) (by omega)
        hlimits
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  exact hcoupling

theorem relTriple_sourceGlobalExact_firstLane_program_boundedHit
    (q hitLimit : Nat) (adversary : Adversary) (hown : OwnHashBound adversary q)
    (hlimits : q + verifyHashCalls ≤ hitLimit) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (SourceFirstLaneExactBoundedProgramRelation (q + verifyHashCalls) hitLimit) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit
      (q + verifyHashCalls) hitLimit adversary left right hrel
        hleftSupport hrightViewSupport (by simpa using hown left.publicKey)
        (Nat.le_add_left _ _) hlimits)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution⟩

/-- **The first lane at the adversary's own budget**: its own hash calls, the final
verification's and the forgery's probes. -/
theorem exactFirstLane_probability_le (q : Nat) (adversary : Adversary)
    (hown : OwnHashBound adversary q) :
    Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs x] ≤
      ((q + verifyHashCalls + forgeryProbeCount : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  let fuel := q + verifyHashCalls + forgeryProbeCount
  calc
    _ ≤ Pr{let x ← globalFirstLaneExactCoupledProgram adversary}[(GlobalFirstLaneExactCoupledEnforcedHit fuel) x] := by
      apply prEvent_le_of_relTriple
        (relTriple_with_support
          (relTriple_sourceGlobalExact_firstLane_program_boundedHit
            q fuel adversary hown (by simp [fuel])))
      intro left right hrelation hevent
      exact sourceWinningExactFirstLane_implies_coupled_enforcedHit
        (q + verifyHashCalls) fuel adversary left right
          hrelation.2.1 hrelation.2.2 hrelation.1 (by simp [fuel]) hevent
    _ = Pr{let x ← globalFirstLaneExactPublicEagerExperiment adversary}[(GlobalFirstLaneExactPublicEnforcedHit fuel) x] :=
      coupled_enforcedHit_probability_eq_public_eager fuel adversary
    _ ≤ _ := public_eager_enforcedHit_probability_le fuel adversary

end XmssSecurity.CappedChain
