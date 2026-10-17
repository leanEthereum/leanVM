import XmssSecurity.Proof.CappedEncodingGameTrace
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000

def ValidFreshSigningCollisionsRepresented
    (secretKey : SecretKey) (signingTrace : SigningCacheTrace)
    (actions : EncodingActionTrace) : Prop :=
  signingTrace.leafIndices.Nodup →
    ∀ entry ∈ signingTrace, entry.FreshSigningEncodingCollision secretKey →
      ∃ signedOutput oldOutput before middle after,
        TargetSum.ValidDigest (truncateHash signedOutput) ∧
        TargetSum.ValidDigest (truncateHash oldOutput) ∧
        truncateHash signedOutput = truncateHash oldOutput ∧
        actions = before ++ [.query entry.request.leafIndex oldOutput] ++ middle ++
          [.sign entry.request.leafIndex signedOutput] ++ after

theorem ValidFreshSigningCollisionsRepresented.append_actions
    {secretKey : SecretKey} {signingTrace : SigningCacheTrace}
    {actions : EncodingActionTrace}
    (hrepresented : ValidFreshSigningCollisionsRepresented secretKey signingTrace actions)
    (suffix : EncodingActionTrace) :
    ValidFreshSigningCollisionsRepresented secretKey signingTrace
      (actions ++ suffix) := by
  intro hnodup entry hentry hcollision
  obtain ⟨signedOutput, oldOutput, before, middle, after, hsignedValid,
    holdValid, hdigest, hactions⟩ :=
    hrepresented hnodup entry hentry hcollision
  refine ⟨signedOutput, oldOutput, before, middle, after ++ suffix,
    hsignedValid, holdValid, hdigest, ?_⟩
  rw [hactions]
  simp [List.append_assoc]

theorem cappedCacheTracedMappedAdversaryImpl_query_signingTrace_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    result.2.2 = signingCacheTraceUpdate input initialState.1 result.1
      result.2.1 initialState.2 := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, _hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rfl

theorem cappedCacheTracedMappedAdversaryImpl_query_base_support
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : QueryCache HashSpec × SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    (result.1, result.2.1) ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run initialState.1) := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact hbase

theorem cappedEncodingTracedMappedAdversaryImpl_query_support_info
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    ∃ output finalState suffix,
      result = (output, (finalState,
        encodingActionTraceUpdate secretKey input initialState.1 output
          finalState initialState.2)) ∧
      (output, finalState.1) ∈ support
        ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run
          initialState.1.1) ∧
      finalState.2 = signingCacheTraceUpdate input initialState.1.1 output
        finalState.1 initialState.1.2 ∧
      initialState.1.1 ≤ finalState.1 ∧
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
        initialState.2 = initialState.2 ++ suffix := by
  rw [cappedEncodingTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalState⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hbaseSupport := cappedCacheTracedMappedAdversaryImpl_query_base_support
    publicKey secretKey input initialState.1 (output, finalState) hbase
  have htraceEq := cappedCacheTracedMappedAdversaryImpl_query_signingTrace_eq
    publicKey secretKey input initialState.1 (output, finalState) hbase
  obtain ⟨suffix, hsuffix⟩ : ∃ suffix : EncodingActionTrace,
      encodingActionTraceUpdate secretKey input initialState.1 output finalState
          initialState.2 = initialState.2 ++ suffix := by
    rcases encodingActionTraceUpdate_eq_or_append secretKey input initialState.1
      output finalState initialState.2 with hsame | ⟨observation, happend⟩
    · exact ⟨[], by simpa using hsame⟩
    · exact ⟨[observation], happend⟩
  exact ⟨output, finalState, suffix, rfl, hbaseSupport, htraceEq,
    cappedUnloggedMappedAdversaryImpl_cache_le publicKey secretKey input
      initialState.1.1 (output, finalState.1) hbaseSupport,
    hsuffix⟩

theorem cappedUnloggedMappedAdversaryImpl_directHash_fresh_cache_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (queriedInput targetInput : HashInput)
    (initialCache finalCache : QueryCache HashSpec)
    (output targetOutput : HashOutput)
    (hmem : (output, finalCache) ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr queriedInput))).run initialCache))
    (hfresh : initialCache targetInput = none)
    (hfinal : finalCache targetInput = some targetOutput) :
    queriedInput = targetInput ∧ output = targetOutput := by
  change (output, finalCache) ∈ support
    ((randomOracle (spec := HashSpec) queriedInput).run initialCache) at hmem
  cases hqueried : initialCache queriedInput with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hmem
      obtain ⟨sampled, _hsampled, heq⟩ := hmem
      cases heq
      by_cases hinput : queriedInput = targetInput
      · subst targetInput
        have hself := QueryCache.cacheQuery_self initialCache queriedInput output
        rw [hfinal] at hself
        exact ⟨rfl, Option.some.inj hself.symm⟩
      · have hnone : (initialCache.cacheQuery queriedInput output) targetInput = none := by
          rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hinput)]
          exact hfresh
        rw [hfinal] at hnone
        contradiction
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      rw [hfresh] at hfinal
      contradiction

theorem cappedUnloggedMappedAdversaryImpl_uniform_cache_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (uniformInput : unifSpec.Domain)
    (initialCache : QueryCache HashSpec)
    (result : unifSpec.Range uniformInput × QueryCache HashSpec)
    (hmem : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inl uniformInput))).run initialCache)) :
    result.2 = initialCache := by
  have hrun :
      (unifFwdImpl HashSpec uniformInput).run initialCache =
        (fun sample => (sample, initialCache)) <$>
          (liftM (unifSpec.query uniformInput) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
  change result ∈ support ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem cappedEncodingTracedMappedAdversaryImpl_query_signLeafIndices_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsublist : List.Sublist
      (EncodingMonitor.observedSignLeafIndices initialState.2) initialState.1.2.leafIndices)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    List.Sublist (EncodingMonitor.observedSignLeafIndices result.2.2)
      result.2.1.2.leafIndices := by
  obtain ⟨output, finalState, _suffix, hresult, _hbase, htraceEq,
    _hcacheLe, _hsuffix⟩ :=
    cappedEncodingTracedMappedAdversaryImpl_query_support_info publicKey
      secretKey input initialState result hmem
  subst result
  exact encodingActionTraceUpdate_signLeafIndices_sublist secretKey input initialState.1
    output finalState initialState.2 htraceEq hsublist

theorem cappedEncodingTracedMappedAdversaryImpl_query_freshSigningActionsRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 := by
  obtain ⟨output, finalState, suffix, hresult, hbaseSupport, htraceEq,
    _hcacheLe, hsuffix⟩ :=
    cappedEncodingTracedMappedAdversaryImpl_query_support_info publicKey
      secretKey input initialState result hmem
  subst result
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq, hsuffix]
      exact hrepresented.append_actions suffix
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro entry hentry signature hsignature hfresh
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · rw [hsuffix]
        exact hrepresented.append_actions suffix entry hentry signature hsignature hfresh
      · simp only [List.mem_singleton] at hentry
        subst entry
        cases output with
        | none => simp at hsignature
        | some returnedSignature =>
            simp only [Option.some.injEq] at hsignature
            subst returnedSignature
            change initialState.1.1
              (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex
                (request.message, signature.randomness)) = none at hfresh
            have hsignSupport : (some signature, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run
                    initialState.1.1) := by
              change (some signature, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run
                    initialState.1.1) at hbaseSupport
              exact hbaseSupport
            obtain ⟨hashOutput, houtput⟩ :=
              Concrete.precomputedCappedSign_success_encodingInput_cached secretKey
                request initialState.1.1 finalState.1 signature hsignSupport
            refine ⟨hashOutput, initialState.2, [], houtput, ?_⟩
            simp [encodingActionTraceUpdate, encodingObservation?, hfresh, houtput]

theorem cappedEncodingTracedMappedAdversaryImpl_query_unsignedEncodingEntriesRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hrepresented : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      result.2.1.1 result.2.1.2 result.2.2 := by
  obtain ⟨output, finalState, suffix, hresult, hbaseSupport, htraceEq,
    hcacheLe, hsuffix⟩ :=
    cappedEncodingTracedMappedAdversaryImpl_query_support_info publicKey
      secretKey input initialState result hmem
  subst result
  change UnsignedEncodingEntriesRepresented secretKey.parameter baseCache finalState.1
    finalState.2
      (encodingActionTraceUpdate secretKey input initialState.1 output finalState
        initialState.2)
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      cases worldInput with
      | inl uniformInput =>
          have hcacheEq := cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey
            secretKey uniformInput initialState.1.1 (output, finalState.1) hbaseSupport
          change finalState.1 = initialState.1.1 at hcacheEq
          rw [htraceEq, hcacheEq]
          simpa [encodingActionTraceUpdate, encodingObservation?] using hrepresented
      | inr queriedInput =>
          rw [htraceEq]
          intro leafIndex hunsigned targetInput targetOutput hencoding hbaseFresh hfinal
          cases hinitial : initialState.1.1 targetInput with
          | some oldOutput =>
              have hfinalOld := hcacheLe hinitial
              have houtputEq : oldOutput = targetOutput := by
                rw [hfinal] at hfinalOld
                exact Option.some.inj hfinalOld.symm
              subst oldOutput
              obtain ⟨before, after, hactions⟩ := hrepresented leafIndex hunsigned
                targetInput targetOutput hencoding hbaseFresh hinitial
              refine ⟨before, after ++ suffix, ?_⟩
              rw [hsuffix, hactions]
              simp [List.append_assoc]
          | none =>
              obtain ⟨hinput, houtput⟩ :=
                cappedUnloggedMappedAdversaryImpl_directHash_fresh_cache_eq publicKey
                  secretKey queriedInput targetInput initialState.1.1 finalState.1
                  output targetOutput hbaseSupport hinitial hfinal
              subst queriedInput
              subst output
              refine ⟨initialState.2, [], ?_⟩
              simp [encodingActionTraceUpdate, encodingObservation?, hinitial,
                hencoding]
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro leafIndex hunsigned targetInput targetOutput hencoding hbaseFresh hfinal
      have hunsignedInitial : leafIndex ∉ initialState.1.2.leafIndices := by
        intro hmem
        exact hunsigned (by simp [hmem])
      have hotherLeafIndex : request.leafIndex ≠ leafIndex := by
        intro heq
        subst leafIndex
        exact hunsigned (by simp [SigningCacheTrace.leafIndices])
      cases hinitial : initialState.1.1 targetInput with
      | some oldOutput =>
          have hfinalOld := hcacheLe hinitial
          have houtputEq : oldOutput = targetOutput := by
            rw [hfinal] at hfinalOld
            exact Option.some.inj hfinalOld.symm
          subst oldOutput
          obtain ⟨before, after, hactions⟩ := hrepresented leafIndex hunsignedInitial
            targetInput targetOutput hencoding hbaseFresh hinitial
          refine ⟨before, after ++ suffix, ?_⟩
          rw [hsuffix, hactions]
          simp [List.append_assoc]
      | none =>
          have hsignSupport : (output, finalState.1) ∈ support
              ((simulateQ romImpl
                (Concrete.precomputedCappedSign secretKey request.leafIndex
                  request.message)).run
                  initialState.1.1) := by
            change (output, finalState.1) ∈ support
              ((simulateQ romImpl
                (Concrete.precomputedCappedSign secretKey request.leafIndex
                  request.message)).run
                  initialState.1.1) at hbaseSupport
            exact hbaseSupport
          obtain ⟨targetPair, htargetPair⟩ :=
            exists_encodingInput_of_encodingInputLeafIndex?_eq_some secretKey.parameter
              targetInput leafIndex hencoding
          have hnone :=
            Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
              secretKey request.leafIndex leafIndex request.message targetPair initialState.1.1
              finalState.1 output hsignSupport hotherLeafIndex
            (by rw [htargetPair]; exact hinitial)
          rw [htargetPair, hfinal] at hnone
          cases hnone

theorem cappedEncodingTracedMappedAdversaryImpl_query_validFreshSigningCollisionsRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (hbaseEncodingFree : ∀ leafIndex input,
      baseCache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex input) = none)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hunsigned : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hrepresented : ValidFreshSigningCollisionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    ValidFreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  obtain ⟨output, finalState, suffix, hresult, hbaseSupport, htraceEq,
    _hcacheLe, hsuffix⟩ :=
    cappedEncodingTracedMappedAdversaryImpl_query_support_info publicKey
      secretKey input initialState result hmem
  subst result
  change ValidFreshSigningCollisionsRepresented secretKey finalState.2
    (encodingActionTraceUpdate secretKey input initialState.1 output finalState
      initialState.2)
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq, hsuffix]
      exact hrepresented.append_actions suffix
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro hnodup entry hentry hcollision
      have hnodupInitial : initialState.1.2.leafIndices.Nodup := by
        exact (List.nodup_append.mp (by simpa using hnodup)).1
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · rw [hsuffix]
        exact hrepresented.append_actions suffix hnodupInitial entry hentry hcollision
      · simp only [List.mem_singleton] at hentry
        subst entry
        obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
          hfresh, hsigned, hold, _hne, hdigest⟩ := hcollision
        change initialState.1.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex
            (request.message, signature.randomness)) = none at hfresh
        change finalState.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex
            (request.message, signature.randomness)) = some signedOutput at hsigned
        change initialState.1.1
          (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex oldInput) =
            some oldOutput at hold
        cases output with
        | none => simp at hsignature
        | some returnedSignature =>
            simp only [Option.some.injEq] at hsignature
            subst returnedSignature
            have hsignSupport : (some signature, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run initialState.1.1) := by
              change (some signature, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run initialState.1.1) at hbaseSupport
              exact hbaseSupport
            obtain ⟨encoding, hdecode⟩ :=
              Concrete.precomputedCappedSign_success_decode secretKey request
                initialState.1.1 finalState.1 signature hsignSupport
            have hsignedValid : TargetSum.ValidDigest (truncateHash signedOutput) := by
              refine ⟨encoding, ?_⟩
              simpa [Concrete.CacheView.encodingHash,
                Concrete.CacheView.digestAt_eq_of_cache_eq_some hsigned] using hdecode
            have holdValid : TargetSum.ValidDigest (truncateHash oldOutput) := by
              rw [← hdigest]
              exact hsignedValid
            have hrequestFresh : request.leafIndex ∉ initialState.1.2.leafIndices := by
              intro hmem
              have hcross := (List.nodup_append.mp (by simpa using hnodup)).2.2
              exact hcross request.leafIndex hmem request.leafIndex
                (by simp [SigningCacheTrace.leafIndices]) rfl
            obtain ⟨before, middle, hqueryActions⟩ := hunsigned request.leafIndex
              hrequestFresh
              (Concrete.CacheView.encodingInput secretKey.parameter request.leafIndex oldInput)
              oldOutput (by simp) (hbaseEncodingFree request.leafIndex oldInput) hold
            refine ⟨signedOutput, oldOutput, before, middle, [], hsignedValid,
              holdValid, hdigest, ?_⟩
            rw [show encodingActionTraceUpdate secretKey (.inr request) initialState.1
                (some signature) finalState initialState.2 =
                initialState.2 ++ [.sign request.leafIndex signedOutput] by
              simp [encodingActionTraceUpdate, encodingObservation?, hfresh, hsigned]]
            rw [hqueryActions]
            simp [List.append_assoc]


theorem cappedEncodingTracedMappedAdversaryImpl_query_postSigningQueriesRepresented
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsignActions : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hrepresented : PostSigningQueriesRepresented secretKey initialState.1.2
      initialState.1.1 initialState.2)
    (hmem : result ∈ support
      ((cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run initialState)) :
    PostSigningQueriesRepresented secretKey result.2.1.2 result.2.1.1
      result.2.2 := by
  obtain ⟨output, finalState, suffix, hresult, hbaseSupport, htraceEq,
    hcacheLe, hsuffix⟩ :=
    cappedEncodingTracedMappedAdversaryImpl_query_support_info publicKey
      secretKey input initialState result hmem
  subst result
  change PostSigningQueriesRepresented secretKey finalState.2 finalState.1
    (encodingActionTraceUpdate secretKey input initialState.1 output finalState
      initialState.2)
  cases input with
  | inl worldInput =>
      rw [signingCacheTraceUpdate] at htraceEq
      cases worldInput with
      | inl uniformInput =>
          have hcacheEq := cappedUnloggedMappedAdversaryImpl_uniform_cache_eq publicKey
            secretKey uniformInput initialState.1.1 (output, finalState.1) hbaseSupport
          change finalState.1 = initialState.1.1 at hcacheEq
          rw [htraceEq, hcacheEq]
          simpa [encodingActionTraceUpdate, encodingObservation?] using hrepresented
      | inr queriedInput =>
          rw [htraceEq]
          intro hnodup entry hentry signature signedOutput targetInput targetOutput
            hsignature hfresh hsigned hencoding hentryFresh hfinal
          cases hinitial : initialState.1.1 targetInput with
          | some oldOutput =>
              have hfinalOld := hcacheLe hinitial
              have houtputEq : oldOutput = targetOutput := by
                rw [hfinal] at hfinalOld
                exact Option.some.inj hfinalOld.symm
              subst oldOutput
              obtain ⟨before, middle, after, hactions⟩ := hrepresented hnodup entry
                hentry signature signedOutput targetInput targetOutput hsignature hfresh
                hsigned hencoding hentryFresh hinitial
              refine ⟨before, middle, after ++ suffix, ?_⟩
              rw [hsuffix, hactions]
              simp [List.append_assoc]
          | none =>
              obtain ⟨hinput, houtput⟩ :=
                cappedUnloggedMappedAdversaryImpl_directHash_fresh_cache_eq publicKey
                  secretKey queriedInput targetInput initialState.1.1 finalState.1
                  output targetOutput hbaseSupport hinitial hfinal
              subst queriedInput
              subst output
              obtain ⟨actionSignedOutput, before, middle, hcached, hsignActionsEq⟩ :=
                hsignActions entry hentry signature hsignature hfresh
              have hsignedOutputEq : actionSignedOutput = signedOutput := by
                rw [hsigned] at hcached
                exact Option.some.inj hcached.symm
              subst actionSignedOutput
              refine ⟨before, middle, [], ?_⟩
              rw [show encodingActionTraceUpdate secretKey (.inl (.inr targetInput))
                  initialState.1 targetOutput finalState initialState.2 =
                  initialState.2 ++ [.query entry.request.leafIndex targetOutput] by
                simp [encodingActionTraceUpdate, encodingObservation?, hinitial,
                  hencoding]]
              rw [hsignActionsEq]
              simp [List.append_assoc]
  | inr request =>
      rw [signingCacheTraceUpdate] at htraceEq
      rw [htraceEq]
      intro hnodup entry hentry signature signedOutput targetInput targetOutput
        hsignature hfresh hsigned hencoding hentryFresh hfinal
      have hnodupInitial : initialState.1.2.leafIndices.Nodup :=
        (List.nodup_append.mp (by simpa using hnodup)).1
      rw [List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · have hotherLeafIndex : request.leafIndex ≠ entry.request.leafIndex := by
          intro heq
          have hcross := (List.nodup_append.mp (by simpa using hnodup)).2.2
          exact hcross entry.request.leafIndex
            (by exact List.mem_map.mpr ⟨entry, hentry, rfl⟩) request.leafIndex
            (by simp [SigningCacheTrace.leafIndices]) heq.symm
        cases hinitial : initialState.1.1 targetInput with
        | some oldOutput =>
            have hfinalOld := hcacheLe hinitial
            have houtputEq : oldOutput = targetOutput := by
              rw [hfinal] at hfinalOld
              exact Option.some.inj hfinalOld.symm
            subst oldOutput
            obtain ⟨before, middle, after, hactions⟩ := hrepresented hnodupInitial
              entry hentry signature signedOutput targetInput targetOutput hsignature
              hfresh hsigned hencoding hentryFresh hinitial
            refine ⟨before, middle, after ++ suffix, ?_⟩
            rw [hsuffix, hactions]
            simp [List.append_assoc]
        | none =>
            have hsignSupport : (output, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run
                    initialState.1.1) := by
              change (output, finalState.1) ∈ support
                ((simulateQ romImpl
                  (Concrete.precomputedCappedSign secretKey request.leafIndex
                    request.message)).run
                    initialState.1.1) at hbaseSupport
              exact hbaseSupport
            obtain ⟨targetPair, htargetPair⟩ :=
              exists_encodingInput_of_encodingInputLeafIndex?_eq_some secretKey.parameter
                targetInput entry.request.leafIndex hencoding
            have hnone :=
              Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
                secretKey request.leafIndex entry.request.leafIndex request.message targetPair
                initialState.1.1 finalState.1 output hsignSupport hotherLeafIndex
              (by rw [htargetPair]; exact hinitial)
            rw [htargetPair, hfinal] at hnone
            cases hnone
      · simp only [List.mem_singleton] at hentry
        subst entry
        change finalState.1 targetInput = none at hentryFresh
        rw [hfinal] at hentryFresh
        cases hentryFresh

theorem cappedEncodingTracedMappedAdversaryImpl_signLeafIndices_sublist
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsublist : List.Sublist
      (EncodingMonitor.observedSignLeafIndices initialState.2) initialState.1.2.leafIndices)
    (hmem : result ∈ support
      ((simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    List.Sublist (EncodingMonitor.observedSignLeafIndices result.2.2)
      result.2.1.2.leafIndices := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => List.Sublist (EncodingMonitor.observedSignLeafIndices state.2)
      state.1.2.leafIndices)
    (by
      intro input state hstate queryResult hquery
      exact cappedEncodingTracedMappedAdversaryImpl_query_signLeafIndices_sublist
        publicKey secretKey input state queryResult hstate hquery)
    computation initialState hsublist result hmem

theorem cappedEncodingTracedMappedAdversaryImpl_validEncodingCollisionInvariants
    (publicKey : PublicKey) (secretKey : SecretKey)
    (baseCache : QueryCache HashSpec)
    (hbaseEncodingFree : ∀ leafIndex input,
      baseCache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex input) = none)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hunsigned : UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
      initialState.1.1 initialState.1.2 initialState.2)
    (hcollisions : ValidFreshSigningCollisionsRepresented secretKey initialState.1.2
      initialState.2)
    (hmem : result ∈ support
      ((simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    UnsignedEncodingEntriesRepresented secretKey.parameter baseCache result.2.1.1
        result.2.1.2 result.2.2 ∧
      ValidFreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    (fun state =>
      UnsignedEncodingEntriesRepresented secretKey.parameter baseCache
          state.1.1 state.1.2 state.2 ∧
        ValidFreshSigningCollisionsRepresented secretKey state.1.2 state.2)
    (by
      intro input state hstate queryResult hquery
      constructor
      · exact
          cappedEncodingTracedMappedAdversaryImpl_query_unsignedEncodingEntriesRepresented
            publicKey secretKey baseCache input state queryResult hstate.1 hquery
      · exact
          cappedEncodingTracedMappedAdversaryImpl_query_validFreshSigningCollisionsRepresented
            publicKey secretKey baseCache hbaseEncodingFree input state queryResult
            hstate.1 hstate.2 hquery)
    computation initialState ⟨hunsigned, hcollisions⟩ result hmem


theorem cappedEncodingTracedMappedAdversaryImpl_postSigningInvariants
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
    (result : α ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hsignActions : FreshSigningActionsRepresented secretKey initialState.1.2
      initialState.2)
    (hpostSigning : PostSigningQueriesRepresented secretKey initialState.1.2
      initialState.1.1 initialState.2)
    (hmem : result ∈ support
      ((simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    FreshSigningActionsRepresented secretKey result.2.1.2 result.2.2 ∧
      PostSigningQueriesRepresented secretKey result.2.1.2 result.2.1.1
        result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    (fun state =>
      FreshSigningActionsRepresented secretKey state.1.2 state.2 ∧
        PostSigningQueriesRepresented secretKey state.1.2 state.1.1 state.2)
    (by
      intro input state hstate queryResult hquery
      constructor
      · exact cappedEncodingTracedMappedAdversaryImpl_query_freshSigningActionsRepresented
          publicKey secretKey input state queryResult hstate.1 hquery
      · exact cappedEncodingTracedMappedAdversaryImpl_query_postSigningQueriesRepresented
          publicKey secretKey input state queryResult hstate.1 hstate.2 hquery)
    computation initialState ⟨hsignActions, hpostSigning⟩ result hmem


theorem cappedDetailedGameAfterKeygenWithEncodingTrace_signLeafIndices_sublist
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache)) :
    List.Sublist (EncodingMonitor.observedSignLeafIndices result.2.2)
      result.2.1.2.leafIndices := by
  unfold cappedDetailedGameAfterKeygenWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hsublist := cappedEncodingTracedMappedAdversaryImpl_signLeafIndices_sublist
    publicKey secretKey (adversary.main publicKey) ((initialCache, []), [])
    (forgery, (adversaryState, encodingTrace))
    (List.Sublist.refl []) hadversary
  change List.Sublist (EncodingMonitor.observedSignLeafIndices
    (appendVerificationEncodingObservation secretKey forgery adversaryState.1
      finalCache encodingTrace)) adversaryState.2.leafIndices
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
    (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, EncodingMonitor.observedSignLeafIndices] using hsublist
    | some output =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput, EncodingMonitor.observedSignLeafIndices] using hsublist
  · simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
      EncodingMonitor.observedSignLeafIndices] using hsublist

theorem cappedDetailedGameAfterKeygenWithEncodingTrace_validFreshSigningCollisionsRepresented
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (hinitialEncodingFree : ∀ leafIndex input,
      initialCache
        (Concrete.CacheView.encodingInput secretKey.parameter leafIndex input) = none)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support
      (cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache)) :
    ValidFreshSigningCollisionsRepresented secretKey result.2.1.2 result.2.2 := by
  unfold cappedDetailedGameAfterKeygenWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hinvariants := cappedEncodingTracedMappedAdversaryImpl_validEncodingCollisionInvariants
    publicKey secretKey initialCache hinitialEncodingFree (adversary.main publicKey)
    ((initialCache, []), []) (forgery, (adversaryState, encodingTrace))
    (UnsignedEncodingEntriesRepresented.refl secretKey.parameter initialCache)
    (by simp [ValidFreshSigningCollisionsRepresented, SigningCacheTrace.leafIndices]) hadversary
  have hrepresented := hinvariants.2
  change ValidFreshSigningCollisionsRepresented secretKey adversaryState.2
    (appendVerificationEncodingObservation secretKey forgery adversaryState.1
      finalCache encodingTrace)
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
    (forgery.message, forgery.signature.randomness)
  by_cases hfresh : adversaryState.1 forgedInput = none
  · cases houtput : finalCache forgedInput with
    | none =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh,
          houtput] using hrepresented
    | some output =>
        simpa [appendVerificationEncodingObservation, forgedInput, hfresh, houtput]
          using hrepresented.append_actions
            [EncodingMonitor.ObservedAction.query forgery.leafIndex output]
  · simpa [appendVerificationEncodingObservation, forgedInput, hfresh] using hrepresented


theorem cappedDetailedGameWithEncodingTrace_signLeafIndices_sublist
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary)) :
    List.Sublist (EncodingMonitor.observedSignLeafIndices result.2.2)
      result.2.1.2.leafIndices := by
  unfold cappedDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  exact cappedDetailedGameAfterKeygenWithEncodingTrace_signLeafIndices_sublist adversary
    publicKey secretKey keyCache result hrest

theorem cappedDetailedGameWithEncodingTrace_validFreshSigningCollisionsRepresented
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary)) :
    ValidFreshSigningCollisionsRepresented result.1.secretKey result.2.1.2 result.2.2 := by
  unfold cappedDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨keyResult, hkeygen, hrest⟩ := hmem
  obtain ⟨⟨publicKey, secretKey⟩, keyCache⟩ := keyResult
  have hkeygen' : ((publicKey, secretKey), keyCache) ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hencodingFree : ∀ leafIndex input,
      keyCache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex input) = none :=
    fun leafIndex input => Concrete.precomputedKeygen_cache_none_encodingInput
      ((publicKey, secretKey), keyCache) hkeygen' leafIndex input
  have hrepresented :=
    cappedDetailedGameAfterKeygenWithEncodingTrace_validFreshSigningCollisionsRepresented
      adversary publicKey secretKey keyCache hencodingFree result hrest
  have hprojection : (result.1, result.2.1) ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey keyCache) := by
    rw [← cappedDetailedGameAfterKeygenWithEncodingTrace_projection, support_map]
    exact ⟨result, hrest, rfl⟩
  have hsecretKey :=
    (cappedDetailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey secretKey
      keyCache (result.1, result.2.1) hprojection).1
  rw [hsecretKey]
  exact hrepresented


theorem cappedDetailedGameWithEncodingTrace_signingLeafIndices_nodup_of_winning
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding) :
    result.2.1.2.leafIndices.Nodup := by
  have hprojected : (result.1, result.2.1) ∈
      support (cappedDetailedGameWithSigningTrace adversary) := by
    rw [← cappedDetailedGameWithEncodingTrace_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  have hlog := (cappedDetailedGameWithSigningTrace_invariants adversary
    (result.1, result.2.1) hprojected).1
  have htraceNodup : result.2.1.2.leafIndices.Nodup := by
    have hvalid := hevent.signingTranscript_valid
    rw [← hlog] at hvalid
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.leafIndices, SigningCacheTrace.toSigningLog,
      List.map_map, Function.comp_def] using hvalid
  exact htraceNodup

theorem cappedDetailedGameWithEncodingTrace_signLeafIndices_nodup_of_winning
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding) :
    (EncodingMonitor.observedSignLeafIndices result.2.2).Nodup := by
  have htraceNodup :=
    cappedDetailedGameWithEncodingTrace_signingLeafIndices_nodup_of_winning adversary result
      hmem hevent
  exact htraceNodup.sublist
    (cappedDetailedGameWithEncodingTrace_signLeafIndices_sublist adversary result hmem)

theorem cappedDetailedGameWithEncodingTrace_validSignLeafIndices_nodup_of_winning
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding) :
    (CappedEncodingMonitor.validObservedSignLeafIndices result.2.2).Nodup := by
  have hraw := cappedDetailedGameWithEncodingTrace_signLeafIndices_nodup_of_winning
    adversary result hmem hevent
  exact hraw.sublist (EncodingMonitor.observedSignLeafIndices_sublist
    (CappedEncodingMonitor.validActions_sublist result.2.2))

theorem CappedEncodingMonitor.runObserved_empty_eq_true_of_query_before_sign_of_valid
    (leafIndex : LeafIndex) (oldOutput signedOutput : HashOutput)
    (before middle after : EncodingActionTrace)
    (holdValid : TargetSum.ValidDigest (truncateHash oldOutput))
    (hsignedValid : TargetSum.ValidDigest (truncateHash signedOutput))
    (hdigest : truncateHash oldOutput = truncateHash signedOutput)
    (hnodup : (CappedEncodingMonitor.validObservedSignLeafIndices
      (before ++ [.query leafIndex oldOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after)).Nodup) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      (before ++ [.query leafIndex oldOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after) = true := by
  rw [CappedEncodingMonitor.runObserved_eq_standard_validActions _ _
    CappedEncodingMonitor.State.valid_empty]
  have hquery : CappedEncodingMonitor.ActionValid (.query leafIndex oldOutput) := holdValid
  have hsign : CappedEncodingMonitor.ActionValid (.sign leafIndex signedOutput) := hsignedValid
  rw [CappedEncodingMonitor.validActions_append_two_valid before middle after
    (.query leafIndex oldOutput) (.sign leafIndex signedOutput) hquery hsign]
  apply EncodingMonitor.runObserved_empty_eq_true_of_query_before_sign_of_nodup
    leafIndex oldOutput signedOutput (CappedEncodingMonitor.validActions before)
      (CappedEncodingMonitor.validActions middle)
      (CappedEncodingMonitor.validActions after) hdigest
  change (EncodingMonitor.observedSignLeafIndices
    (CappedEncodingMonitor.validActions
      (before ++ [.query leafIndex oldOutput] ++ middle ++
        [.sign leafIndex signedOutput] ++ after))).Nodup at hnodup
  rw [CappedEncodingMonitor.validActions_append_two_valid before middle after
    (.query leafIndex oldOutput) (.sign leafIndex signedOutput) hquery hsign] at hnodup
  exact hnodup

theorem CappedEncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_valid
    (leafIndex : LeafIndex) (signedOutput forgedOutput : HashOutput)
    (before middle after : EncodingActionTrace)
    (hsignedValid : TargetSum.ValidDigest (truncateHash signedOutput))
    (hforgedValid : TargetSum.ValidDigest (truncateHash forgedOutput))
    (hdigest : truncateHash signedOutput = truncateHash forgedOutput)
    (hnodup : (CappedEncodingMonitor.validObservedSignLeafIndices
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex forgedOutput] ++ after)).Nodup) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex forgedOutput] ++ after) = true := by
  rw [CappedEncodingMonitor.runObserved_eq_standard_validActions _ _
    CappedEncodingMonitor.State.valid_empty]
  have hsign : CappedEncodingMonitor.ActionValid (.sign leafIndex signedOutput) := hsignedValid
  have hquery : CappedEncodingMonitor.ActionValid (.query leafIndex forgedOutput) := hforgedValid
  rw [CappedEncodingMonitor.validActions_append_two_valid before middle after
    (.sign leafIndex signedOutput) (.query leafIndex forgedOutput) hsign hquery]
  apply EncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_nodup
    leafIndex signedOutput forgedOutput (CappedEncodingMonitor.validActions before)
      (CappedEncodingMonitor.validActions middle)
      (CappedEncodingMonitor.validActions after) hdigest
  change (EncodingMonitor.observedSignLeafIndices
    (CappedEncodingMonitor.validActions
      (before ++ [.sign leafIndex signedOutput] ++ middle ++
        [.query leafIndex forgedOutput] ++ after))).Nodup at hnodup
  rw [CappedEncodingMonitor.validActions_append_two_valid before middle after
    (.sign leafIndex signedOutput) (.query leafIndex forgedOutput) hsign hquery] at hnodup
  exact hnodup

theorem cappedDetailedGameWithEncodingTrace_freshSigningCollision_monitorHit
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding)
    (hcollision : ∃ entry ∈ result.2.1.2,
      entry.FreshSigningEncodingCollision result.1.secretKey) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty result.2.2 = true := by
  obtain ⟨entry, hentry, hentryCollision⟩ := hcollision
  have hactionNodup :=
    cappedDetailedGameWithEncodingTrace_validSignLeafIndices_nodup_of_winning
      adversary result hmem hevent
  have hrepresented :=
    cappedDetailedGameWithEncodingTrace_validFreshSigningCollisionsRepresented
      adversary result hmem
  obtain ⟨signedOutput, oldOutput, before, middle, after, hsignedValid,
    holdValid, hdigest, hactions⟩ :=
    hrepresented
      (cappedDetailedGameWithEncodingTrace_signingLeafIndices_nodup_of_winning
        adversary result hmem hevent)
      entry hentry hentryCollision
  rw [hactions]
  exact CappedEncodingMonitor.runObserved_empty_eq_true_of_query_before_sign_of_valid
    entry.request.leafIndex oldOutput signedOutput before middle after holdValid
      hsignedValid hdigest.symm (by simpa [hactions] using hactionNodup)

theorem cappedDetailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
    (adversary : Adversary)
    (result : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace))
    (hmem : result ∈ support (cappedDetailedGameWithEncodingTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs result.2.1.1 result.1 .encoding)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash result.2.1.1 result.1.secretKey.parameter
        result.1.forgery.leafIndex
        (result.1.forgery.message, result.1.forgery.signature.randomness)) =
      some encoding)
    (hcollision : ∃ entry ∈ result.2.1.2,
      entry.PostSigningFreshForgedEncodingCollision result.1.secretKey
        result.1.forgery result.2.1.1) :
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty result.2.2 = true := by
  have htraceNodup :=
    cappedDetailedGameWithEncodingTrace_signingLeafIndices_nodup_of_winning adversary result
      hmem hevent
  have hactionNodup :=
    cappedDetailedGameWithEncodingTrace_validSignLeafIndices_nodup_of_winning adversary result
      hmem hevent
  unfold cappedDetailedGameWithEncodingTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold cappedDetailedGameAfterKeygenWithEncodingTrace at hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨forgery, adversaryState, encodingTrace⟩, hadversary, hverifyRest⟩ := hrest
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hinvariants := cappedEncodingTracedMappedAdversaryImpl_postSigningInvariants
    publicKey secretKey (adversary.main publicKey) ((keyCache, []), [])
    (forgery, (adversaryState, encodingTrace))
    (by simp [FreshSigningActionsRepresented])
    (by simp [PostSigningQueriesRepresented]) hadversary
  have hsignActions := hinvariants.1
  have hpostSigning := hinvariants.2
  obtain ⟨entry, hentry, hfreshForged, hentryForgedFresh,
    signature, hsignature, hsignedFresh⟩ := hcollision
  obtain ⟨collisionSignature, signedOutput, forgedOutput,
    hcollisionSignature, hleafIndex, _hforgedInitiallyFresh, hsigned,
    hforgedFinal, _hdistinct, hdigest⟩ := hfreshForged
  have hsignatureEq : collisionSignature = signature := by
    rw [hsignature] at hcollisionSignature
    exact (Option.some.inj hcollisionSignature).symm
  subst collisionSignature
  have hleafIndex' : entry.request.leafIndex = forgery.leafIndex := by
    simpa using hleafIndex
  let forgedInput := Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
    (forgery.message, forgery.signature.randomness)
  have hforgedValid : TargetSum.ValidDigest (truncateHash forgedOutput) := by
    refine ⟨encoding, ?_⟩
    simpa [Concrete.CacheView.encodingHash, forgedInput,
      Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedFinal] using hdecode
  have hsignedValid : TargetSum.ValidDigest (truncateHash signedOutput) := by
    rw [hdigest]
    exact hforgedValid
  cases hadversaryForged : adversaryState.1 forgedInput with
  | some adversaryOutput =>
      have hcacheLe : adversaryState.1 ≤ finalCache :=
        xmssRom_cache_le _ adversaryState.1 (verified, finalCache) hverify
      have hadversaryOutputEq : adversaryOutput = forgedOutput := by
        have hcached := hcacheLe hadversaryForged
        change finalCache forgedInput = some forgedOutput at hforgedFinal
        rw [hforgedFinal] at hcached
        exact Option.some.inj hcached.symm
      subst adversaryOutput
      obtain ⟨before, middle, after, hactionsBase⟩ :=
        hpostSigning htraceNodup entry hentry signature signedOutput forgedInput
          forgedOutput hsignature hsignedFresh hsigned
          (by simp [forgedInput, hleafIndex']) hentryForgedFresh hadversaryForged
      have hactions :
          appendVerificationEncodingObservation secretKey forgery adversaryState.1
              finalCache encodingTrace =
            before ++ [.sign entry.request.leafIndex signedOutput] ++ middle ++
              [.query entry.request.leafIndex forgedOutput] ++ after := by
        simpa [appendVerificationEncodingObservation, forgedInput,
          hadversaryForged] using hactionsBase
      rw [hactions]
      exact CappedEncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_valid
        entry.request.leafIndex signedOutput forgedOutput before middle after hsignedValid
        hforgedValid hdigest
        (by simpa [hactions] using hactionNodup)
  | none =>
      obtain ⟨actionOutput, before, middle, hactionOutput, hactionsBase⟩ :=
        hsignActions entry hentry signature hsignature hsignedFresh
      have hactionOutputEq : actionOutput = signedOutput := by
        rw [hsigned] at hactionOutput
        exact Option.some.inj hactionOutput.symm
      subst actionOutput
      have hactions :
          appendVerificationEncodingObservation secretKey forgery adversaryState.1
              finalCache encodingTrace =
            before ++ [.sign entry.request.leafIndex signedOutput] ++ middle ++
              [.query entry.request.leafIndex forgedOutput] ++ [] := by
        have hactionsBase' : encodingTrace =
            before ++ [.sign entry.request.leafIndex signedOutput] ++ middle := by
          simpa using hactionsBase
        change finalCache forgedInput = some forgedOutput at hforgedFinal
        rw [hactionsBase']
        simp [appendVerificationEncodingObservation, forgedInput,
          hadversaryForged, hforgedFinal, ← hleafIndex', List.append_assoc]
      rw [hactions]
      exact CappedEncodingMonitor.runObserved_empty_eq_true_of_sign_before_query_of_valid
        entry.request.leafIndex signedOutput forgedOutput before middle [] hsignedValid
        hforgedValid hdigest
        (by simpa [hactions] using hactionNodup)


end XmssSecurity
