import XmssSecurity.Proof.CappedEncodingExpectedBound
import XmssSecurity.Proof.LossDecomposition
import XmssSecurity.Scan.PerKey

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- Every signature selected an input whose initially cached digest, if any, is valid. -/
def SigningCacheTrace.SelectedValid (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, ∀ signature, entry.signature = some signature → ∀ o,
    entry.initialCache (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
      (entry.request.message, signature.randomness)) = some o →
    TargetSum.ValidDigest (truncateHash o)

theorem cappedCacheTracedMappedAdversaryImpl_selectedValid
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.SelectedValid secretKey)
    (hmem : result ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.SelectedValid secretKey := by
  refine OracleComp.simulateQ_run_preservesInv
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.2.SelectedValid secretKey) ?_ computation (initialCache, initialTrace) htrace result hmem
  intro input state hstate queryResult hquery
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply, mem_support_bind_iff] at hquery
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hquery
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst queryResult
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using hstate
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact hstate entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        intro signature hsignature o ho
        exact Ghost.sign_selected_valid secretKey (r := (output, finalCache)) hbase hsignature ho

theorem cappedDetailedGameAfterKeygenWithSigningTrace_selectedValid
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : result ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey initialCache)) :
    result.2.2.SelectedValid secretKey := by
  unfold cappedDetailedGameAfterKeygenWithSigningTrace at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedCacheTracedMappedAdversaryImpl_selectedValid publicKey secretKey
    (adversary.main publicKey) initialCache [] (forgery, (adversaryCache, trace))
    (fun _ h => by cases h) hadversary

open Ghost in
/-- A winning cached-selection collision is a pre-signing partner or a post-signing repeat. -/
theorem cachedSelection_event_le (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (x : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hx : x ∈ support
      (cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey initialCache))
    (hevent : WinningOutcomeBadEventOccurs x.2.1 x.1 .encoding ∧
      ∃ entry ∈ x.2.2, entry.CachedSelectionCollision x.1.secretKey x.2.1) :
    x.2.2.leafIndices.Nodup ∧
      (PreBad secretKey x.2.2 ∨ PostBad secretKey.parameter x.2.2 x.2.1) := by
  obtain ⟨hsk, hlog, hle, -⟩ :=
    cappedDetailedGameAfterKeygenWithSigningTrace_invariants adversary publicKey secretKey initialCache x hx
  have hpres := cappedDetailedGameAfterKeygenWithSigningTrace_preservesOtherValidEncodingInputs
    adversary publicKey secretKey initialCache x hx
  have hsel := cappedDetailedGameAfterKeygenWithSigningTrace_selectedValid
    adversary publicKey secretKey initialCache x hx
  obtain ⟨hwin, entry, hentry, signature, so, z, oo, hs, hso, hoo, hz, ht⟩ := hevent
  rw [hsk] at hso hoo
  have hnodup : x.2.2.leafIndices.Nodup := by
    have hvalid := hwin.signingTranscript_valid
    rw [← hlog] at hvalid
    unfold SigningTranscript.Valid at hvalid
    simpa [SigningCacheTrace.leafIndices, SigningCacheTrace.toSigningLog, List.map_map,
      Function.comp_def] using hvalid
  have hfirst := first_of_nodup hnodup hentry
  refine ⟨hnodup, ?_⟩
  cases hz0 : entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex z) with
  | some o =>
      have hoo' : oo = o := Option.some.inj (hoo.symm.trans ((hle entry hentry).1 hz0))
      subst hoo'
      exact Or.inl ⟨entry.request.leafIndex, entry, hfirst, signature, so, z, oo, hs, hso, hz0, hz, ht⟩
  | none =>
      refine Or.inr ⟨entry.request.leafIndex, entry, hfirst, signature, so, z, oo, hs, hso, ?_, hoo, ht⟩
      cases hlocal : entry.finalCache
          (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex z) with
      | none => exact hlocal
      | some o3 =>
          have houtput : o3 = oo := Option.some.inj (((hle entry hentry).2 hlocal).symm.trans hoo)
          have hvalid := hsel entry hentry signature hs so hso
          obtain ⟨encoding, hdecode⟩ := hvalid
          have hdecodeLocal : TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash entry.finalCache secretKey.parameter
                entry.request.leafIndex z) = some encoding := by
            rw [Concrete.CacheView.encodingHash, Concrete.CacheView.digestAt_eq_of_cache_eq_some hlocal,
              houtput, ← ht]
            exact hdecode
          have hne : Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
              (entry.request.message, signature.randomness) ≠
              Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex z := fun h =>
            hz (Concrete.CacheView.encodingInput_injective _ _ h).symm
          have hnone := hpres entry hentry signature hs entry.request.leafIndex z encoding hdecodeLocal hne hz0
          rw [hlocal] at hnone
          cases hnone

/-- The source game's verification, returning the forgery. -/
noncomputable def verifyCont (publicKey : PublicKey) (forgery : Forgery) : OracleComp OracleWorld (Forgery × Bool) :=
  Concrete.scheme.verify publicKey forgery.leafIndex forgery.message forgery.signature >>= fun verified =>
    pure (forgery, verified)

open Ghost in
theorem cappedDetailedGameAfterKeygenWithSigningTrace_eq_map (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey initialCache =
      (fun y : (Forgery × State) × ((Forgery × Bool) × QueryCache HashSpec) =>
        ((⟨publicKey, secretKey, y.1.1, y.1.2.1.2.toSigningLog, y.2.1.2⟩ : GameOutcome), (y.2.2, y.1.2.1.2))) <$>
      ((simulateQ (impl publicKey secretKey) (adversary.main publicKey)).run ((initialCache, []), 0) >>= fun r =>
        (fun v => (r, v)) <$> (simulateQ romImpl (verifyCont publicKey r.1)).run r.2.1.1) := by
  have h : (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey) (adversary.main publicKey)).run
      (initialCache, []) = Prod.map id Prod.fst <$>
        (simulateQ (impl publicKey secretKey) (adversary.main publicKey)).run ((initialCache, []), 0) :=
    (OracleComp.extendState_run_proj_eq _ _ _ _ _).symm
  unfold cappedDetailedGameAfterKeygenWithSigningTrace
  rw [h]
  simp [verifyCont, map_bind, bind_map_left, Functor.map_map]

/-- Lane 2's digest term: a cached selection with a colliding input. -/
theorem capped_cachedSelection_probability_le_expectedDigest
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q) (hq : q < 2 ^ 127) :
    Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] ≤
      CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  have hproj : Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] =
      Pr{let x ← cappedDetailedGameWithSigningTrace adversary}[WinningOutcomeBadEventOccurs x.2.1 x.1 .encoding ∧
            ∃ entry ∈ x.2.2, entry.CachedSelectionCollision x.1.secretKey x.2.1] := by
    rw [← cappedDetailedGameWithEncodingTrace_projection, prEvent_map]
    rfl
  rw [hproj, cappedDetailedGameWithSigningTrace, OracleComp.prEvent_bind_eq_tsum,
    CappedEncodingMonitor.expectedPostKeygenEncodingQueries, div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun keyResult => ?_
  by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
  · rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    obtain ⟨⟨publicKey, secretKey⟩, cache0⟩ := keyResult
    have hc0 : ∀ e y, cache0 (Partner.input secretKey.parameter e y) = none := fun e y =>
      Concrete.precomputedKeygen_cache_none_encodingInput _ (by simpa [Concrete.scheme] using hkey) e y
    have hcore := Ghost.collision_le publicKey secretKey hc0 _ hq (adversary.main publicKey)
      (verifyCont publicKey)
      (cappedSourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen q adversary hbound _ hkey)
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl Ghost.N_ne_zero) (Or.inl Ghost.N_ne_top)]
    rw [mul_assoc, ENNReal.mul_le_mul_iff_right Ghost.N_ne_zero Ghost.N_ne_top] at hcore
    refine le_trans ?_ hcore
    rw [mul_comm]
    refine mul_le_mul' le_rfl ?_
    rw [cappedDetailedGameAfterKeygenWithSigningTrace_eq_map, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun y hy hev => ?_
    refine cachedSelection_event_le adversary publicKey secretKey cache0 _ ?_ hev
    rw [cappedDetailedGameAfterKeygenWithSigningTrace_eq_map, support_map]
    exact ⟨y, hy, rfl⟩
  · rw [(prEvent_eq_zero_of_not_mem_support _) hkey, zero_mul]
    exact zero_le

end XmssSecurity
