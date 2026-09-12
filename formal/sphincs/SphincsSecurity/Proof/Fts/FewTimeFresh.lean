import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeLoop
import SphincsSecurity.Proof.Fts.FewTimePadding
import SphincsSecurity.Proof.Fts.FewTimeSignerView
/-!
# Fresh signer views

During a digest retry loop, every message input added after the loop's reference cache contains an
inadmissible answer. Thus a successful input absent from the reference cache is answered freshly,
and its retained few-time view has the uniform distribution even after all failed retries.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev HashOutputRest :=
  FtsLeaf × BitVec (hashOutputBits - messageDigestBits)

def reorderHashOutputCoordinates :
    (HashOutputRest × FewTimeView) ≃ HashOutputCoordinates where
  toFun value := ((value.2, value.1.1), value.1.2)
  invFun value := ((value.1.2, value.2), value.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutputCoordinates_bind_reordered {Result : Type}
    (continuation : HashOutputCoordinates → ProbComp Result) :
    𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
      𝒟[($ᵗ HashOutputRest : ProbComp HashOutputRest) >>= fun rest =>
        ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          continuation ((view, rest.1), rest.2)] := by
  let paired : ProbComp (HashOutputRest × FewTimeView) := do
    let rest ← $ᵗ HashOutputRest
    let view ← $ᵗ FewTimeView
    pure (rest, view)
  have hpaired :
      𝒟[paired] = 𝒟[($ᵗ (HashOutputRest × FewTimeView) :
        ProbComp (HashOutputRest × FewTimeView))] := by
    exact evalDist_independent_uniform_pair
  have hreordered :
      𝒟[reorderHashOutputCoordinates <$> paired] =
        𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
    calc
      𝒟[reorderHashOutputCoordinates <$> paired] =
          reorderHashOutputCoordinates <$> 𝒟[paired] := by rw [evalDist_map]
      _ = reorderHashOutputCoordinates <$>
          𝒟[($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [hpaired]
      _ = 𝒟[reorderHashOutputCoordinates <$>
          ($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [evalDist_map]
      _ = 𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
        evalDist_map_bijective_uniform_cross
          (α := HashOutputRest × FewTimeView) (β := HashOutputCoordinates)
          (reorderHashOutputCoordinates : HashOutputRest × FewTimeView →
            HashOutputCoordinates)
          reorderHashOutputCoordinates.bijective
  calc
    𝒟[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
        𝒟[(reorderHashOutputCoordinates <$> paired) >>= continuation] := by
      rw [evalDist_bind, ← hreordered, ← evalDist_bind]
    _ = _ := by
      simp only [paired, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        reorderHashOutputCoordinates, Function.comp_apply]
      rfl

theorem probEvent_uniformDigestCoordinates_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 ∧ P coordinates.1 |
      ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  change Pr[fun coordinates : FewTimeView × FtsLeaf =>
      coordinates.2 = 0 ∧ P coordinates.1 |
    Prod.mk <$> ($ᵗ FewTimeView : ProbComp FewTimeView) <*>
      ($ᵗ FtsLeaf : ProbComp FtsLeaf)] = _
  calc
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          Pr[fun leaf : FtsLeaf => leaf = 0 |
            ($ᵗ FtsLeaf : ProbComp FtsLeaf)] := by
      apply probEvent_seq_map_eq_mul
      intro view _hview leaf _hleaf
      simp [and_comm]
    _ = Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ := by
      rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, Fintype.card_fin]
    _ = _ := by rw [mul_comm]

set_option maxRecDepth 100000 in
theorem probEvent_uniformHashOutput_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput =>
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  let coordinates : HashOutput → FewTimeView × FtsLeaf := fun output =>
    digestCoordinates (truncateMessageDigest output)
  let event : FewTimeView × FtsLeaf → Prop := fun value => value.2 = 0 ∧ P value.1
  calc
    Pr[fun output : HashOutput =>
        signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        Pr[event | coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_map]
      congr 1
      funext output
      rw [signAttemptResultOfOutput_ne_none_iff]
      rfl
    _ = Pr[event |
        ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (by
        simpa only [coordinates] using evalDist_hashOutput_digestCoordinates_uniform)
    _ = _ := probEvent_uniformDigestCoordinates_admissible_view P

def OnlyRejectedNewMessageEntries (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) : Prop :=
  ∀ randomness output,
    referenceCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none →
    workingCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output →
    signAttemptResultOfOutput output = none

theorem onlyRejectedNewMessageEntries_self (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) :
    OnlyRejectedNewMessageEntries cache cache secretKey message := by
  intro randomness output hmiss hhit
  rw [hmiss] at hhit
  simp at hhit

theorem onlyRejectedNewMessageEntries_cacheRejected
    (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (output : HashOutput)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message)
    (hrejected : signAttemptResultOfOutput output = none) :
    OnlyRejectedNewMessageEntries referenceCache
      (workingCache.cacheQuery
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled)) output)
      secretKey message := by
  intro randomness found hreferenceFound hfound
  let foundInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : foundInput = sampledInput
  · have hfound' : some output = some found := by
      calc
        some output =
            (workingCache.cacheQuery sampledInput output) sampledInput := by
              rw [QueryCache.cacheQuery_self]
        _ = (workingCache.cacheQuery sampledInput output) foundInput := by rw [hsame]
        _ = some found := by simpa only [foundInput, sampledInput] using hfound
    rw [← Option.some.inj hfound']
    exact hrejected
  · have hworking : workingCache foundInput = some found := by
      rw [QueryCache.cacheQuery_of_ne workingCache output hsame] at hfound
      simpa only [foundInput, sampledInput] using hfound
    exact hinvariant randomness found hreferenceFound hworking

set_option maxRecDepth 100000 in
theorem onlyRejectedNewMessageEntries_of_failed_attempt
    (referenceCache beforeCache afterCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache beforeCache secretKey message)
    (hmem : (none, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message sampled)).run beforeCache)) :
    OnlyRejectedNewMessageEntries referenceCache afterCache secretKey message := by
  intro randomness output hreference hafter
  let target := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : target = sampledInput
  · apply Eq.symm
    have hafterSampled : afterCache sampledInput = some output := by
      change afterCache target = some output at hafter
      rw [← hsame]
      exact hafter
    change afterCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message sampled)) = some output at hafterSampled
    exact signAttempt_result_of_cached secretKey message sampled beforeCache afterCache
      none output hafterSampled hmem
  · by_cases hbefore : beforeCache target = none
    · change beforeCache
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none at hbefore
      change (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) ≠
        tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled) at hsame
      have hnone := signAttempt_cache_other_none secretKey message sampled beforeCache afterCache
        none hmem _ hbefore hsame
      rw [hnone] at hafter
      simp at hafter
    · obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp hbefore
      have hmemWorld : (none, afterCache) ∈ support
          ((simulateQ romImpl
            (liftM (signAttempt secretKey message sampled :
              OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
                OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))).run
              beforeCache) := by
        rw [simulateQ_romImpl_liftM]
        exact hmem
      have hle : beforeCache ≤ afterCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
          beforeCache (none, afterCache) hmemWorld
      have heq : prior = output := Option.some.inj ((hle hprior).symm.trans hafter)
      rw [← heq]
      exact hinvariant randomness prior hreference hprior

def FreshSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ referenceCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) = none
      ∧ P (selectedFewTimeView index leaves)

end SphincsSecurity.Concrete
