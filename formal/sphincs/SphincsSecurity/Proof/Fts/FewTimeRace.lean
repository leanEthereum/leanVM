import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeFresh
import SphincsSecurity.Proof.Fts.FewTimePrehit
/-!
# A weighted prefix split for the digest race

The cached branch of a digest retry loop wins immediately, a rejected answer continues, and an
ordinary successful answer ends the event. The weighted split below keeps the continuation
probability instead of paying one full copy of its bound at every retry.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable local instance instSampleableTypeRandomness_2 : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem cachedMessageEntryCount_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    cachedMessageEntryCount cache parameter root message ≤ QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSet cache parameter root message ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1
  simpa only [cachedMessageEntryCount, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)

set_option maxRecDepth 100000 in
theorem Concrete.probEvent_signAttempt_fresh_success_eq
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none) :
    Pr[fun result => result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ := by
  have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
    secretKey message randomness cache hcache
    (fun result => pure result)
  simp only [bind_pure] at hcoordinates
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates]
  change Pr[fun result => result.1 ≠ none |
    ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
      pure ∘ fun coordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates))] = _
  rw [probEvent_bind_pure_comp]
  let event : HashOutputCoordinates → Prop := fun coordinates => coordinates.1.2 = 0
  calc
    Pr[fun coordinates : HashOutputCoordinates =>
        (signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates),
          cache.cacheQuery
            (tweakableHashInput secretKey.parameter .message
              (messageDigestPayload secretKey.root message randomness))
            (hashOutputCoordinatesEquiv.symm coordinates)).1 ≠ none |
        ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] =
        Pr[event | ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
      apply probEvent_congr'
      · intro coordinates _
        exact signAttemptResultOfOutput_coordinates_ne_none_iff coordinates
      · rfl
    _ = Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 |
        Prod.fst <$> ($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun coordinates : FewTimeView × FtsLeaf => coordinates.2 = 0 |
        ($ᵗ (FewTimeView × FtsLeaf) : ProbComp (FewTimeView × FtsLeaf))] := by
      apply probEvent_congr'
      · intro coordinates _
        rfl
      · exact evalDist_map_fst_uniformSample_prod
    _ = _ := by
      simpa only [and_true, probEvent_True_eq_sub, probFailure_of_liftM_PMF,
        tsub_zero, mul_one] using
        probEvent_uniformDigestCoordinates_admissible_view (fun _ => True)

noncomputable def Concrete.signDigestAttemptPrefix
    (secretKey : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    ProbComp (Randomness ×
      (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)) :=
  ($ᵗ Randomness) >>= fun randomness =>
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache >>= fun result =>
        pure (randomness, result)

theorem Concrete.signDigestLoop_run_succ_eq_attemptPrefix
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (signDigestLoop (attempts + 1) secretKey message)).run cache =
      signDigestAttemptPrefix secretKey message cache >>= fun attempt =>
        signDigestLoopContinuation attempts secretKey message attempt.1 attempt.2 := by
  rw [signDigestLoop_run_succ_eq, signDigestAttemptPrefix]
  simp only [bind_assoc, pure_bind]

def Concrete.FavorablePrehitAttempt (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (attempt : Randomness ×
      (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)) : Prop :=
  ∃ output, referenceCache
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message attempt.1)) = some output
    ∧ signAttemptResultOfOutput output ≠ none
    ∧ P (hashOutputFewTimeView output)

end SphincsSecurity
