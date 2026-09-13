import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheSize
import SphincsSecurity.Proof.Fts.FewTimeLoop
import SphincsSecurity.Proof.Scheme.Secrets
import SphincsSecurity.Proof.Reference.SigningTrace
/-!
# Cached signer views

The cached-input branch retains the predicate on the cached answer's few-time view. Its randomizer
reuse cost is charged only against cache entries that satisfy that predicate.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

def cachedMessageInputSetWhere (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cachedMessageInputSet cache parameter root message |
    Concrete.signAttemptResultOfOutput entry.2 ≠ none
      ∧ P (Concrete.hashOutputFewTimeView entry.2)}

noncomputable def cachedMessageEntryCountWhere (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) : ℝ≥0∞ :=
  (((cachedMessageInputSetWhere cache parameter root message P).encard : ENat) : ℝ≥0∞)

theorem cachedMessageEntryCountWhere_le_enncard
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≤
      QueryCache.enncard cache := by
  have hsubset : cachedMessageInputSetWhere cache parameter root message P ⊆ cache.toSet := by
    intro entry hentry
    exact hentry.1.1
  simpa only [cachedMessageEntryCountWhere, QueryCache.enncard] using
    ENat.toENNReal_mono (Set.encard_le_encard hsubset)

def Concrete.PrehitSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : Concrete.FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ ∃ output, referenceCache
        (tweakableHashInput secretKey.parameter .message
          (Concrete.messageDigestPayload secretKey.root message randomness)) = some output
        ∧ Concrete.signAttemptResultOfOutput output = some (index, leaves)
        ∧ P (Concrete.hashOutputFewTimeView output)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.signDigestLoop_initial_cached_result
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (initialCache finalCache : QueryCache HashSpec) (output : HashOutput)
    (hcached : initialCache
      (tweakableHashInput secretKey.parameter .message
        (Concrete.messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (some (randomness, index, leaves), finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.signDigestLoop attempts secretKey message)).run initialCache)) :
    Concrete.signAttemptResultOfOutput output = some (index, leaves) := by
  induction attempts generalizing initialCache finalCache with
  | zero =>
      simp [Concrete.signDigestLoop] at hmem
  | succ attempts ih =>
      rw [Concrete.signDigestLoop_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨sampled, _hsampled, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
        exact hattempt
      have hle : initialCache ≤ attemptCache :=
        simulateQ_romImpl_cache_le
          (liftM (Concrete.signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
          initialCache (attempt, attemptCache) (by
            rw [simulateQ_romImpl_liftM]
            exact hattempt)
      cases hattemptResult : attempt with
      | none =>
          have hfuture : (some (randomness, index, leaves), finalCache) ∈ support
              ((simulateQ romImpl
                (Concrete.signDigestLoop attempts secretKey message)).run attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult] using hfinish
          exact ih attemptCache finalCache (hle hcached) hfuture
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinishEq :
              (some (randomness, index, leaves), finalCache) =
                (some (sampled, selectedIndex, selectedLeaves), attemptCache) := by
            simpa only [Concrete.signDigestLoopContinuation, hattemptResult, support_pure,
              Set.mem_singleton_iff] using hfinish
          have htuple : (randomness, index, leaves) =
              (sampled, selectedIndex, selectedLeaves) :=
            Option.some.inj (congrArg Prod.fst hfinishEq)
          have hrandomness : randomness = sampled := congrArg Prod.fst htuple
          have hcached' : attemptCache
              (tweakableHashInput secretKey.parameter .message
                (Concrete.messageDigestPayload secretKey.root message sampled)) = some output :=
            hle (by
              rw [← hrandomness]
              exact hcached)
          have hattemptSelected : (some (selectedIndex, selectedLeaves), attemptCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec _)
                (Concrete.signAttempt secretKey message sampled)).run initialCache) := by
            have heq : (attempt, attemptCache) =
                (some (selectedIndex, selectedLeaves), attemptCache) :=
              Prod.ext hattemptResult rfl
            rw [← heq]
            exact hattempt'
          have hselectedResult :=
            (Concrete.signAttempt_result_of_cached secretKey message sampled initialCache
              attemptCache (some (selectedIndex, selectedLeaves)) output hcached'
              hattemptSelected).symm
          exact hselectedResult.trans (congrArg some (congrArg Prod.snd htuple).symm)

end SphincsSecurity
