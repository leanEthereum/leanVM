import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeRace
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_2 : SampleableType Randomness := SampleableType.ofFintype Randomness
attribute [local irreducible] signAttempt signDigestAttemptPrefix

abbrev DigestAttemptResult := Randomness × (Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)

noncomputable def cachedDigestAttemptRate (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) : ENNReal :=
  Pr[fun randomness : Randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) | ($ᵗ Randomness : ProbComp Randomness)]

noncomputable def digestAttemptExpectation : Nat → SecretKey → Message → QueryCache HashSpec → ENNReal
  | 0, _, _, _ => 0
  | attempts + 1, key, message, cache => 1 +
      ∑' result, Pr[= result | signDigestAttemptPrefix key message cache] *
        if result.2.1 = none then digestAttemptExpectation attempts key message result.2.2 else 0

theorem signDigestAttemptPrefix_support_attempt (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache)) :
    result.2 ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt key message result.1)).run cache) := by
  rw [signDigestAttemptPrefix, mem_support_bind_iff] at hr
  obtain ⟨randomness, _, hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨attempt, ha, hr⟩ := hr
  simp only [mem_support_pure_iff] at hr
  have hfirst := congrArg Prod.fst hr
  have hsecond := congrArg Prod.snd hr
  rw [hfirst, hsecond]
  exact ha

theorem signDigestAttemptPrefix_cache_le (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache)) : cache ≤ result.2.2 := by
  apply simulateQ_romImpl_cache_le (liftM (signAttempt key message result.1 :
    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache result.2
  rw [simulateQ_romImpl_liftM]
  exact signDigestAttemptPrefix_support_attempt key message cache result hr

theorem signDigestAttemptPrefix_cached_result (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : DigestAttemptResult) (output : HashOutput)
    (hr : result ∈ support (signDigestAttemptPrefix key message cache))
    (hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message result.1)) = some output) :
    result.2.1 = signAttemptResultOfOutput output :=
  signAttempt_result_of_cached key message result.1 cache result.2.2 result.2.1 output
    ((signDigestAttemptPrefix_cache_le key message cache result hr) hc)
    (signDigestAttemptPrefix_support_attempt key message cache result hr)

theorem probEvent_signDigestAttemptPrefix_favorablePrehit_eq
    (referenceCache workingCache : QueryCache HashSpec) (key : SecretKey) (message : Message) (P : FewTimeView → Prop) :
    Pr[FavorablePrehitAttempt referenceCache key message P | signDigestAttemptPrefix key message workingCache] =
      cachedDigestAttemptRate key message referenceCache P := by
  rw [signDigestAttemptPrefix, probEvent_bind_eq_tsum, cachedDigestAttemptRate, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro randomness
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] *
    Pr[fun _ => ∃ output, referenceCache (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = some output ∧ signAttemptResultOfOutput output ≠ none ∧
        P (hashOutputFewTimeView output) |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run workingCache] = _
  rw [probEvent_const]
  rw [probFailure_of_liftM_PMF, tsub_zero]
  split_ifs <;> simp only [mul_one, mul_zero]

end SphincsSecurity.Concrete
