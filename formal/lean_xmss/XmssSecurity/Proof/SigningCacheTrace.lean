import XmssSecurity.Proof.SigningLogConsistency

open OracleComp OracleSpec

namespace XmssSecurity

structure SigningCacheEntry where
  request : SignRequest
  signature : Option Signature
  initialCache : QueryCache HashSpec
  finalCache : QueryCache HashSpec

abbrev SigningCacheTrace := List SigningCacheEntry

def SigningCacheTrace.CachesLe
    (trace : SigningCacheTrace) (cache : QueryCache HashSpec) : Prop :=
  ∀ entry ∈ trace, entry.initialCache ≤ cache ∧ entry.finalCache ≤ cache

def SigningCacheTrace.toSigningLog (trace : SigningCacheTrace) : QueryLog SigningSpec :=
  trace.map fun entry => ⟨entry.request, entry.signature⟩

theorem SigningTranscript.returned_toSigningLog_iff
    (trace : SigningCacheTrace) (request : SignRequest) (signature : Signature) :
    SigningTranscript.Returned trace.toSigningLog request signature ↔
      ∃ entry ∈ trace,
        entry.request = request ∧ entry.signature = some signature := by
  constructor
  · rintro ⟨loggedEntry, hlogged, hrequest, hsignature⟩
    rw [SigningCacheTrace.toSigningLog, List.mem_map] at hlogged
    obtain ⟨entry, hentry, heq⟩ := hlogged
    subst loggedEntry
    exact ⟨entry, hentry, hrequest, hsignature⟩
  · rintro ⟨entry, hentry, hrequest, hsignature⟩
    refine ⟨⟨entry.request, entry.signature⟩, ?_, hrequest, hsignature⟩
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩

def SigningCacheEntry.EncodingInputPrehit
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature output,
    entry.signature = some signature ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some output

def SigningCacheEntry.PreexistingEncodingCollision
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput oldInput oldOutput,
    entry.signature = some signature ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex oldInput) =
        some oldOutput ∧
    oldInput ≠ (entry.request.message, signature.randomness) ∧
    truncateHash signedOutput = truncateHash oldOutput

def SigningCacheEntry.FreshSigningEncodingCollision
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput oldInput oldOutput,
    entry.signature = some signature ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = none ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex oldInput) =
        some oldOutput ∧
    oldInput ≠ (entry.request.message, signature.randomness) ∧
    truncateHash signedOutput = truncateHash oldOutput

/-- The signer selected an input that was already cached, and another input at the same leaf index has the same digest. -/
def SigningCacheEntry.CachedSelectionCollision
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput otherInput otherOutput,
    entry.signature = some signature ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    cache (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex otherInput) =
      some otherOutput ∧
    otherInput ≠ (entry.request.message, signature.randomness) ∧
    truncateHash signedOutput = truncateHash otherOutput

def SigningCacheEntry.FreshForgedEncodingCollision
    (secretKey : SecretKey) (forgery : Forgery)
    (finalCache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  ∃ signature signedOutput forgedOutput,
    entry.signature = some signature ∧
    entry.request.leafIndex = forgery.leafIndex ∧
    entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = none ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some signedOutput ∧
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = some forgedOutput ∧
    Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness) ∧
    truncateHash signedOutput = truncateHash forgedOutput

def SigningCacheEntry.PostSigningFreshForgedEncodingCollision
    (secretKey : SecretKey) (forgery : Forgery)
    (finalCache : QueryCache HashSpec) (entry : SigningCacheEntry) : Prop :=
  entry.FreshForgedEncodingCollision secretKey forgery finalCache ∧
    entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter forgery.leafIndex
        (forgery.message, forgery.signature.randomness)) = none ∧
    ∃ signature, entry.signature = some signature ∧
      entry.initialCache
        (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
          (entry.request.message, signature.randomness)) = none

def SigningCacheEntry.SuccessfulEncodingCached
    (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  ∀ signature, entry.signature = some signature →
    ∃ output, entry.finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) = some output

def SigningCacheTrace.SuccessfulEncodingsCached
    (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.SuccessfulEncodingCached secretKey

theorem SigningCacheEntry.preexistingEncodingCollision_cases
    (secretKey : SecretKey) (entry : SigningCacheEntry)
    (hevent : entry.PreexistingEncodingCollision secretKey) :
    entry.EncodingInputPrehit secretKey ∨
      entry.FreshSigningEncodingCollision secretKey := by
  obtain ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
    hsigned, hold, hne, hdigest⟩ := hevent
  cases hinitial : entry.initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter entry.request.leafIndex
        (entry.request.message, signature.randomness)) with
  | none =>
      exact Or.inr ⟨signature, signedOutput, oldInput, oldOutput, hsignature,
        hinitial, hsigned, hold, hne, hdigest⟩
  | some output =>
      exact Or.inl ⟨signature, output, hsignature, hinitial⟩

def signingLogFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : QueryLog SigningSpec :=
  match input with
  | .inl _ => []
  | .inr request => [⟨request, output⟩]

def signingCacheTraceUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec)
    (trace : SigningCacheTrace) : SigningCacheTrace :=
  match input with
  | .inl _ => trace
  | .inr request =>
      trace ++ [SigningCacheEntry.mk request output initialCache finalCache]

def signingLogUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalCache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : QueryLog SigningSpec :=
  log ++ signingLogFragment input output

theorem signingCacheTraceUpdate_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).toSigningLog =
      signingLogUpdate input initialCache output finalCache trace.toSigningLog := by
  cases input <;> simp [signingCacheTraceUpdate, signingLogUpdate,
    signingLogFragment, SigningCacheTrace.toSigningLog]

theorem SigningCacheTrace.CachesLe.mono
    {trace : SigningCacheTrace} {initialCache finalCache : QueryCache HashSpec}
    (htrace : trace.CachesLe initialCache) (hle : initialCache ≤ finalCache) :
    trace.CachesLe finalCache := by
  intro entry hentry
  exact ⟨(htrace entry hentry).1.trans hle, (htrace entry hentry).2.trans hle⟩

theorem signingCacheTraceUpdate_cachesLe
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (htrace : trace.CachesLe initialCache) (hle : initialCache ≤ finalCache) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).CachesLe
      finalCache := by
  cases input with
  | inl worldInput =>
      exact htrace.mono hle
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact (htrace entry hentry).imp (fun h => h.trans hle) (fun h => h.trans hle)
      · simp only [List.mem_singleton] at hentry
        subst entry
        exact ⟨hle, le_rfl⟩

end XmssSecurity
