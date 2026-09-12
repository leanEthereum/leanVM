import SphincsSecurity.Proof.Residual.RetainedResidualSigningOrigin
import SphincsSecurity.Proof.Residual.RetainedResidualVerifySupport
import SphincsSecurity.Proof.Residual.RetainedResidualReplay
import SphincsSecurity.Proof.Residual.RetainedResidualInitial
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAfterDigest boundaryEval
set_option backward.isDefEq.respectTransparency false

def signingInput (key : SecretKey) (message : Message) (signature : Signature) : HashInput :=
  tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)

def signingView (key : SecretKey) (oracle : QueryImpl HashSpec Id) (message : Message) (signature : Signature) : FewTimeView :=
  hashOutputFewTimeView (oracle (signingInput key message signature))

def SignatureOrigin (key : SecretKey) (oracle : QueryImpl HashSpec Id) (cache : ExternalCache)
    (message : Message) (signature : Signature) : Prop :=
  let input := signingInput key message signature
  let digest := truncateMessageDigest (oracle input)
  cache input ≠ none ∧ Admissible digest ∧
    evalWithAnswerFn oracle (signAfterDigest key signature.randomness (digestIndex digest) (digestLeaves digest)) = some signature

structure SigningHistory (key : SecretKey) (oracle : QueryImpl HashSpec Id) (memory : Memory) : Prop where
  entries : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ memory.log →
    SignatureOrigin key oracle memory.external.cache message signature
  disclosed : ∀ index tree leaf, memory.routing.disclosed index tree leaf →
    ∃ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ memory.log ∧
      index = (signingView key oracle message signature).1 ∧ leaf = (signingView key oracle message signature).2 tree

private theorem cacheFold_present (entries : List (HashInput × HashOutput)) (cache : ExternalCache)
    (input : HashInput) (hcache : cache input ≠ none) :
    (entries.foldl (fun (current : ExternalCache) entry => Function.update current entry.1 (some entry.2)) cache) input ≠ none := by
  induction entries generalizing cache with
  | nil => exact hcache
  | cons entry entries ih =>
      apply ih
      change Function.update cache entry.1 (some entry.2) input ≠ none
      by_cases heq : input = entry.1
      · subst input
        rw [Function.update_self]
        exact Option.some_ne_none _
      · rw [Function.update_of_ne heq]
        exact hcache

private theorem cacheFold_entry (entries : List (HashInput × HashOutput)) (cache : ExternalCache)
    (input : HashInput) (answer : HashOutput) (hentry : (input, answer) ∈ entries) :
    (entries.foldl (fun (current : ExternalCache) entry => Function.update current entry.1 (some entry.2)) cache) input ≠ none := by
  induction entries generalizing cache with
  | nil => cases hentry
  | cons entry entries ih =>
      rcases List.mem_cons.mp hentry with heq | hmem
      · subst entry
        apply cacheFold_present entries _ input
        change Function.update cache input (some answer) input ≠ none
        rw [Function.update_self]
        exact Option.some_ne_none _
      · exact ih _ hmem

theorem SignatureOrigin.mono {key : SecretKey} {oracle : QueryImpl HashSpec Id} {before after : ExternalCache}
    {message : Message} {signature : Signature} (horigin : SignatureOrigin key oracle before message signature)
    (hcache : ∀ input, before input ≠ none → after input ≠ none) : SignatureOrigin key oracle after message signature :=
  ⟨hcache _ horigin.1, horigin.2⟩

theorem SigningHistory.transport {key : SecretKey} {oracle : QueryImpl HashSpec Id} {before after : Memory}
    (hhistory : SigningHistory key oracle before) (hlog : after.log = before.log)
    (hdisclosed : after.routing.disclosed = before.routing.disclosed)
    (hcache : ∀ input, before.external.cache input ≠ none → after.external.cache input ≠ none) :
    SigningHistory key oracle after := by
  constructor
  · intro message signature hentry
    rw [hlog] at hentry
    exact (hhistory.entries message signature hentry).mono hcache
  · intro index tree leaf hdisclose
    rw [hdisclosed] at hdisclose
    obtain ⟨message, signature, hentry, hcoords⟩ := hhistory.disclosed index tree leaf hdisclose
    exact ⟨message, signature, hlog ▸ hentry, hcoords⟩

theorem SigningHistory.applyBoundary {key : SecretKey} {oracle : QueryImpl HashSpec Id} {memory : Memory}
    (hhistory : SigningHistory key oracle memory) (trace : SigningBoundaryTrace) :
    SigningHistory key oracle (memory.applyBoundary trace) :=
  hhistory.transport rfl rfl (fun input hcache => cacheFold_present trace.messageCalls _ input hcache)

private theorem disclosed_afterSigning (routing : InterleavedResidual.Routing) (record : SigningRecord)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (h : (routing.afterSigning record).disclosed index tree leaf) :
    routing.disclosed index tree leaf ∨ ∃ signature view, record.1.1 = some signature ∧ record.1.2 = some view ∧
      index = view.1 ∧ leaf = view.2 tree := by
  rcases record with ⟨⟨signature, view⟩, trace⟩
  cases signature with
  | none => exact Or.inl h
  | some signature =>
      cases view with
      | none => exact Or.inl h
      | some view =>
          rcases h with hold | hnew
          · exact Or.inl hold
          · exact Or.inr ⟨signature, view, rfl, rfl, hnew⟩

theorem SigningHistory.recordSigning {key : SecretKey} {oracle : QueryImpl HashSpec Id} {memory : Memory}
    (hhistory : SigningHistory key oracle memory) (message : Message) (record : SigningRecord)
    (hrecord : 𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] record ≠ 0) :
    SigningHistory key oracle ((memory.applyBoundary record.2).recordSigning message record) := by
  have hbase := hhistory.applyBoundary record.2
  constructor
  · intro signedMessage signature hentry
    change (⟨signedMessage, some signature⟩ : SigningEntry) ∈ memory.log ++ [⟨message, record.1.1⟩] at hentry
    rcases List.mem_append.mp hentry with hold | hnew
    · exact hbase.entries signedMessage signature hold
    · have heq := List.mem_singleton.mp hnew
      have hmessage : signedMessage = message := congrArg Sigma.fst heq
      have hsignature : some signature = record.1.1 := congrArg (fun entry : SigningEntry => entry.2) heq
      subst signedMessage
      have hrecord' : 𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)]
          ((some signature, record.1.2), record.2) ≠ 0 := by
        simpa only [hsignature] using hrecord
      obtain ⟨_, hadmissible, hsign, hmem⟩ := fixedBoundaryRun_signing_origin key oracle message signature record.1.2 record.2 hrecord'
      exact ⟨cacheFold_entry record.2.messageCalls _ _ _ hmem, hadmissible, hsign⟩
  · intro index tree leaf hdisclose
    have h := disclosed_afterSigning memory.routing record index tree leaf hdisclose
    rcases h with hold | ⟨signature, view, hsignature, hview, hcoords⟩
    · obtain ⟨signedMessage, signature, hentry, hcoords⟩ := hhistory.disclosed index tree leaf hold
      exact ⟨signedMessage, signature, List.mem_append.mpr (Or.inl hentry), hcoords⟩
    · have hrecord' : 𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)]
          ((some signature, some view), record.2) ≠ 0 := by
        change 𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] ((record.1.1, record.1.2), record.2) ≠ 0 at hrecord
        simpa only [hsignature, hview] using hrecord
      have hselected := (fixedBoundaryRun_signing_origin key oracle message signature (some view) record.2 hrecord').1
      have hselected' : view = signingView key oracle message signature := Option.some.inj hselected
      refine ⟨message, signature, ?_, ?_⟩
      · apply List.mem_append.mpr
        right
        rw [hsignature]
        exact List.mem_singleton_self _
      · simpa only [← hselected'] using hcoords

theorem SigningHistory.fixedHashStep {inputs : Finset HashInput} (context : Context inputs) (input : HashInput)
    (memory : Memory) (hhistory : SigningHistory context.key context.oracle memory) (answer : HashOutput)
    (hlive : (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing
      context.actual context.oracle input memory).1 = some answer) :
    SigningHistory context.key context.oracle
      (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).2 := by
  apply hhistory.transport (fixedHashStep_log context input memory)
    (congrArg InterleavedResidual.Routing.disclosed (fixedHashStep_routing ..))
  intro row hcache
  rw [fixedHashStep_cache context input memory answer hlive]
  by_cases heq : row = input
  · subst row
    rw [Function.update_self]
    exact Option.some_ne_none _
  · rw [Function.update_of_ne heq]
    exact hcache

theorem fixedSourceImpl_signingHistory {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain) (memory : Memory) (hhistory : SigningHistory context.key context.oracle memory)
    (answer : (OracleWorld + SigningSpec).Range input) (after : Memory)
    (hresult : (fixedSourceImpl context input).run.run memory (some answer, after) ≠ 0) :
    SigningHistory context.key context.oracle after := by
  cases input with
  | inl input =>
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query] at hresult
      cases input with
      | inl input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨value, _, hresult⟩ := hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
          exact hresult.2 ▸ hhistory
      | inr input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          have h := hhistory.fixedHashStep context input memory answer (congrArg Prod.fst hresult).symm
          simpa only [← hresult] using h
  | inr message =>
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨record, hrecord, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
      exact hresult.2 ▸ hhistory.recordSigning message record hrecord

theorem fixedSourceRun_signingHistory {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory)
    (hhistory : SigningHistory context.key context.oracle memory) (value : Result) (after : Memory)
    (hresult : fixedSourceRun context computation memory (some value, after) ≠ 0) :
    SigningHistory context.key context.oracle after := by
  induction computation using OracleComp.inductionOn generalizing memory value after with
  | pure value =>
      simp only [fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
      exact hresult.2 ▸ hhistory
  | query_bind input next ih =>
      rw [fixedSourceRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq, Option.some_ne_none, false_and, not_not] at hresult
      | some answer =>
          exact ih answer middle (fixedSourceImpl_signingHistory context input memory hhistory answer middle hmiddle) value after hresult

theorem signingHistory_initial (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (exposed : InitialPublicLabels words) :
    SigningHistory key oracle (initialMemory words exposed) := by
  constructor
  · intro message signature hentry
    cases hentry
  · intro index tree leaf hdisclose
    cases hdisclose

end SphincsSecurity.Concrete.RetainedResidual
