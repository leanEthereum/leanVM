import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualOriginalBudget
import SphincsSecurity.Proof.Residual.RetainedResidualSigningCandidates
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation)
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem knownEncodingMessage_afterSigning (routing : Routing) (record : SigningRecord) :
    knownEncodingMessage (routing.afterSigning record).known = knownEncodingMessage routing.known := by
  funext position
  exact routing.afterSigning_graph record _

section Local

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_encodingClean (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (hlive : (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).1 ≠ none) :
    ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
      (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache := by
  let actions := ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows
  have hp := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => (result.1, result.2.memory))
    (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  have hf := ResidualByteFrontend.hashQueryResult_project parameter inputs words routing.disclosed routing.known actions
    actual seed input (project state) hcovered
    (ResidualByteAction.freshPrefix_local parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input)
  have h := congrArg (ResidualByteFrontend.checkedResult
    (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input.val) (hp.trans hf)
  change ((checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).1,
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external) = _ at h
  have hanswer := congrArg Prod.fst h
  have hcache := congrArg (fun result => result.2.cache) h
  rw [hanswer] at hlive
  rw [hcache]
  generalize ResidualByteFrontend.publicCachedReply inputs actions actual seed input (project state).memory = answer at hlive ⊢
  cases answer with
  | none => exact False.elim (hlive rfl)
  | some answer =>
      dsimp only [ResidualByteFrontend.checkedResult, Option.bind_some] at hlive ⊢
      split at hlive
      · exact False.elim (hlive rfl)
      · rename_i hsafe
        exact ResidualByteFrontend.replyClean_store _ _ hclean input.val answer hsafe

theorem lazyByteRun_bind {A B : Type} (routing : Routing) (computation : OracleComp OracleWorld A)
    (next : A → OracleComp OracleWorld B) (state : State inputs) :
    lazyByteRun parameter inputs hencoding words publicReplies selections rows routing (computation >>= next) state =
      (lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer =>
          lazyByteRun parameter inputs hencoding words publicReplies selections rows routing (next answer) result.2)) := by
  simp only [lazyByteRun, simulateQ_bind, lazyRun_bind]

theorem lazyByteRun_encodingClean {Result : Type} (routing : Routing) (computation : OracleComp OracleWorld Result)
    (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (result : Option Result × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state result ≠ 0)
    (hlive : result.1 ≠ none) :
    ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) result.2.memory.external.cache := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyByteRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hclean
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      cases input with
      | inl input =>
          rw [lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          exact ih answer (hnext answer) state ha hcovered hclean result hresult hlive
      | inr input =>
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [lazyByteRun_bind, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨middle, hmiddle, hresult⟩ := hresult
          have ha' := lazyRun_nonempty (environment parameter inputs hencoding words publicReplies selections rows) _ state ha middle hmiddle
          have hcovered' := lazyRun_rowsCovered parameter inputs hencoding words publicReplies selections rows _ state ha hcovered middle hmiddle
          rcases middle with ⟨answer, after⟩
          cases answer with
          | none =>
              simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              exact False.elim (hlive rfl)
          | some answer =>
              obtain ⟨actual, seed, heq⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows
                routing input hin state ha (some answer, after) hmiddle
              have hs := checkedHashResult_encodingClean parameter inputs hencoding words publicReplies selections rows routing actual seed
                ⟨input, hin⟩ state hcovered hclean (by rw [← heq]; simp)
              rw [← heq] at hs
              exact ih answer (hnext answer) after ha' hcovered' hs result hresult hlive

theorem lazyRun_jointSigningProgram_encodingClean (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message) ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) state.memory.external.cache)
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state result ≠ 0) :
    ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) result.2.memory.external.cache := by
  rw [ResidualByteFrontend.jointSigningProgram, simulateQ_bind, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨middle, hmiddle, hresult⟩ := hresult
  rw [← lazyByteRun] at hmiddle
  obtain ⟨⟨work, hwork⟩, hcandidates⟩ := lazyByteRun_message_support parameter inputs hencoding words publicReplies selections rows
    routing _ hinputs (ResidualByteFrontend.publicSigningWork_messageOnly parameter root routing.known words selections message)
    state hcovered middle hmiddle
  have hs := lazyByteRun_encodingClean parameter inputs hencoding words publicReplies selections rows routing _ hinputs state ha hcovered hclean
    middle hmiddle (by rw [hwork]; simp)
  have ha' : ∀ coordinate, (middle.2.candidates coordinate).Nonempty := by rw [hcandidates]; exact ha
  rw [hwork, Option.elim_some] at hresult
  obtain ⟨actual, _, hmemory⟩ := lazyRun_completeWork_support parameter inputs hencoding words publicReplies selections rows
    routing work middle.2 ha' result hresult
  rw [hmemory]
  exact hs

omit parameter hencoding in
theorem lazyRun_request_encodingClean (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.memory.routing.known) words selections) state.memory.external.cache)
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0)
    (hlive : result.1 ≠ none) :
    ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage result.2.memory.routing.known) words selections) result.2.memory.external.cache := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ state ha result hresult
      rw [hrouting]
      exact lazyByteRun_encodingClean key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
        _ hinputs state ha hcovered hclean result hresult hlive
  | inr message =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0 at hresult
      rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
        map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      have hwork := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key
        state.memory.routing.known words selections message).trans hinputs
      have hs := lazyRun_jointSigningProgram_encodingClean key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key.root message hwork state ha hcovered hclean raw hraw
      have hrouting := lazyRun_embed_routing key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing _ state ha raw hraw
      rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hwork
      obtain ⟨record, hrecord⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing key.root message hwork state ha hcovered raw hraw
      simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      change ResidualByteFrontend.ReplyClean
        (PublicEncodingMatch.Match key.parameter (knownEncodingMessage (raw.2.memory.routing.afterSigning record).known) words selections)
        raw.2.memory.external.cache
      rw [knownEncodingMessage_afterSigning, hrouting]
      exact hs

end Local

theorem referenceEncodingAuxiliary_select (encoding : ReferenceEncodingAuxiliary)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support) (position : EncodingPosition) :
    FirstSuccessTable.select decodeEncodingOutput (fun counter => encoding.rows (position, counter)) = encoding.selections position :=
  referenceAuxiliarySample_select ∅ ⟨encoding.selections, encoding.rows, fun _ => 0⟩
    (referenceEncodingAuxiliary_support_seed ∅ encoding hencoding (fun _ => 0)) position

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

end SphincsSecurity.Concrete.RetainedResidual
