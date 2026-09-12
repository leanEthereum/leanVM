import SphincsSecurity.Proof.Reference.ReferenceCertificateTrace
import SphincsSecurity.Proof.Fts.OriginalProposalPrefixBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
open RetainedResidual (signingInput)
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
  frontierRoot honestNode

theorem eligibleSigningViews_eq_of_cache_agree (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput)
    (hlog : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      before (signingInput key message signature) = after (signingInput key message signature)) :
    eligibleSigningViews (messageAnswers key.parameter before) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter after) key.root payload log := by
  funext slot
  change eligibleSigningView? _ _ _ (log.get slot) = eligibleSigningView? _ _ _ (log.get slot)
  have hentry := List.get_mem log slot
  generalize he : log.get slot = entry at hentry ⊢
  rcases entry with ⟨message, response⟩
  cases response with
  | none => simp [eligibleSigningView?]
  | some signature =>
      simp only [eligibleSigningView?, observedSigningView?, Option.bind_eq_bind', Option.bind_some]
      change (if messageDigestPayload key.root message signature.randomness = payload then none
        else before (signingInput key message signature) >>= fun answer => pure (hashOutputFewTimeView answer)) = _
      rw [hlog message signature hentry]
      rfl

theorem recordedCache_agrees (f : QueryImpl HashSpec Id) (trace : Trace) : (recordedCache f trace).AgreesWithFn f := by
  intro input output houtput
  by_cases hm : (input, f input) ∈ trace.toList
  · simpa only [recordedCache, if_pos hm, Option.some.injEq] using houtput
  · simp only [recordedCache, if_neg hm] at houtput
    cases houtput

theorem boundaryEval_verify_message (key : SecretKey) (f : QueryImpl HashSpec Id) (forgery : Forgery) :
    (signingInput key forgery.message forgery.signature, f (signingInput key forgery.message forgery.signature)) ∈
      (boundaryEval key.parameter f (verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature)).2.messageCalls := by
  rw [verify, boundaryEval_bind, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
  apply Or.inl
  have hquery : boundaryEval key.parameter f
      (oracleHash (signingInput key forgery.message forgery.signature) : OracleComp HashSpec HashOutput) =
      (f (signingInput key forgery.message forgery.signature), signingBoundaryTrace key.parameter
        (.inr (signingInput key forgery.message forgery.signature)) (f (signingInput key forgery.message forgery.signature))) := rfl
  rw [messageDigest, boundaryEval_bind]
  change _ ∈ ((boundaryEval key.parameter f
    (oracleHash (signingInput key forgery.message forgery.signature) : OracleComp HashSpec HashOutput)).2 * 1).messageCalls
  rw [hquery, mul_one]
  change (signingInput key forgery.message forgery.signature, f (signingInput key forgery.message forgery.signature)) ∈
    (signingBoundaryTrace key.parameter (.inr (signingInput key forgery.message forgery.signature))
      (f (signingInput key forgery.message forgery.signature))).messageCalls
  rw [signingBoundaryTrace, if_pos (show FtsProbeSimulation.MessageHashInput key.parameter
    (signingInput key forgery.message forgery.signature) from ⟨_, rfl⟩)]
  exact List.mem_singleton_self _

theorem certificate_to_message_record (key : SecretKey) (f : QueryImpl HashSpec Id)
    (before : (Forgery × QueryLog SigningSpec) × SigningBoundaryTrace) (trace : Trace) (required : Finset FtsTree)
    (horigin : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ before.1.2 →
      ReferenceSigningWitness.SignatureOrigin key f message signature before.2)
    (htrace : RetainedResidual.TraceValid key.parameter f (completeCertificateRest key f before).2)
    (hcertificate : TargetCertificateAt key required (ReferenceFtsCoverage.transcriptCache f before.2 trace, before.1.2)
      (signingInput key before.1.1.message before.1.1.signature)) :
    TargetCertificateAt key required (hashRowsCache (completeCertificateRest key f before).2.messageCalls, before.1.2)
      (signingInput key before.1.1.message before.1.1.signature) := by
  have hrows : ∀ row ∈ (completeCertificateRest key f before).2.messageCalls, row.2 = f row.1 :=
    fun row hr => (htrace row hr).2
  have hsign (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ before.1.2) :
      hashRowsCache (completeCertificateRest key f before).2.messageCalls (signingInput key message signature) =
        some (f (signingInput key message signature)) := by
    apply hashRowsCache_lookup _ f hrows
    rw [completeCertificateRest, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
    exact Or.inl (horigin message signature hentry).1
  have htarget : hashRowsCache (completeCertificateRest key f before).2.messageCalls
      (signingInput key before.1.1.message before.1.1.signature) = some (f (signingInput key before.1.1.message before.1.1.signature)) := by
    apply hashRowsCache_lookup _ f hrows
    rw [completeCertificateRest, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
    exact Or.inr (boundaryEval_verify_message key f before.1.1)
  obtain ⟨output, houtput, hm, ha, hcovered⟩ := hcertificate
  have hf : f (signingInput key before.1.1.message before.1.1.signature) = output :=
    recordedCache_agrees f _ houtput
  refine ⟨output, htarget.trans (congrArg some hf), hm, ha, ?_⟩
  have hviews := eligibleSigningViews_eq_of_cache_agree key
    (ReferenceFtsCoverage.transcriptCache f before.2 trace) (hashRowsCache (completeCertificateRest key f before).2.messageCalls)
    before.1.2 (payloadOf (signingInput key before.1.1.message before.1.1.signature)) (fun message signature hentry =>
      (ReferenceFtsCoverage.cache_signing (horigin message signature hentry) trace).trans (hsign message signature hentry).symm)
  simpa only [TargetCoveredOn, ← hviews] using hcovered

theorem referenceForgeryRest_traceValid_atRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = (ReferenceVerifierWitness.rootedKey key f).root)
    (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy adversary)) :
    RetainedResidual.TraceValid key.parameter f (completeCertificateRest { key with root := root } f before.1).2 := by
  have hrecord : ({ key with root := root },
      (completeCertificateRest { key with root := root } f before.1).1,
      (completeCertificateRest { key with root := root } f before.1).2) ∈ support
      ((fun before : AdversaryTrace =>
        let result := completeCertificateRest ({ key with root := root } : SecretKey) f before.1
        (({ key with root := root } : SecretKey), result.1, result.2)) <$>
        referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
          (referenceTableSelection key f) dummy adversary) := by
    rw [support_map]
    exact ⟨before, hb, rfl⟩
  rw [referenceForgeryRest_certificateRecord_atRoot key f root hroot dummy adversary, support_map] at hrecord
  obtain ⟨result, hr, heq⟩ := hrecord
  have heq' : result = completeCertificateRest { key with root := root } f before.1 := congrArg Prod.snd heq
  rw [heq'] at hr
  apply RetainedResidual.fixedBoundaryRun_traceValid key.parameter f _ _
  simpa only [mem_support_iff, probOutput_def] using hr

theorem referenceForgeryRest_origin_atRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = (ReferenceVerifierWitness.rootedKey key f).root)
    (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy adversary))
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ before.1.1.2) :
    ReferenceSigningWitness.SignatureOrigin { key with root := root } f message signature before.1.2 := by
  rw [referenceForgeryRest, ReferenceVerifierWitness.source_root, ← hroot] at hb
  have hw : referenceFamilyWords (referenceTableSelection key f) dummy =
      canonicalReferenceWords ({ key with root := root } : SecretKey) f dummy := by
    rw [referenceFamilyWords_selected]
    exact (ReferenceVerifierWitness.canonicalReferenceWords_root key f root dummy).symm
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root, hw] at hb
  exact ReferenceSigningWitness.fixedTrace_origin { key with root := root } f _ _
    (isSigningFrontier_canonical { key with root := root } f _)
    (frontierReferenceWord_canonical { key with root := root } f dummy) _ before hb message signature hentry

theorem referenceForgeryRest_certificate_atRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = (ReferenceVerifierWitness.rootedKey key f).root)
    (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy adversary))
    (trace : Trace) (required : Finset FtsTree)
    (hcertificate : TargetCertificateAt { key with root := root } required
      (ReferenceFtsCoverage.transcriptCache f before.1.2 trace, before.1.1.2)
      (signingInput { key with root := root } before.1.1.1.message before.1.1.1.signature)) :
    TargetCertificateAt { key with root := root } required
      (hashRowsCache (completeCertificateRest { key with root := root } f before.1).2.messageCalls, before.1.1.2)
      (signingInput { key with root := root } before.1.1.1.message before.1.1.1.signature) :=
  certificate_to_message_record { key with root := root } f before.1 trace required
    (referenceForgeryRest_origin_atRoot key f root hroot dummy adversary before hb)
    (referenceForgeryRest_traceValid_atRoot key f root hroot dummy adversary before hb) hcertificate

noncomputable def ReferenceForgerySample.fullCertificate {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let key := ReferenceVerifierWitness.rootedKey sample.1 f
  let result := (sample.context dummy).2.2.2
  SigningTranscript.Valid sample.2.2.1.1.2 ∧
    TargetCertificateAt key Finset.univ
      (ReferenceFtsCoverage.transcriptCache f sample.2.2.1.2 (result.before * result.after), sample.2.2.1.1.2)
      (signingInput key sample.2.2.1.1.1.message sample.2.2.1.1.1.signature)

noncomputable def ReferenceForgerySample.remainingFts {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let key := ReferenceVerifierWitness.rootedKey sample.1 f
  let result := (sample.context dummy).2.2.2
  SigningTranscript.Valid sample.2.2.1.1.2 ∧
    (ReferenceFtsCoverage.NearGuess key f sample.2.2.1.1.2 sample.2.2.1.2 (result.before * result.after) sample.2.2.1.1.1 ∨
      ReferenceFtsCoverage.TwoGuesses key f sample.2.2.1.1.2 (result.before * result.after) sample.2.2.1.1.1)

theorem ReferenceForgerySample.ftsOutcome_cases {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) (h : sample.ftsOutcome dummy) :
    sample.fullCertificate dummy ∨ sample.remainingFts dummy := by
  rcases h with ⟨hvalid, hfull | hrest⟩
  · exact Or.inl ⟨hvalid, hfull⟩
  · exact Or.inr ⟨hvalid, hrest⟩

theorem referenceForgeryGame_full_record (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (sample : ReferenceForgerySample inputs)
    (hsample : sample ∈ support (referenceForgeryGame inputs hencoding dummy adversary))
    (hfull : sample.fullCertificate dummy) : sample.certificateRecord.full := by
  obtain ⟨href, hb⟩ := referenceForgeryGame_support inputs hencoding dummy adversary sample hsample
  rw [referenceFamilyOracleSample_selections sample.1 inputs (hencoding sample.1.parameter)
    (hgraph sample.1.parameter) sample.2.1 href] at hb
  refine ⟨hfull.1, signingInput (ReferenceVerifierWitness.rootedKey sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2))
    sample.2.2.1.1.1.message sample.2.2.1.1.1.signature, ?_⟩
  exact referenceForgeryRest_certificate_atRoot sample.1 (finiteHashAnswer ∅ inputs sample.2.1.2) _ rfl
    dummy adversary sample.2.2 hb _ Finset.univ hfull.2

private theorem probEvent_le_project {Source Result : Type} (source : SPMF Source) (native : ProbComp Result)
    (projection : Source → Result) (event : Source → Prop) (nativeEvent : Result → Prop)
    (hlaw : projection <$> source = 𝒟[native])
    (hevent : ∀ sample ∈ support source, event sample → nativeEvent (projection sample)) :
    Pr[event | source] ≤ Pr[nativeEvent | native] := by
  calc
    _ ≤ Pr[nativeEvent ∘ projection | source] := _root_.probEvent_mono hevent
    _ = Pr[nativeEvent | projection <$> source] := (probEvent_map source projection nativeEvent).symm
    _ = Pr[nativeEvent | native] := by rw [hlaw]; rfl

theorem referenceForgeryGame_full_le (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[ReferenceForgerySample.fullCertificate dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      Pr[OriginalFullCertificate | originalCertificateSource adversary] :=
  (probEvent_le_project _ _ ReferenceForgerySample.certificateRecord (ReferenceForgerySample.fullCertificate dummy)
    CertificateTraceRecord.full (referenceForgeryGame_native_certificateRecord dummy adversary)
    (referenceForgeryGame_full_record _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary)).trans
      (certificateTraceProgram_full_le adversary)

theorem forgeAdvantage_le_remainingFts_small_budget (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf))
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    forgeAdvantage scheme adversary ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ +
      Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  have hfts : Pr[ReferenceForgerySample.ftsOutcome dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      Pr[OriginalFullCertificate | originalCertificateSource adversary] +
      Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
    refine (_root_.probEvent_mono (mx := referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
      (p := ReferenceForgerySample.ftsOutcome dummy)
      (q := fun sample => sample.fullCertificate dummy ∨ sample.remainingFts dummy)
      (fun sample _ h => sample.ftsOutcome_cases dummy h)).trans ?_
    exact (probEvent_or_le _ _ _).trans (add_le_add (referenceForgeryGame_full_le dummy adversary) le_rfl)
  have h := (forgeAdvantage_le_referenceForgery_cases dummy hdummy adversary).trans (add_le_add hfts le_rfl)
  rw [add_right_comm, add_comm (Pr[OriginalFullCertificate | originalCertificateSource adversary])] at h
  exact h.trans (add_le_add (original_primitive_add_full_certificate_small_budget dummy adversary q hbound hsmall) le_rfl)

end SphincsSecurity.Concrete
