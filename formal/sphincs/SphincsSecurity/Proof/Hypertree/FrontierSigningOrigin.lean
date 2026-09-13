import SphincsSecurity.Proof.Residual.RetainedResidualSigningOrigin
import SphincsSecurity.Proof.Reference.VerifierTraceSource

/-! ## CausalVerifierTrace -/

namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierRoot maskOtsPrefixes

theorem ContainsRun.mul_left {Result : Type} {f : QueryImpl HashSpec Id} {trace : Trace} {computation : OracleComp HashSpec Result}
    (h : ContainsRun f trace computation) (before : Trace) : ContainsRun f (before * trace) computation := by
  intro input hi
  exact List.mem_append_right _ (h input hi)

abbrev AdversaryTrace := ((Forgery × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace

end SphincsSecurity.Concrete.OtsContactTrace

namespace SphincsSecurity.Concrete.ReferenceSigningWitness

open _root_.OracleComp OracleSpec OtsContactTrace
attribute [local irreducible] signDigestLoop signAfterDigest boundaryEval fixedBoundaryRun frontierSigningRun frontierAdversaryImpl frontierAdversaryRun
set_option backward.isDefEq.respectTransparency false

private theorem supported_nonzero {Result : Type} (computation : ProbComp Result) (result : Result)
    (hr : result ∈ support computation) : 𝒟[computation] result ≠ 0 := by
  simpa only [mem_support_iff, probOutput_def] using hr

def SignatureOrigin (key : SecretKey) (f : QueryImpl HashSpec Id) (message : Message) (signature : Signature)
    (trace : SigningBoundaryTrace) : Prop :=
  let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)
  let digest := truncateMessageDigest (f input)
  (input, f input) ∈ trace.messageCalls ∧ Admissible digest ∧
    evalWithAnswerFn f (signAfterDigest key signature.randomness (digestIndex digest) (digestLeaves digest)) = some signature

theorem SignatureOrigin.mono {key : SecretKey} {f : QueryImpl HashSpec Id} {message : Message} {signature : Signature}
    {before after : SigningBoundaryTrace} (h : SignatureOrigin key f message signature before)
    (htrace : before.messageCalls ⊆ after.messageCalls) : SignatureOrigin key f message signature after :=
  ⟨htrace h.1, h.2⟩

theorem signing_origin (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (message : Message) (signature : Signature) (trace : SigningBoundaryTrace)
    (hr : (some signature, trace) ∈ support (frontierSigningRun key.parameter key.root f key.ftsSecret words frontier message)) :
    SignatureOrigin key f message signature trace := by
  rw [frontierSigningRun, ← fixedBoundaryRun_signWithView_frontier key f words frontier hfrontier hwords, support_map] at hr
  obtain ⟨⟨⟨response, view⟩, recorded⟩, hr, heq⟩ := hr
  have hresponse : response = some signature := congrArg (fun result => result.1) heq
  have htrace : recorded = trace := congrArg (fun result => result.2) heq
  subst response recorded
  have h := RetainedResidual.fixedBoundaryRun_signing_origin key f message signature view trace
    (supported_nonzero _ _ hr)
  exact ⟨h.2.2.2, h.2.1, h.2.2.1⟩

private theorem logged_run_query_bind {Result : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    ((simulateQ (impl.withTraceAppend signingLogFragment) (liftM (OracleSpec.query input) >>= next)).run).run =
      (impl input).run >>= fun first =>
        (fun tail => ((tail.1.1, signingLogFragment input first.1 ++ tail.1.2), first.2 * tail.2)) <$>
          ((simulateQ (impl.withTraceAppend signingLogFragment) (next first.1)).run).run := by
  simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withTraceAppend_apply,
    WriterT.run_bind, WriterT.run_tell, WriterT.run_monadLift', WriterT.run_map, bind_map_left, bind_assoc,
    pure_bind, Functor.map_map]
  rfl

private theorem logged_run_origin {Result : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (impl : QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp))
    (horigin : ∀ message signature trace, (some signature, trace) ∈ support ((impl (.inr message)).run) →
      SignatureOrigin key f message signature trace)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (result : (Result × QueryLog SigningSpec) × SigningBoundaryTrace)
    (hr : result ∈ support (((simulateQ (impl.withTraceAppend signingLogFragment) computation).run).run))
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ result.1.2) :
    SignatureOrigin key f message signature result.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      cases hentry
  | query_bind input next ih =>
      rw [logged_run_query_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨tail, htail, rfl⟩ := hr
      rcases List.mem_append.mp hentry with hhead | htailEntry
      · cases input with
        | inl input => cases hhead
        | inr request =>
            have heq := List.mem_singleton.mp hhead
            have hm : message = request := congrArg Sigma.fst heq
            have hs : some signature = first.1 := congrArg (fun entry : SigningEntry => entry.2) heq
            subst request
            have hsign : (some signature, first.2) ∈ support ((impl (.inr message)).run) := by
              simpa only [← hs] using (show (first.1, first.2) ∈ support ((impl (.inr message)).run) from hfirst)
            apply (horigin message signature first.2 hsign).mono
            intro entry hmem
            rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append]
            exact Or.inl hmem
      · apply (ih first.1 tail htail htailEntry).mono
        intro entry hmem
        rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append]
        exact Or.inr hmem

theorem adversaryRun_origin {Result : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (result : (Result × QueryLog SigningSpec) × SigningBoundaryTrace)
    (hr : result ∈ support (frontierAdversaryRun key.parameter key.root f key.ftsSecret words frontier computation))
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ result.1.2) :
    SignatureOrigin key f message signature result.2 := by
  have horigin (request : Message) (signed : Signature) (trace : SigningBoundaryTrace)
      (hs : (some signed, trace) ∈ support
        ((frontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier (.inr request)).run)) :
      SignatureOrigin key f request signed trace := by
    rw [frontierAdversaryImpl, WriterT.run_mk] at hs
    exact signing_origin key f words frontier hfrontier hwords request signed trace hs
  rw [frontierAdversaryRun] at hr
  exact logged_run_origin key f (frontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier)
    horigin computation result hr message signature hentry

theorem fixedTrace_origin {Result : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace)
    (hr : result ∈ support (fixedTrace f
      (CausalFrontierProgram.adversaryRun key.parameter key.root f key.ftsSecret words frontier computation)))
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ result.1.1.2) :
    SignatureOrigin key f message signature result.1.2 := by
  have hbase : result.1 ∈ support (Prod.fst <$> fixedTrace f
      (CausalFrontierProgram.adversaryRun key.parameter key.root f key.ftsSecret words frontier computation)) := by
    rw [support_map]
    exact ⟨result, hr, rfl⟩
  rw [fixedTrace_forget, CausalFrontierProgram.fixed_adversaryRun] at hbase
  exact adversaryRun_origin key f words frontier hfrontier hwords computation result.1 hbase message signature hentry

end SphincsSecurity.Concrete.ReferenceSigningWitness
