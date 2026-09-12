import SphincsSecurity.Proof.Reference.ReferenceVerifierInstantiation
import SphincsSecurity.Proof.Residual.RetainedResidualSigningHistory
import SphincsSecurity.Proof.Fts.BankedTargetEnvelope
namespace SphincsSecurity.Concrete.ReferenceFtsCoverage

open _root_.OracleComp OracleSpec OtsContactTrace
open RetainedResidual (signingInput signingView)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAfterDigest canonicalGraphInputs canonicalEncodingInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def transcriptCache (f : QueryImpl HashSpec Id) (boundary : SigningBoundaryTrace) (trace : Trace) : QueryCache HashSpec :=
  recordedCache f (FreeMonoid.ofList boundary.messageCalls * trace)

def CoveredByLog (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec) (target : FewTimeView) (tree : FtsTree) : Prop :=
  ∃ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log ∧
    (signingView key f message signature).1 = target.1 ∧ (signingView key f message signature).2 tree = target.2 tree

theorem cache_trace (f : QueryImpl HashSpec Id) (boundary : SigningBoundaryTrace) (trace : Trace) (input : HashInput)
    (h : (input, f input) ∈ trace.toList) : transcriptCache f boundary trace input = some (f input) := by
  apply if_pos
  exact List.mem_append_right _ h

theorem cache_signing {key : SecretKey} {f : QueryImpl HashSpec Id} {message : Message} {signature : Signature}
    {boundary : SigningBoundaryTrace} (h : ReferenceSigningWitness.SignatureOrigin key f message signature boundary) (trace : Trace) :
    transcriptCache f boundary trace (signingInput key message signature) = some (f (signingInput key message signature)) := by
  apply if_pos
  exact List.mem_append_left _ h.1

theorem covered_witness (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec)
    (boundary : SigningBoundaryTrace) (trace : Trace) (forgery : Forgery)
    (horigin : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      ReferenceSigningWitness.SignatureOrigin key f message signature boundary)
    (hnew : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      messageDigestPayload key.root message signature.randomness ≠ messageDigestPayload key.root forgery.message forgery.signature.randomness)
    (target : FewTimeView) (tree : FtsTree) (hcovered : CoveredByLog key f log target tree) :
    ∃ slot view, fixedSigningViews key.parameter (transcriptCache f boundary trace) key.root log
      (signingInput key forgery.message forgery.signature) slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree := by
  obtain ⟨message, signature, hentry, hi, hl⟩ := hcovered
  obtain ⟨slot, hslot⟩ := List.mem_iff_get.mp hentry
  refine ⟨slot, signingView key f message signature, ?_, hi, hl⟩
  change eligibleSigningView? _ _ _ (log.get slot) = _
  rw [hslot]
  simp only [eligibleSigningView?, signingInput, payloadOf_tweakableHashInput, Option.bind_eq_bind', Option.bind_some,
    if_neg (hnew message signature hentry), observedSigningView?, FtsProbeSimulation.messageAnswers]
  change (transcriptCache f boundary trace (signingInput key message signature) >>= fun answer => pure (hashOutputFewTimeView answer)) = _
  rw [cache_signing (horigin message signature hentry)]
  rfl

theorem certificate_of_covered (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec)
    (boundary : SigningBoundaryTrace) (trace : Trace) (forgery : Forgery) (required : Finset FtsTree)
    (horigin : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      ReferenceSigningWitness.SignatureOrigin key f message signature boundary)
    (hnew : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      messageDigestPayload key.root message signature.randomness ≠ messageDigestPayload key.root forgery.message forgery.signature.randomness)
    (hrun : ContainsRun f trace (messageDigest key.parameter key.root forgery.message forgery.signature.randomness))
    (hadmissible : Admissible (truncateMessageDigest (f (signingInput key forgery.message forgery.signature))))
    (hcovered : ∀ tree ∈ required, CoveredByLog key f log (signingView key f forgery.message forgery.signature) tree) :
    TargetCertificateAt key required (transcriptCache f boundary trace, log) (signingInput key forgery.message forgery.signature) := by
  have hrow : (signingInput key forgery.message forgery.signature, f (signingInput key forgery.message forgery.signature)) ∈ trace.toList := by
    apply hrun
    change signingInput key forgery.message forgery.signature ∈ [signingInput key forgery.message forgery.signature]
    exact List.mem_singleton_self _
  refine ⟨f (signingInput key forgery.message forgery.signature), cache_trace f boundary trace _ hrow, ?_, hadmissible, ?_⟩
  · exact ⟨messageDigestPayload key.root forgery.message forgery.signature.randomness, rfl⟩
  · intro tree ht
    exact (targetTreeMatchCount_pos_iff _ _ tree).mpr
      (covered_witness key f log boundary trace forgery horigin hnew _ tree (hcovered tree ht))

def NearGuess (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec)
    (boundary : SigningBoundaryTrace) (trace : Trace) (forgery : Forgery) : Prop :=
  let target := signingView key f forgery.message forgery.signature
  ∃ omitted : FtsTree,
    TargetCertificateAt key (Finset.univ.erase omitted) (transcriptCache f boundary trace, log) (signingInput key forgery.message forgery.signature) ∧
    ¬CoveredByLog key f log target omitted ∧ FtsVerifierWitness.TrueSecretQuery f key target.1 omitted (target.2 omitted) trace

def TwoGuesses (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec) (trace : Trace) (forgery : Forgery) : Prop :=
  let target := signingView key f forgery.message forgery.signature
  ∃ first second : FtsTree, first ≠ second ∧
    ¬CoveredByLog key f log target first ∧ FtsVerifierWitness.TrueSecretQuery f key target.1 first (target.2 first) trace ∧
    ¬CoveredByLog key f log target second ∧ FtsVerifierWitness.TrueSecretQuery f key target.1 second (target.2 second) trace

def Outcome (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec)
    (boundary : SigningBoundaryTrace) (trace : Trace) (forgery : Forgery) : Prop :=
  TargetCertificateAt key Finset.univ (transcriptCache f boundary trace, log) (signingInput key forgery.message forgery.signature) ∨
    NearGuess key f log boundary trace forgery ∨ TwoGuesses key f log trace forgery

theorem classification (key : SecretKey) (f : QueryImpl HashSpec Id) (log : QueryLog SigningSpec)
    (boundary : SigningBoundaryTrace) (trace : Trace) (forgery : Forgery)
    (horigin : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      ReferenceSigningWitness.SignatureOrigin key f message signature boundary)
    (hnew : ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ log →
      messageDigestPayload key.root message signature.randomness ≠ messageDigestPayload key.root forgery.message forgery.signature.randomness)
    (hrun : ContainsRun f trace (messageDigest key.parameter key.root forgery.message forgery.signature.randomness))
    (hadmissible : Admissible (truncateMessageDigest (f (signingInput key forgery.message forgery.signature))))
    (hqueries : let target := signingView key f forgery.message forgery.signature
      ∀ tree, FtsVerifierWitness.TrueSecretQuery f key target.1 tree (target.2 tree) trace) : Outcome key f log boundary trace forgery := by
  by_cases hall : ∀ tree, CoveredByLog key f log (signingView key f forgery.message forgery.signature) tree
  · exact Or.inl (certificate_of_covered key f log boundary trace forgery Finset.univ horigin hnew hrun hadmissible (fun tree _ => hall tree))
  · push Not at hall
    obtain ⟨first, hfirst⟩ := hall
    by_cases hrest : ∀ tree, tree ≠ first → CoveredByLog key f log (signingView key f forgery.message forgery.signature) tree
    · refine Or.inr (Or.inl ⟨first, ?_, hfirst, hqueries first⟩)
      exact certificate_of_covered key f log boundary trace forgery (Finset.univ.erase first) horigin hnew hrun hadmissible
        (fun tree ht => hrest tree (Finset.mem_erase.mp ht).1)
    · push Not at hrest
      obtain ⟨second, hne, hsecond⟩ := hrest
      exact Or.inr (Or.inr ⟨first, second, hne.symm, hfirst, hqueries first, hsecond, hqueries second⟩)

end SphincsSecurity.Concrete.ReferenceFtsCoverage
