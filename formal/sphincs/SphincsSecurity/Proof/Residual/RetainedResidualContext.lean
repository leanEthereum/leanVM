import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualHistory
import SphincsSecurity.Proof.Residual.RetainedResidualTraceValidity
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

structure Context (inputs : Finset HashInput) where
  key : SecretKey
  graph : CanonicalGraphLabels
  auxiliary : ReferenceAuxiliary inputs
  encoding : canonicalEncodingInputs key.parameter ⊆ inputs
  auxiliary_valid : auxiliary ∈ (referenceAuxiliarySample inputs).support
  dummy : OtsReferenceWords
  publicReplies : CanonicalGraphLabels

def Context.words {inputs : Finset HashInput} (context : Context inputs) : OtsReferenceWords :=
  referenceFamilyWords context.auxiliary.selections context.dummy

def Context.actual {inputs : Finset HashInput} (context : Context inputs) : Labels :=
  CanonicalCoordinate.value context.key.otsSecret context.key.ftsSecret context.graph

noncomputable def Context.oracle {inputs : Finset HashInput} (context : Context inputs) : QueryImpl HashSpec Id :=
  programmedHash context.key.parameter context.key.otsSecret context.key.ftsSecret context.graph
    (finiteHashAnswer ∅ inputs (canonicalPrefixResidual context.key.parameter inputs context.encoding context.graph
      context.auxiliary.selections context.auxiliary.rows context.auxiliary.seed))

noncomputable def Context.environment {inputs : Finset HashInput} (context : Context inputs) :=
  RetainedResidual.environment context.key.parameter inputs context.encoding context.words context.publicReplies context.auxiliary.selections context.auxiliary.rows

def Context.EncodingMatch {inputs : Finset HashInput} (context : Context inputs) : HashInput → HashOutput → Prop :=
  PublicEncodingMatch.Match context.key.parameter (canonicalGraphMessage context.graph) context.words context.auxiliary.selections

structure Compatible {inputs : Finset HashInput} (context : Context inputs) (memory : Memory) : Prop where
  agrees : PublicAgreement context.words memory.routing.disclosed memory.routing.known context.actual
  replies : ∀ position, ¬CanonicalCoordinate.Hidden context.words memory.routing.disclosed (.graph position) → context.publicReplies position = context.graph position
  cached : ResidualByteFrontend.CacheMatches context.oracle memory.external.cache
  structural : CacheClean context.key.parameter context.words memory.routing.disclosed context.actual memory.external.cache
  encoding : ResidualByteFrontend.ReplyClean context.EncodingMatch memory.external.cache

theorem afterReply_history (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    (memory.afterReply parameter input answer external).history = memory.history := by
  cases answer with
  | none => rfl
  | some answer => exact observeMessage_history parameter _ _ _

theorem fixedHashStep_routing (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    (fixedHashStep parameter words selections routing actual oracle input memory).2.routing = memory.routing :=
  congrArg Prod.fst (afterReply_history parameter memory input _ _)

theorem Context.encodingMatch_known {inputs : Finset HashInput} (context : Context inputs) (memory : Memory) (hcompatible : Compatible context memory) :
    PublicEncodingMatch.Match context.key.parameter (knownEncodingMessage memory.routing.known) context.words context.auxiliary.selections = context.EncodingMatch :=
  PublicEncodingMatch.known_eq_original context.key.parameter context.words memory.routing.disclosed memory.routing.known
    context.key.otsSecret context.key.ftsSecret context.graph hcompatible.agrees context.auxiliary.selections

theorem fixedHashStep_compatible {inputs : Finset HashInput} (context : Context inputs) (input : HashInput)
    (memory : Memory) (hcompatible : Compatible context memory) (answer : HashOutput)
    (hanswer : (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).1 = some answer) :
    Compatible context (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory).2 := by
  have hrouting := fixedHashStep_routing context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory
  have hstep := ResidualByteFrontend.fixedStep_preserves context.key.parameter context.words memory.routing.disclosed memory.routing.known
    context.actual context.oracle input memory.external hcompatible.cached hcompatible.structural
  rw [← fixedHashStep_external context.key.parameter context.words context.auxiliary.selections memory.routing context.actual context.oracle input memory] at hstep
  refine ⟨?_, ?_, hstep.1, ?_, ?_⟩
  · rw [hrouting]; exact hcompatible.agrees
  · rw [hrouting]; exact hcompatible.replies
  · rw [hrouting]; exact hstep.2.1
  · have hclean := hcompatible.encoding
    rw [← context.encodingMatch_known memory hcompatible] at hclean ⊢
    have h := ResidualByteFrontend.checkedFixedStep_replyClean context.key.parameter context.words memory.routing.disclosed memory.routing.known
      context.actual _ context.oracle input memory.external hclean answer hanswer
    simpa only [fixedHashStep, afterReply_external, ResidualByteFrontend.checkedResult] using h

theorem Compatible.afterSigning {inputs : Finset HashInput} (context : Context inputs) (memory : Memory)
    (hcompatible : Compatible context memory) (message : Message) (record : SigningRecord)
    (htrace : TraceValid context.key.parameter context.oracle record.2)
    (hcompletion : ∃ planned : PublicSigningRecord,
      completePublicSigningRecord (fun index tree leaf => context.actual (.ftsStart index tree leaf)) planned = record) :
    Compatible context ((memory.applyBoundary record.2).recordSigning message record) := by
  have hagrees : PublicAgreement context.words (memory.routing.afterSigning record).disclosed
      (memory.routing.afterSigning record).known context.actual := by
    obtain ⟨planned, rfl⟩ := hcompletion
    exact memory.routing.afterSigning_completed_agreement context.words context.actual hcompatible.agrees planned
  refine ⟨hagrees, ?_, ?_, ?_, ?_⟩
  · intro position hpublic
    apply hcompatible.replies position
    rw [InterleavedResidual.hidden_graph_disclosed context.words memory.routing.disclosed (memory.routing.afterSigning record).disclosed position]
    exact hpublic
  · exact applyBoundary_cacheMatches context.key.parameter context.oracle memory record.2 htrace hcompatible.cached
  · exact memory.routing.afterSigning_cacheClean record context.key.parameter context.words context.actual _
      (applyBoundary_cacheClean context.key.parameter context.oracle context.words memory.routing.disclosed context.actual memory record.2 htrace hcompatible.structural)
  · exact applyBoundary_encodingClean context.key.parameter context.oracle context.words (canonicalGraphMessage context.graph)
      context.auxiliary.selections memory record.2 htrace hcompatible.encoding

theorem originalSigning_compatible {inputs : Finset HashInput} (context : Context inputs) (memory : Memory)
    (hcompatible : Compatible context memory) (message : Message) (record : SigningRecord)
    (hrecord : 𝒟[fixedBoundaryRun context.key.parameter context.oracle (signWithView context.key message)] record ≠ 0) :
    Compatible context ((memory.applyBoundary record.2).recordSigning message record) := by
  apply Compatible.afterSigning context memory hcompatible message record
    (fixedBoundaryRun_traceValid context.key.parameter context.oracle _ record hrecord)
  have h := fixedBoundaryRun_signWithView_prefix_public context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid
    context.dummy memory.routing.disclosed memory.routing.known hcompatible.agrees message
  have h := congrArg evalDist h
  change 𝒟[fixedBoundaryRun context.key.parameter context.oracle (signWithView context.key message)] = _ at h
  rw [h, evalDist_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hrecord
  obtain ⟨planned, _, hrecord⟩ := hrecord
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hrecord
  exact ⟨planned, hrecord.symm⟩

end SphincsSecurity.Concrete.RetainedResidual
