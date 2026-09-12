import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCompletion
import SphincsSecurity.Proof.Residual.RetainedResidualProgram
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def finishWork (actual : Labels) (result : Option (PublicSigningRecord × Nat) × Memory) : Option SigningRecord × Memory :=
  result.1.elim (none, result.2) (fun work =>
    (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) work.1), result.2.accountWork work.2))

theorem observedRun_externalProgram_original_memory {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (graph : CanonicalGraphLabels)
    (seed : inputs → HashOutput) (computation : OracleComp OracleWorld Result)
    (hinputs : hashInputs computation ⊆ inputs) (state : State inputs)
    (hagrees : PublicAgreement words state.memory.routing.disclosed state.memory.routing.known
      (CanonicalCoordinate.value otsSecret ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words state.memory.routing.disclosed (.graph position) → publicReplies position = graph position)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches (programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))) state.memory.external.cache)
    (hclean : CacheClean parameter words state.memory.routing.disclosed (CanonicalCoordinate.value otsSecret ftsSecret graph) state.memory.external.cache) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret graph
    let oracle := programmedHash parameter otsSecret ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding graph selections rows seed))
    forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (externalProgram inputs parameter words selections computation) state =
      fixedByteRun parameter words selections state.memory.routing actual oracle computation state.memory := by
  dsimp only
  rw [externalProgram, observedRun_routing_bind]
  exact byteRun_eq_fixed parameter inputs hencoding words publicReplies selections rows state.memory.routing
    (CanonicalCoordinate.value otsSecret ftsSecret graph) seed _
    (fun input => ResidualByteAction.freshPrefix_eq_original parameter inputs hencoding words state.memory.routing.disclosed state.memory.routing.known
      otsSecret ftsSecret graph publicReplies hagrees hreplies selections rows seed input)
    computation hinputs state hcovered hmatches hclean

theorem observedRun_jointSigningProgram_memory (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (oracle : QueryImpl HashSpec Id)
    (hfresh : ∀ input : inputs, ResidualByteAction.eval actual seed
      (ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input) =
      ResidualByteFrontend.fixedAnswer parameter words routing.disclosed actual oracle input.val)
    (root : Digest) (message : Message)
    (hinputs : hashInputs (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches oracle state.memory.external.cache)
    (hclean : CacheClean parameter words routing.disclosed actual state.memory.external.cache) :
    forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state =
      (fun record => (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) record),
        state.memory.applyBoundary record.2)) <$> 𝒟[publicSigningRecord parameter root oracle routing.known words selections message] := by
  calc
    _ = finishWork actual <$> (forgetState <$>
        byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed
          (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message) state) := by
      rw [ResidualByteFrontend.jointSigningProgram, simulateQ_bind, observedRun_bind, map_bind]
      simp only [byteRun, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      apply congrArg (_ >>= ·)
      funext result
      rcases result with ⟨work, after⟩
      cases work with
      | none => simp only [Option.elim_none, pure_bind, finishWork, forgetState]
      | some work =>
          change forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
            (simulateQ (embed inputs routing) (ResidualByteFrontend.jointCompleteSigningWork work)) after = _
          rw [observedRun_completeWork_memory]
          rfl
    _ = _ := by
      rw [byteRun_message_trace parameter inputs hencoding words publicReplies selections rows routing actual seed oracle hfresh
        _ hinputs (ResidualByteFrontend.publicSigningWork_messageOnly parameter root routing.known words selections message)
        state hcovered hmatches hclean]
      have h := congrArg (fun computation =>
        (fun result => (some (completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1), result.2)) <$>
          𝒟[computation]) (publicSigningWork_fixed_memory parameter root oracle routing.known words selections message state.memory)
      simpa only [evalDist_map, Functor.map_map, finishWork, Option.elim_some] using h

theorem observedRun_jointSigningProgram_original_memory (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (graph : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (routing : Routing) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) routing.disclosed routing.known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden (referenceFamilyWords auxiliary.selections dummy) routing.disclosed (.graph position) →
      publicReplies position = graph position)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches (programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed)))
      state.memory.external.cache)
    (hclean : CacheClean key.parameter (referenceFamilyWords auxiliary.selections dummy) routing.disclosed
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph) state.memory.external.cache) :
    let words := referenceFamilyWords auxiliary.selections dummy
    let actual := CanonicalCoordinate.value key.otsSecret key.ftsSecret graph
    let oracle := programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed))
    forgetState <$> observedRun (environment key.parameter inputs hencoding words publicReplies auxiliary.selections auxiliary.rows) actual auxiliary.seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root routing.known words auxiliary.selections message)) state =
      (fun record => (some record, state.memory.applyBoundary record.2)) <$>
        𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] := by
  dsimp only
  rw [observedRun_jointSigningProgram_memory key.parameter inputs hencoding _ publicReplies auxiliary.selections auxiliary.rows
    routing (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph) auxiliary.seed _
    (fun input => ResidualByteAction.freshPrefix_eq_original key.parameter inputs hencoding _ routing.disclosed routing.known
      key.otsSecret key.ftsSecret graph publicReplies hagrees hreplies auxiliary.selections auxiliary.rows auxiliary.seed input)
    key.root message ((ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key routing.known _ auxiliary.selections message).trans hinputs)
    state hcovered hmatches hclean]
  have hmessage (randomness : Randomness) := programmedPrefixResidual_outside key.parameter inputs hencoding _ routing.disclosed routing.known
    key.otsSecret key.ftsSecret graph hagrees auxiliary.selections auxiliary.rows auxiliary.seed _
    (decodePosition_message key.parameter (messageDigestPayload key.root message randomness))
  have hpublic := fixedBoundaryRun_publicDigestLoop_eq_of_message key.parameter key.root message _ _ hmessage digestAttemptLimit
  have hrecord := fixedBoundaryRun_signWithView_prefix_public key inputs hencoding graph auxiliary hauxiliary dummy routing.disclosed routing.known hagrees message
  have h := congrArg (fun computation => (fun record => (some record, state.memory.applyBoundary record.2)) <$> 𝒟[computation]) hrecord
  simp only [evalDist_map, Functor.map_map, completePublicSigningRecord_trace] at h
  rw [publicSigningRecord, hpublic]
  exact h.symm

noncomputable def finishSigning (message : Message) (result : Option SigningRecord × Memory) : Option (Option Signature) × Memory :=
  result.1.elim (none, result.2) (fun record => (some record.1.1, result.2.recordSigning message record))

theorem observedRun_signingProgram_full_project (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (actual : Labels) (seed : inputs → HashOutput) (root : Digest) (message : Message) (state : State inputs) :
    forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (signingProgram inputs parameter root words selections message) state =
      finishSigning message <$> (forgetState <$> observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs parameter root state.memory.routing.known words selections message)) state) := by
  rw [observedRun_signingProgram, map_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨record, after⟩
  cases record <;> simp only [Option.elim_none, Option.elim_some, pure_bind, forgetState, finishSigning]

theorem observedRun_signingProgram_original_memory (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (graph : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed state.memory.routing.known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed (.graph position) →
      publicReplies position = graph position)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches (programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed)))
      state.memory.external.cache)
    (hclean : CacheClean key.parameter (referenceFamilyWords auxiliary.selections dummy) state.memory.routing.disclosed
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret graph) state.memory.external.cache) :
    let words := referenceFamilyWords auxiliary.selections dummy
    let actual := CanonicalCoordinate.value key.otsSecret key.ftsSecret graph
    let oracle := programmedHash key.parameter key.otsSecret key.ftsSecret graph
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding graph auxiliary.selections auxiliary.rows auxiliary.seed))
    forgetState <$> observedRun (environment key.parameter inputs hencoding words publicReplies auxiliary.selections auxiliary.rows) actual auxiliary.seed
      (signingProgram inputs key.parameter key.root words auxiliary.selections message) state =
      (fun record => (some record.1.1, (state.memory.applyBoundary record.2).recordSigning message record)) <$>
        𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] := by
  dsimp only
  rw [observedRun_signingProgram_full_project,
    observedRun_jointSigningProgram_original_memory key inputs hencoding graph auxiliary hauxiliary dummy publicReplies
      state.memory.routing message hinputs state hagrees hreplies hcovered hmatches hclean]
  simp only [Functor.map_map, finishSigning, Option.elim_some]

end SphincsSecurity.Concrete.RetainedResidual
