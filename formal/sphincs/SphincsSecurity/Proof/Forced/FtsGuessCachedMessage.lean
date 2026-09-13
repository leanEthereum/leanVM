import SphincsSecurity.Proof.Forced.FtsGuessSeedCache
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open FtsProbeSimulation (MessageHashInput)
open ResidualByteFrontend (MessageOnly)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs publicDigestLoop

theorem cached_residualWorld_query (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (rows : CanonicalEncodingRows)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (hinput : ∀ hash, input = .inr hash → hash ∈ inputs ∧ MessageHashInput parameter hash) :
    cachedSeedRun inputs (simulateQ (seedLift inputs) (residualWorld parameter inputs hencoding known rows input)) cache =
      𝒟[(romImpl input).run cache] := by
  cases input with
  | inl input =>
      simp [residualWorld, seedLift, cachedSeedRun, cachedSeedImpl, forcedSeedAuxiliary,
        romImpl, unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl, StateT.run_monadLift]
  | inr input =>
      obtain ⟨hin, hm⟩ := hinput input rfl
      rw [residualWorld_message parameter inputs hencoding known rows ⟨input, hin⟩ hm,
        simulateQ_spec_query, seedLift, cachedSeedRun, simulateQ_spec_query]
      rfl

theorem cached_residualWorld_run {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (rows : CanonicalEncodingRows)
    (computation : OracleComp OracleWorld Result) (cache : QueryCache HashSpec)
    (hmessage : MessageOnly parameter computation) (hinputs : hashInputs computation ⊆ inputs) :
    cachedSeedRun inputs (simulateQ (seedLift inputs)
      (simulateQ (residualWorld parameter inputs hencoding known rows) computation)) cache =
      𝒟[(simulateQ romImpl computation).run cache] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, cachedSeedRun, simulateQ_pure, StateT.run_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, cachedSeedRun, StateT.run_bind, evalDist_bind]
      change (cachedSeedRun inputs (simulateQ (seedLift inputs)
        (residualWorld parameter inputs hencoding known rows input)) cache >>= fun result =>
          cachedSeedRun inputs (simulateQ (seedLift inputs)
            (simulateQ (residualWorld parameter inputs hencoding known rows) (next result.1))) result.2) = _
      rw [cached_residualWorld_query parameter inputs hencoding known rows input cache (by
        intro hash heq
        subst input
        have hi := mem_hashInputs_hash_bind hash next
        exact ⟨hinputs hi, hmessage hash hi⟩)]
      apply congrArg (𝒟[(romImpl input).run cache] >>= ·)
      funext result
      exact ih result.1 result.2
        (fun hash hh => hmessage hash ((hashInputs_next_subset input next result.1) hh))
        ((hashInputs_next_subset input next result.1).trans hinputs)

theorem publicRecordProgram_eq_work {TargetIndex : Type} {targetSpec : OracleSpec TargetIndex}
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl OracleWorld (OracleComp targetSpec))
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    publicRecordProgram parameter root outside known words selections message =
      simulateQ outside (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root known words selections message) := by
  rw [publicRecordProgram, ResidualByteFrontend.publicSigningWork, map_bind, simulateQ_bind]
  change (simulateQ outside (boundaryComputation parameter (publicDigestLoop parameter root message digestAttemptLimit)) >>= _) = _
  apply congrArg (simulateQ outside (boundaryComputation parameter (publicDigestLoop parameter root message digestAttemptLimit)) >>= ·)
  funext selected
  cases selected.1 <;> rfl

theorem cached_reference_signing_record (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords)
    (message : Message) (cache : QueryCache HashSpec)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    cachedSeedRun inputs (simulateQ (seedLift inputs)
      (referenceProgram parameter root otsSecret labels inputs hencoding selections rows dummy (.inr message))) cache =
      𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root (known otsSecret labels)
        (referenceFamilyWords selections dummy) selections message)).run cache] := by
  rw [referenceProgram, publicRecordProgram_eq_work]
  apply cached_residualWorld_run
  · exact ResidualByteFrontend.messageOnly_map parameter Prod.fst _
      (ResidualByteFrontend.publicSigningWork_messageOnly parameter root _ _ selections message)
  · rwa [ResidualByteFrontend.hashInputs_map, ResidualByteFrontend.hashInputs_publicSigningWork]

end SphincsSecurity.Concrete.FtsGuessHash
