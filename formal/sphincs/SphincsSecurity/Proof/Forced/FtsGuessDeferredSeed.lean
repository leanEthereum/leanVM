import SphincsSecurity.Proof.Forced.FtsGuessAuxiliaryProgram
import SphincsSecurity.Proof.Forced.SecretGuessForcedProgram
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State initialState forcedRun forcedProgram)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

abbrev SecretSamplingSpec := (SPMF Bool →ₒ Bool) + (SPMF Digest →ₒ Digest)
abbrev ForcedSeedAuxiliary := unifSpec + SecretSamplingSpec
abbrev ForcedSeedSpec (inputs : Finset HashInput) := ForcedSeedAuxiliary + (inputs →ₒ HashOutput)

noncomputable def forcedSeedAuxiliary : QueryImpl ForcedSeedAuxiliary SPMF
  | .inl input => 𝒟[(liftM (unifSpec.query input) : ProbComp _)]
  | .inr (.inl law) => law
  | .inr (.inr law) => law

noncomputable def seedLift (inputs : Finset HashInput) : QueryImpl (SeedSpec inputs) (OracleComp (ForcedSeedSpec inputs))
  | .inl input => liftM ((ForcedSeedSpec inputs).query (.inl (.inl input)))
  | .inr input => liftM ((ForcedSeedSpec inputs).query (.inr input))

noncomputable def sampleForcedBool (inputs : Finset HashInput) (law : SPMF Bool) : OracleComp (ForcedSeedSpec inputs) Bool :=
  liftM ((ForcedSeedSpec inputs).query (.inl (.inr (.inl law))))

noncomputable def sampleForcedDigest (inputs : Finset HashInput) (law : SPMF Digest) : OracleComp (ForcedSeedSpec inputs) Digest :=
  liftM ((ForcedSeedSpec inputs).query (.inl (.inr (.inr law))))

theorem seedLift_fixed {Result : Type} (inputs : Finset HashInput) (seed : inputs → HashOutput)
    (computation : OracleComp (SeedSpec inputs) Result) :
    simulateQ (UniformTableObservation.fixedImpl forcedSeedAuxiliary seed) (simulateQ (seedLift inputs) computation) =
      𝒟[simulateQ (seedAnswers inputs seed) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalDist_bind]
      cases input <;> simp only [seedLift, seedAnswers, simulateQ_spec_query, UniformTableObservation.fixedImpl,
        forcedSeedAuxiliary, evalDist_pure, pure_bind, ih]

noncomputable def forcedSeedProgram (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords)
    (slot : Nat) (adversary : Adversary) : OracleComp (ForcedSeedSpec inputs) (Completed × State Coordinate Digest PUnit) :=
  forcedProgram (fun input => simulateQ (seedLift inputs)
    (referenceProgram parameter root otsSecret labels inputs hencoding selections rows dummy input))
    (sampleForcedBool inputs) (sampleForcedDigest inputs) slot
    (completedRun parameter root labels adversary) (initialState PUnit.unit)

theorem forcedSeedProgram_fixed (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput)
    (dummy : OtsReferenceWords) (slot : Nat) (adversary : Adversary) :
    simulateQ (UniformTableObservation.fixedImpl forcedSeedAuxiliary seed)
      (forcedSeedProgram parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary) =
        forcedRun (SecretGuessObservation.environment
          (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) slot
          (completedRun parameter root labels adversary) (initialState PUnit.unit) := by
  apply SecretGuessObservation.simulateQ_forcedProgram
  · intro input
    rw [seedLift_fixed, referenceProgram_fixed]
  · intro law
    simp only [sampleForcedBool, simulateQ_spec_query, UniformTableObservation.fixedImpl, forcedSeedAuxiliary]
  · intro law
    simp only [sampleForcedDigest, simulateQ_spec_query, UniformTableObservation.fixedImpl, forcedSeedAuxiliary]

noncomputable def deferredForcedRun (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords)
    (slot : Nat) (adversary : Adversary) : SPMF ((Completed × State Coordinate Digest PUnit) × (inputs → Finset HashOutput)) :=
  UniformTableObservation.lazyRun forcedSeedAuxiliary
    (forcedSeedProgram parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary)
    (fun _ => Finset.univ)

theorem forcedRun_seed_marginal (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords)
    (slot : Nat) (adversary : Adversary) :
    (𝒟[PMF.uniformOfFintype (inputs → HashOutput)] >>= fun seed =>
      forcedRun (SecretGuessObservation.environment
        (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) slot
        (completedRun parameter root labels adversary) (initialState PUnit.unit)) =
      Prod.fst <$> deferredForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary := by
  have h := UniformTableObservation.run_marginal forcedSeedAuxiliary
    (forcedSeedProgram parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary)
    (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty)
  rw [complete_of_nonempty _ (fun _ => Finset.univ_nonempty), uniformTable_univ] at h
  simpa only [forcedSeedProgram_fixed, deferredForcedRun] using h

end SphincsSecurity.Concrete.FtsGuessHash
