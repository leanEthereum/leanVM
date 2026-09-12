import SphincsSecurity.Proof.Ots.ReferenceFamilyAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

abbrev FrontierObserver (Result : Type) := PublicParameter → OtsReferenceWords → OtsFrontierValues →
  OracleComp OracleWorld (Bool × SigningBoundaryTrace) → OracleComp OracleWorld Result

noncomputable def referenceInstrumentedRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  simulateQ (fixedHashWorld oracle) (observer key.parameter words frontier
    (CausalFrontierProgram.game key.parameter oracle key.ftsSecret words frontier adversary))

abbrev InstrumentedResult (Result : Type) := PublicParameter × ReferenceFamily × Result

noncomputable def referenceInstrumentedGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒟[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let oracle := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[referenceInstrumentedRest observer key oracle
    (canonicalGraphLabels parameter otsSecret ftsSecret oracle) reference.1 dummy adversary]
  pure (parameter, reference.1, result)

theorem referenceInstrumentedRest_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    erase <$> referenceInstrumentedRest observer key oracle labels selections dummy adversary =
      referenceFamilyFrontierRest key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, ← simulateQ_map, herase, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]

theorem referenceInstrumentedGame_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => (result.2.1, erase result.2.2)) <$> referenceInstrumentedGame observer inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceInstrumentedGame referenceFamilyGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceInstrumentedRest_erased observer erase herase, evalDist_map, bind_map_left]

end SphincsSecurity.Concrete
