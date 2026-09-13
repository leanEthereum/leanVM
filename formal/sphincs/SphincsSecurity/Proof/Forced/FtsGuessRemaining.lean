import SphincsSecurity.Proof.Forced.FtsGuessPairSource
import SphincsSecurity.Proof.Reference.ReferenceCertificateCoverage
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open RetainedResidual (signingInput)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

noncomputable def ReferenceForgerySample.nearGuess {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  let key := ReferenceVerifierWitness.rootedKey sample.1 f
  let result := (sample.context dummy).2.2.2
  SigningTranscript.Valid sample.2.2.1.1.2 ∧
    ReferenceFtsCoverage.NearGuess key f sample.2.2.1.1.2 sample.2.2.1.2
      (result.before * result.after) sample.2.2.1.1.1

theorem ReferenceForgerySample.remainingFts_cases {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) (h : sample.remainingFts dummy) :
    FtsGuessHash.referenceTwoGuesses dummy sample ∨ sample.nearGuess dummy := by
  rcases h with ⟨hvalid, h | h⟩
  · exact Or.inr ⟨hvalid, h⟩
  · exact Or.inl h

theorem referenceForgeryGame_remainingFts_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) :
    Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      FtsGuessHash.pairRate budget +
      Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  refine (_root_.probEvent_mono'' (mx := referenceForgeryGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    (fun sample h => sample.remainingFts_cases dummy h)).trans ?_
  exact (probEvent_or_le _ _ _).trans
    (add_le_add (FtsGuessHash.referenceForgeryGame_two_guesses dummy adversary budget hbudget) le_rfl)

theorem forgeAdvantage_le_nearGuess_small_budget (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf))
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    forgeAdvantage scheme adversary ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ + FtsGuessHash.pairRate q +
      Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  have h := (forgeAdvantage_le_remainingFts_small_budget dummy hdummy adversary q hbound hsmall).trans
    (add_le_add le_rfl (referenceForgeryGame_remainingFts_le dummy adversary q hbound))
  simpa only [add_assoc] using h

theorem forgeAdvantage_le_nearGuess_normalized_small_budget (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf))
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    forgeAdvantage scheme adversary ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ + ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
      Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] :=
  (forgeAdvantage_le_nearGuess_small_budget dummy hdummy adversary q hbound hsmall).trans
    (add_le_add (add_le_add le_rfl (FtsGuessHash.pairRate_le_normalized q)) le_rfl)

end SphincsSecurity.Concrete
