import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphGame
import SphincsSecurity.Proof.Reference.CausalFrontierGame
import SphincsSecurity.Proof.Ots.ReferenceFamilyConditioning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false

def fixedReferenceDummyWord : Encoding :=
  fun index => if index.val < 27 then ⟨7, by decide⟩ else if index.val = 27 then ⟨2, by decide⟩ else ⟨0, by decide⟩

theorem fixedReferenceDummyWord_valid : TargetSum.Valid fixedReferenceDummyWord := by
  change (∑ index : Fin 42, if index.val < 27 then (7 : Nat) else if index.val = 27 then 2 else 0) = 191
  norm_num [Fin.sum_univ_succ]

def fixedReferenceDummy : OtsReferenceWords := fun _ _ _ => fixedReferenceDummyWord

def referenceFamilyWords (selections : ReferenceFamily) (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf => ((selections ⟨lay, tree, leaf⟩).map Prod.snd).getD (dummy lay tree leaf)

theorem referenceFamilyWords_selected (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) :
    referenceFamilyWords (referenceTableSelection key f) dummy = canonicalReferenceWords key f dummy := by
  funext lay tree leaf
  rw [referenceFamilyWords, canonicalReferenceWords,
    ← referenceSelectionResult_eq_search key f ⟨lay, tree, leaf⟩]
  simp only [referenceSelectionResult, Option.map_map, Function.comp_def]

theorem referenceFamilyOracleSample_words (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords) :
    referenceFamilyWords result.1 dummy = canonicalReferenceWords key (finiteHashAnswer ∅ inputs result.2) dummy := by
  rw [referenceFamilyOracleSample_selections key inputs hencoding hgraph result hresult, referenceFamilyWords_selected]

theorem referenceFamilyOracleSample_words_valid (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) :
    ∀ lay tree leaf, TargetSum.Valid (referenceFamilyWords result.1 dummy lay tree leaf) := by
  rw [referenceFamilyOracleSample_words key inputs hencoding hgraph result hresult dummy]
  exact canonicalReferenceWords_valid key (finiteHashAnswer ∅ inputs result.2) dummy hdummy

noncomputable def referenceFamilyFrontierRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  causalFrontierGame key.parameter f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) adversary

theorem referenceFamilyFrontierRest_selected (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceFamilyFrontierRest key f labels (referenceTableSelection key f) dummy adversary =
      graphFrontierGameRest key.parameter key.otsSecret key.ftsSecret labels f dummy adversary := by
  rw [referenceFamilyFrontierRest, referenceFamilyWords_selected, causalFrontierGame_eq, graphFrontierGameRest]
  rfl

noncomputable def referenceFamilyGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒟[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[referenceFamilyFrontierRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (reference.1, result)

theorem referenceFamilyGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary = 𝒟[frontierOracleGame inputs dummy adversary] := by
  rw [referenceFamilyGame, frontierOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame, map_bind, map_pure, bind_pure]
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalDist_bind_comm, evalDist_bind]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  rw [referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) (hgraph parameter) (fun selections table =>
      referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary)]
  simp only [referenceFamilyFrontierRest_selected]

theorem evalDist_boundaryGameCore_referenceFamily (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (referenceFamilyGame_erased inputs hencoding hgraph dummy adversary).symm

theorem forgeAdvantage_eq_referenceFamily (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true |
        referenceFamilyGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage, probOutput_def,
    evalDist_gameCore_frontier (canonicalGraphGameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary), evalDist_map,
    ← referenceFamilyGame_erased (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary,
    ← LawfulFunctor.comp_map]
  change Pr[= true | (Prod.fst ∘ Prod.snd) <$>
    referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _
  rw [probOutput_map]
  rfl

theorem referenceFamilyGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result.2
  apply (mem_support_iff_of_evalDist_eq
    (mx' := Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    (evalDist_boundaryGameCore_referenceFamily (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)) result.2).mpr
  rw [support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete
