import SphincsSecurity.Proof.Ots.OtsPrefixSourceGame
import SphincsSecurity.Proof.Ots.OtsPrefixSecretSampling
import SphincsSecurity.Proof.Ots.OtsPrefixObservedRun
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem swap_samples {A B Result : Type} (first : SPMF A) (second : SPMF B)
    (next : A → B → SPMF Result) :
    (do let a ← first; let b ← second; next a b) = (do let b ← second; let a ← first; next a b) := by
  apply SPMF.ext
  intro result
  change Pr[= result | first >>= fun a => second >>= fun b => next a b] =
    Pr[= result | second >>= fun b => first >>= fun a => next a b]
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ring

theorem reverse_three_samples {A B C Result : Type} (first : SPMF A) (second : SPMF B) (third : SPMF C)
    (next : A → B → C → SPMF Result) :
    (do let a ← first; let b ← second; let c ← third; next a b c) =
      (do let c ← third; let b ← second; let a ← first; next a b c) := by
  rw [swap_samples first second]
  simp_rw [swap_samples first third]
  rw [swap_samples second third]

noncomputable def prefixObservedSourceGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment : OtsPrefix := ⟨parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
  let other ← 𝒟[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒟[(segment.seedObservedRun inputs (hencoding parameter) (hgraph parameter)
    auxiliary other.val ftsSecret words adversary).map (fun result => result.2.1)]
  pure (selections, result)

theorem prefixObservedSourceGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixObservedSourceGame inputs hencoding hgraph lay tree leaf chainIdx dummy adversary =
      prefixSourceGame inputs hencoding hgraph lay tree leaf chainIdx dummy adversary := by
  symm
  unfold prefixSourceGame prefixSeedRest prefixObservedSourceGame
  dsimp only
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [swap_samples 𝒟[sampleOtsSecrets] 𝒟[sampleFtsSecrets]]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  rw [swap_samples 𝒟[sampleOtsSecrets]
    𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]]
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment : OtsPrefix := ⟨parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
  rw [segment.sampleOtsSecrets_eq_split]
  simp only [bind_assoc, pure_bind, OtsPrefix.seedGame_replaceSecret]
  apply congrArg (𝒟[PMF.uniformOfFintype segment.ErasedSecrets] >>= ·)
  funext other
  rw [reverse_three_samples 𝒟[PMF.uniformOfFintype Digest]
    𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
    𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]]
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections] >>= ·)
  funext auxiliary
  rw [OtsPrefix.seedObservedRun, segment.realRun_empty_forget]
  have hselected (secret : Digest) : segment.replaceChain other.val secret lay tree leaf chainIdx = secret :=
    segment.replaceChain_self other.val secret
  simp only [bind_assoc, hselected]
  dsimp only [segment, words]
  simp only [OtsPrefix.seedGame_replaceSecret]

theorem prefixObservedSourceGame_hashCalls_le (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support
      (prefixObservedSourceGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary)
        (canonicalGraphInputs_subset_gameInputs adversary) lay tree leaf chainIdx dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  rw [prefixObservedSourceGame_eq] at hresult
  exact prefixSourceGame_hashCalls_le lay tree leaf chainIdx dummy adversary q hbound result hresult

end SphincsSecurity.Concrete
