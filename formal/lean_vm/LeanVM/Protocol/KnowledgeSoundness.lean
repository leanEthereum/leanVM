/-
  LeanVM.Protocol.KnowledgeSoundness

  The straight-line knowledge extractor and its knowledge soundness, the end statement
  `LeanVM.KnowledgeSoundness` of `Statement/LeanVm.lean`.
-/

module

public import LeanVM.Protocol.Extraction.AS.Lite
public import LeanVM.Protocol.LeanVMRpmASC

/-!
# The knowledge extractor and its knowledge soundness

`transcriptExtractor`: the agreement-set extractor on the lite layout
(`Extraction.AS.transcriptExtractorL`, `Extraction/AS/Lite.lean`) on the adversary's transcript:
it replays the verifier's transcript operations over the transcript's first forward answers,
inverts every committed root's Merkle tree through the transcript's Keccak-256 evaluations, and
descends from the final polynomial to level 0's stack, each fold round decoding the previous
round's word with at most one error on the columns where the current tuple agrees with it; it
runs the one stack it finds. **`knowledgeSoundness_holds`**: it satisfies `KnowledgeSoundness`,
with the end statement's bound: whatever it returns, the agreement-set extractor over Newton's
decoder returns (`extractL_eq`, `extractP_eq`, `extractC_eq`, `extractA_eq`, `extractM_of_ASF`,
`extractASF_of_extractASC`, `transcriptExtractorASC_eq`), which is knowledge sound
(`knowledgeSoundnessAS_holds`).
-/

namespace LeanVM

@[expose] public section

/-- **The knowledge extractor**, in the random-permutation model: the agreement-set extractor on
the adversary's transcript (`Extraction.AS.transcriptExtractorL`). -/
def transcriptExtractor : StraightLineExtractor := Extraction.AS.transcriptExtractorL

/-- An extractor that returns whatever a knowledge-sound extractor returns is knowledge sound. -/
theorem KnowledgeSoundness.of_imp {E₁ E₂ : StraightLineExtractor}
    (h : ∀ prog input T proof t, E₁ prog input T proof = some t → E₂ prog input T proof = some t)
    (h₁ : KnowledgeSoundness E₁) : KnowledgeSoundness E₂ := fun A Q hQ hcap ↦
  (prEvent_mono _ _ _ fun _ ho ↦ ⟨ho.1, fun ⟨t, ht, hv⟩ ↦ ho.2 ⟨t, h _ _ _ _ _ ht, hv⟩⟩).trans
    (h₁ A Q hQ hcap)

/-- **Knowledge soundness holds** (in the random-permutation model), for `transcriptExtractor`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness transcriptExtractor :=
  KnowledgeSoundness.of_imp (fun prog input T π t h ↦ by
    have h1 : transcriptExtractorASC Protocol.Whir.Sound.newtonValsDecoder prog input T π = some t := by
      rw [transcriptExtractorASC_eq]; exact h
    have h2 := Protocol.EndToEnd.Sound.extractASF_of_extractASC Protocol.Whir.Sound.newtonValsDecoder h1
    have h3 := Extraction.AS.extractM_of_ASF Protocol.Whir.Sound.newtonValsDecoder (T := T) h2
    show Extraction.AS.extractL prog input (permutationQueries T) π = some t
    rw [Extraction.AS.extractL_eq, Extraction.AS.extractP_eq, Extraction.AS.extractC_eq,
      Extraction.AS.extractA_eq]
    exact h3) (knowledgeSoundnessAS_holds Protocol.Whir.Sound.newtonNearDecoder)

end

end LeanVM
