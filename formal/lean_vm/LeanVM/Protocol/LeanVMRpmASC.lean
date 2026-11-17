/-
  LeanVM.Protocol.LeanVMRpmASC

  Knowledge soundness in the random-permutation model for the computable agreement-set extractor.
-/

module

public import LeanVM.Protocol.LeanVMRpmAS
public import LeanVM.Protocol.EndToEnd.Sound.ExtractorC
public import LeanVM.Protocol.EndToEnd.Sound.SkelExtract

@[expose] public section

/-!
# The computable agreement-set extractor

`transcriptExtractorASC`: on the transcript's Keccak-256 evaluations (their messages as the keys)
and its first forward answers, the computed extractor (`Sound.extractASC`: the descent over values,
Gao's decoder, the inverse transform). It is the agreement-set extractor over Gao's decoder
(`transcriptExtractorASC_eq`), so the end statement holds for it (`knowledgeSoundnessASC_holds`),
for any decoder over values (`ValsDecoder`).
`transcriptExtractorASF` replays the verifier's skeleton instead of the verifier, and returns
whatever the computed extractor returns, so the end statement holds for it too
(`knowledgeSoundnessASF_holds`).
-/

namespace LeanVM

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Whir.Sound

variable {D : NearDecoder} (W : ValsDecoder D)

/-- **The computable agreement-set extractor on a transcript of permutation queries.** -/
def transcriptExtractorASCWithHash (prog : Semantics.LeanIsaProgram) (input : PublicInput)
    (T : PermutationTranscript) (proof : Compile.Proof) : Option (Execution prog) :=
  let paths := keccakEvaluationsOfTranscript T
  EndToEnd.Sound.extractASC W prog input (lookupEvaluation paths) (paths.map (·.1))
    (Rpm.firstForward T) proof

/-- **The computable agreement-set extractor in the random-permutation model**, on the
adversary's transcript, its coins left out. -/
def transcriptExtractorASC : StraightLineExtractor :=
  fun prog input T proof ↦ transcriptExtractorASCWithHash W prog input (permutationQueries T) proof

/-- It is the agreement-set extractor over the decoder. -/
theorem transcriptExtractorASC_eq : transcriptExtractorASC W = transcriptExtractorAS D := by
  funext prog input T proof
  exact EndToEnd.Sound.extractASC_eq W _ _ _ _ _ _

/-- **Knowledge soundness holds for the computable agreement-set extractor**, with the end
statement's bound. -/
theorem knowledgeSoundnessASC_holds : KnowledgeSoundness (transcriptExtractorASC W) := by
  rw [transcriptExtractorASC_eq]
  exact knowledgeSoundnessAS_holds D

/-- An extractor that returns whatever one knowledge-sound extractor returns is knowledge sound. -/
theorem KnowledgeSoundness.of_imp {E₁ E₂ : StraightLineExtractor}
    (h : ∀ prog input T proof t, E₁ prog input T proof = some t → E₂ prog input T proof = some t)
    (h₁ : KnowledgeSoundness E₁) : KnowledgeSoundness E₂ := fun A Q hQ hcap ↦
  (prEvent_mono _ _ _ fun _ ho ↦ ⟨ho.1, fun ⟨t, ht, hv⟩ ↦ ho.2 ⟨t, h _ _ _ _ _ ht, hv⟩⟩).trans
    (h₁ A Q hQ hcap)

/-- **The agreement-set extractor over the verifier's skeleton**, on the adversary's transcript. -/
def transcriptExtractorASF : StraightLineExtractor :=
  fun prog input T proof ↦
    let paths := keccakEvaluationsOfTranscript (permutationQueries T)
    EndToEnd.Sound.extractASF W prog input (lookupEvaluation paths) (paths.map (·.1))
      (Rpm.firstForward (permutationQueries T)) proof

/-- **Knowledge soundness holds for the extractor over the skeleton**, with the end statement's
bound. -/
theorem knowledgeSoundnessASF_holds : KnowledgeSoundness (transcriptExtractorASF W) :=
  KnowledgeSoundness.of_imp (fun _ _ _ _ _ h ↦ EndToEnd.Sound.extractASF_of_extractASC W h)
    (knowledgeSoundnessASC_holds W)

end LeanVM

end
