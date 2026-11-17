/-
  LeanVM.Protocol.LeanVMRpmASC

  Knowledge soundness in the random-permutation model for the computable agreement-set extractor.
-/

module

public import LeanVM.Protocol.LeanVMRpmAS
public import LeanVM.Protocol.EndToEnd.Sound.ExtractorC

@[expose] public section

/-!
# The computable agreement-set extractor

`transcriptExtractorASC`: on the transcript's Keccak-256 evaluations (their messages as the keys)
and its first forward answers, the computed extractor (`Sound.extractASC`: the descent over values,
Gao's decoder, the inverse transform). It is the agreement-set extractor over Gao's decoder
(`transcriptExtractorASC_eq`), so the end statement holds for it (`knowledgeSoundnessASC_holds`).
-/

namespace LeanVM

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Whir.Sound

/-- **The computable agreement-set extractor on a transcript of permutation queries.** -/
def transcriptExtractorASCWithHash (prog : Semantics.LeanIsaProgram) (input : PublicInput)
    (T : PermutationTranscript) (proof : Compile.Proof) : Option (Execution prog) :=
  let paths := keccakEvaluationsOfTranscript T
  EndToEnd.Sound.extractASC prog input (lookupEvaluation paths) (paths.map (·.1))
    (Rpm.firstForward T) proof

/-- **The computable agreement-set extractor in the random-permutation model**, on the
adversary's transcript, its coins left out. -/
def transcriptExtractorASC : StraightLineExtractor :=
  fun prog input T proof ↦ transcriptExtractorASCWithHash prog input (permutationQueries T) proof

/-- It is the agreement-set extractor over Gao's decoder. -/
theorem transcriptExtractorASC_eq : transcriptExtractorASC = transcriptExtractorAS gaoNearDecoder := by
  funext prog input T proof
  exact EndToEnd.Sound.extractASC_eq _ _ _ _ _ _

/-- **Knowledge soundness holds for the computable agreement-set extractor**, with the end
statement's bound. -/
theorem knowledgeSoundnessASC_holds : KnowledgeSoundness transcriptExtractorASC := by
  rw [transcriptExtractorASC_eq]
  exact knowledgeSoundnessAS_holds gaoNearDecoder

end LeanVM

end
