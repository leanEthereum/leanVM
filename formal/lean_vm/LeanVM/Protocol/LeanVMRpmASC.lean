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
and its first forward answers, the computed extractor (`Sound.extractASC`: the descent over values
with a decoder over values, the inverse transform). It is the agreement-set extractor over that
decoder (`transcriptExtractorASC_eq`), for any decoder over values (`ValsDecoder`).
`transcriptExtractorASF` replays the verifier's skeleton instead of the verifier, and returns
whatever the computed extractor returns (`EndToEnd.Sound.extractASF_of_extractASC`).
`LeanVM.knowledgeSoundness_holds` (`Protocol/KnowledgeSoundness.lean`) composes these.
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

/-- **The agreement-set extractor over the verifier's skeleton**, on the adversary's transcript. -/
def transcriptExtractorASF : StraightLineExtractor :=
  fun prog input T proof ↦
    let paths := keccakEvaluationsOfTranscript (permutationQueries T)
    EndToEnd.Sound.extractASF W prog input (lookupEvaluation paths) (paths.map (·.1))
      (Rpm.firstForward (permutationQueries T)) proof

end LeanVM

end
