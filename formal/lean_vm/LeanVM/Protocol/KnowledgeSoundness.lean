/-
  LeanVM.Protocol.KnowledgeSoundness

  The straight-line knowledge extractor and its knowledge soundness, the end statement
  `LeanVM.KnowledgeSoundness` of `Statement/LeanVm.lean`.
-/

module

public import LeanVM.Protocol.Extraction.AS.Lite

/-!
# The knowledge extractor and its knowledge soundness

`transcriptExtractor`: the agreement-set extractor on the lite layout
(`Extraction.AS.transcriptExtractorL`, `Extraction/AS/Lite.lean`) on the adversary's transcript:
it replays the verifier's transcript operations over the transcript's first forward answers,
inverts every committed root's Merkle tree through the transcript's Keccak-256 evaluations, and
descends from the final polynomial to level 0's stack, each fold round decoding the previous
round's word with at most one error on the columns where the current tuple agrees with it; it
runs the one stack it finds. **`knowledgeSoundness_holds`**: it satisfies `KnowledgeSoundness`,
with the end statement's bound.
-/

namespace LeanVM

@[expose] public section

/-- **The knowledge extractor**, in the random-permutation model: the agreement-set extractor on
the adversary's transcript (`Extraction.AS.transcriptExtractorL`). -/
def transcriptExtractor : StraightLineExtractor := Extraction.AS.transcriptExtractorL

/-- **Knowledge soundness holds** (in the random-permutation model), for `transcriptExtractor`. -/
theorem knowledgeSoundness_holds : KnowledgeSoundness transcriptExtractor :=
  Extraction.AS.knowledgeSoundnessL_holds

end

end LeanVM
