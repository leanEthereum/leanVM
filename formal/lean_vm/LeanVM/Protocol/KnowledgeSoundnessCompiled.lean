/-
  LeanVM.Protocol.KnowledgeSoundnessCompiled

  leanVM's knowledge soundness for the compiled extractor program.
-/

module

public import LeanVM.Protocol.KnowledgeSoundness
public import LeanVM.Protocol.Relation.Link.GroupLinksEnd
public import LeanVM.Protocol.Extraction.AS.LiteSound
public import LeanVM.Cost.KnowledgeExtractor

/-!
# Knowledge soundness of the compiled extractor

`knowledgeSoundness_compiled`: `LeanVM.KnowledgeSoundness` (`Statement/LeanVm.lean`) for the
extractor `compiledKnowledgeExtractor` computes (`LeanVM.extractorComputedBy`), of size within
`leanVmKnowledgeExtractorSizeBound` (`extractorProgram_size_le`). It is `knowledgeSoundness_of`
at the link's interface (`linkIface`), the compiled program's extractor
(`extractorOf_extractorProgram`) and the lite extractor's agreement with the agreement-set one
(`transcriptExtractorL_of`). This is `Statement.Theorems.leanVmKnowledgeSoundness` at
`leanVmKnowledgeExtractor := compiledKnowledgeExtractor`.
-/

namespace LeanVM

@[expose] public section

/-- **leanVM is knowledge sound for the compiled extractor program.** -/
theorem knowledgeSoundness_compiled :
    KnowledgeSoundness (extractorComputedBy Cost.compiledKnowledgeExtractor) :=
  knowledgeSoundness_of Protocol.Relation.linkIface Cost.extractorOf_extractorProgram
    fun _ _ _ _ _ h ↦ Extraction.AS.transcriptExtractorL_of h

end

end LeanVM
