module

public import LeanVM.Cost.AS.End

/-!
# The extractor program

`compiledKnowledgeExtractor`, the cost-machine program whose extractor
(`LeanVM.extractorComputedBy`, `Statement/CostMachine.lean`) is the lite agreement-set extractor:
the compiled `extractL` behind its entry (`Cost/AS/Program.lean`).

* **`extractorProgram_size_le`**: its size is within `leanVmKnowledgeExtractorSizeBound`
  (`asProgram_size_le`, `Cost/AS/ProgramSize.lean`);
* **`extractorOf_extractorProgram`**: the extractor it computes is `transcriptExtractorL`
  (`asExtractor_output`): its price is within `asBudget` wherever it extracts (`asPrice_within`),
  which is the statement's budget (`asBudget_le_statement`).
-/

namespace LeanVM.Cost

public section

/-- **The extractor's program**: the compiled agreement-set extractor behind its entry. -/
@[expose] def compiledKnowledgeExtractor : MachineProgram := AS.compiledASExtractor

/-- **The program's size is within `leanVmKnowledgeExtractorSizeBound`.** -/
theorem extractorProgram_size_le :
    compiledKnowledgeExtractor.size ≤ leanVmKnowledgeExtractorSizeBound :=
  AS.asProgram_size_le.trans (by decide)

/-- **The extractor `compiledKnowledgeExtractor` computes is `transcriptExtractorL`.** -/
theorem extractorOf_extractorProgram :
    LeanVM.extractorComputedBy compiledKnowledgeExtractor = LeanVM.Extraction.AS.transcriptExtractorL := by
  funext prog input T proof
  exact AS.asExtractor_output leanVmKnowledgeExtractorSizeBound extractorProgram_size_le
    leanVmKnowledgeExtractorBudget Bounds.AS.asBudget_le_statement prog input T proof

end

end LeanVM.Cost
