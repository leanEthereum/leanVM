module

public import LeanVM.Cost.AS.End
public import LeanVM.Protocol.KnowledgeSoundness

/-!
# The extractor program

`compiledKnowledgeExtractor`, the cost-machine program `LeanVM.theorems_hold` names as the end
statement's extractor (`LeanVM.extractorComputedBy`, `Statement/CostMachine.lean`): the compiled
agreement-set extractor behind its entry (`Cost/AS/Program.lean`).

* `extractorProgram_size_le`: its size is within `leanVmKnowledgeExtractorSizeBound`
  (`asProgram_size_le`, `Cost/AS/ProgramSize.lean`);
* the compiled extractor's price is proved within `asBudget` wherever it extracts (`asPrice_within`,
  `Cost/AS/End.lean`), within the statement's budget (`asBudget_le_statement`);
* **`extractorOf_extractorProgram`**: the extractor it computes is `transcriptExtractor`
  (`asExtractor_output`).
-/

namespace LeanVM.Cost

public section

/-- **The extractor's program**: the compiled agreement-set extractor behind its entry. -/
@[expose] def compiledKnowledgeExtractor : MachineProgram := AS.compiledASExtractor

/-- **The program's size is within `leanVmKnowledgeExtractorSizeBound`.** -/
theorem extractorProgram_size_le :
    compiledKnowledgeExtractor.size ≤ leanVmKnowledgeExtractorSizeBound :=
  AS.asProgram_size_le.trans (by decide)

/-- **The extractor `compiledKnowledgeExtractor` computes is `transcriptExtractor`**: its spec and
its price within `asBudget`, within the statement's budget (`asBudget_le_statement`). -/
theorem extractorOf_extractorProgram :
    LeanVM.extractorComputedBy compiledKnowledgeExtractor = transcriptExtractor := by
  funext prog input T proof
  exact AS.asExtractor_output leanVmKnowledgeExtractorSizeBound extractorProgram_size_le
    leanVmKnowledgeExtractorBudget Bounds.AS.asBudget_le_statement prog input T proof
end

end LeanVM.Cost
