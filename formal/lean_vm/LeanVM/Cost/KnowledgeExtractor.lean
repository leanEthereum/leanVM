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
* `leanVmKnowledgeExtractorBudget_eq`: the statement's budget is `asBudget`, which the compiled
  extractor's price is proved within wherever it extracts (`asPrice_within`, `Cost/AS/End.lean`);
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

/-- The statement's budget is the one the price is proved within. -/
theorem leanVmKnowledgeExtractorBudget_eq :
    leanVmKnowledgeExtractorBudget = Bounds.AS.asBudget := rfl

/-- **The extractor `compiledKnowledgeExtractor` computes is `transcriptExtractor`**: its spec and
its price within the budget. -/
theorem extractorOf_extractorProgram :
    LeanVM.extractorComputedBy compiledKnowledgeExtractor = transcriptExtractor := by
  funext prog input T proof
  have h := AS.asExtractor_output leanVmKnowledgeExtractorSizeBound extractorProgram_size_le prog
    input T proof
  rw [← leanVmKnowledgeExtractorBudget_eq] at h
  exact h

end

end LeanVM.Cost
