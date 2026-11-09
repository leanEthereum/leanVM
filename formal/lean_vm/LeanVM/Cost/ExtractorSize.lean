module

public import LeanVM.Cost.ExtractorProgram

/-!
# The extractor's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`): the kernel evaluations over the compiled extractor's program, in a
module of their own that imports only the program's definition, so that no edit of a proof
rebuilds them.

* `extractorProgram_indices_increasing`: the bodies' indices are distinct (they increase from the
  entry's `0`: the compiler allocates indices from `1`, and sorts each dependency list);
* **`extractorProgram_size_le_measured`**: the program's size is at most `14242`, evaluated on the
  program itself; its exact size is `14225`: the bodies' sizes (`14201`: `700` compiled bodies and
  the entry, each natural literal counted by its limbs) and `12` indices without a body, a literal
  `0` of size `2` each, `713` indices in all.
-/

namespace LeanVM.Cost

open LeanVM.Cost.Extractor

public section

/-- The bodies' indices increase: the entry's `0`, then the compiled extractor's. -/
theorem extractorProgram_indices_increasing :
    increasingFrom 0 (extractorC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- **The program's size**, from its bodies (`size_ofList_add_length`: the bodies' sizes and two
per index without a body), each count evaluated: at most `14242` (exactly `14225`). -/
theorem extractorProgram_size_le_measured : compiledKnowledgeExtractor.size ≤ 14242 := by
  have h := size_ofList_add_length extractorProgramBodies (by
    rw [extractorProgramBodies, List.map_cons]
    exact nodup_of_increasing extractorProgram_indices_increasing)
  have h1 : (extractorProgramBodies.map fun p ↦ p.2.size).sum = 14201 := by decide +kernel
  have h2 : (extractorProgramBodies.map (·.1)).foldr max 0 = 712 := by decide +kernel
  have h3 : extractorProgramBodies.length = 701 := by decide +kernel
  unfold compiledKnowledgeExtractor
  omega

end

end LeanVM.Cost
