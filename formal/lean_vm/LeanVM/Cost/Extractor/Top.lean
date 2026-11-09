module

public import LeanVM.Cost.Extractor.PMLane
public import LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Extractor
import all Statement.LeanIsa

/-!
# The extractor, compiled

`extractorTop` (`Fast/Compiled.lean`, equal to `transcriptExtractor` at the permutation queries:
`extractorTop_eq`), compiled on top of the chain of its parts (the decoder, the transcript side,
the candidate runner, the replay; each module reusing the earlier ones' functions). Compiled here:
the bytecode's words (`bytecodeWordsC`), the point-free split of `Fast/Compiled.lean`, each a
function of its own (`runBothC`, `fastOfC`, `decOfC`, `leavesOfC`, `runFromLeavesC`, `stageTC`,
`afterRootStageC`), and the top body (`extractorC`): nine functions.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.FastLib

public section

-- The bytecode's words (`bytecodeWords`): sixteen slots of every instruction.
cost_compile bytecodeWordsC := LeanVM.bytecodeWords

-- The candidate runs (the tables, then the fast path's and the decoder's stacks), compiled as a
-- function of their own: inlined into the extractor, its proof does not fit the kernel's check.
cost_compile runBothC := runBoth

-- The fast path's and the decoder's stacks from the committed leaves: the extractor passes them
-- data only (a closure for the word at the top level does not fit the kernel's check either).
cost_compile fastOfC := fastOf
cost_compile decOfC := decOf
cost_compile leavesOfC := leavesOf
cost_compile runFromLeavesC := runFromLeaves
cost_compile stageTC := stageT
cost_compile afterRootStageC := afterRootStage

-- The extractor, compiled.
cost_compile extractorC := extractorTop

end

end LeanVM.Cost.Extractor
