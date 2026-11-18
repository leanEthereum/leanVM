module

public import LeanVM.Cost.Extractor.Replay
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Extractor
import all Statement.LeanIsa

/-!
# The extractor's shared functions, compiled

The end of the compiled chain the agreement-set extractor (`Cost/AS/`) and the guest decoder
(`Cost/Decoder/`) build on (the transcript side, the candidate runner, the replay; each module
reusing the earlier ones' functions): the bytecode's words (`bytecodeWordsC`) and a root's
committed leaves through a preimage index (`leavesInC`).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.FastLib

public section

-- The bytecode's words (`bytecodeWords`): sixteen slots of every instruction.
cost_compile bytecodeWordsC := LeanVM.bytecodeWords

-- A root's committed leaves.
cost_compile leavesInC := leavesIn

end

end LeanVM.Cost.Extractor
