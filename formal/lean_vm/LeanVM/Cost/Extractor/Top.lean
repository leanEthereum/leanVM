module

public import LeanVM.Cost.Extractor.Transcript
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Extractor
import all Statement.LeanIsa

/-!
# The extractor's shared functions, compiled

After the transcript's (`Transcript.lean`): the bytecode's words (`bytecodeWordsC`), a root's
committed leaves through a preimage index (`leavesInC`), and the inverse novel-basis transform
(`novelInvC`), which the descent's step up and level 0's stack run per lane.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.FastLib

public section

cost_enc LeanVM.Parameters.Opcode

open LeanVM.Semantics LeanVM.Arithmetization in
/-- The opcodes' codes `g^0, …, g^5` as words. -/
theorem opcodeCodeLit (o : Opcode) : Opcode.code o = K.ofLane (match o with
    | .xor => 1 | .mulNative => 2 | .setConstant => 4 | .deref => 8 | .jump => 16
    | .keccak => 32) := by
  cases o <;> decide +kernel

cost_rewrite opcodeCodeLit

open LeanVM.Semantics LeanVM.Arithmetization in
/-- `KECCAK`'s output flags by cases on the cells written (the derived equality of
`KeccakOutputCells` has no machine encoding). -/
theorem keccakOutputFlagsCases (outCells : KeccakOutputCells) :
    keccakOutputFlags outCells = match outCells with
      | .one => (layoutFlagWord false, layoutFlagWord false)
      | .two => (layoutFlagWord true, layoutFlagWord false)
      | .all => (layoutFlagWord true, layoutFlagWord true) := by
  cases outCells <;> rfl

cost_rewrite keccakOutputFlagsCases

-- The bytecode's words (`bytecodeWords`): sixteen slots of every instruction.
cost_compile bytecodeWordsC := LeanVM.bytecodeWords

-- A root's committed leaves.
cost_compile leavesInC := leavesIn

cost_compile novelInvC := novelInv

end

end LeanVM.Cost.Extractor
