/-
  Rv64mc.Spec.Bytecode.IsValidEncoding

  The contract of `verifier::bytecode::is_valid_encoding_of_a_leanisa_program(stacked_bytecode: &[u64]) -> bool`:
  the slice passed as a pointer and a length (`a0`, `a1`), its words in the heap (`WordsAt`, `Live`); the result in
  `a0` is `Model.validEncodingRust`'s, `1` for `true` and `0` for `false`.
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Bytecode

namespace Rv64mc.Spec.Bytecode.IsValidEncoding

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The stack it needs: its frame (160 bytes); its one callee, the bounds check's panic, does not return. -/
def need : Nat := 160

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs WordsAt m (regs .x10) (regs .x11) ws ∧ env.Live m (regs .x10) (8 * ws.length)

def Post (ws : List Word) (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = if Model.validEncodingRust ws then 1#64 else 0#64

/-- **The contract of `is_valid_encoding_of_a_leanisa_program`**, function `i` of `p`, for every slice. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post ws)

end Rv64mc.Spec.Bytecode.IsValidEncoding
