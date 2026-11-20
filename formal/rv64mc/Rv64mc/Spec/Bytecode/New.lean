/-
  Rv64mc.Spec.Bytecode.New

  The contract of `Bytecode::new(stacked_bytecode: &[u64]) -> Result<Bytecode, VerifierError>`: the result's slot
  (`sret`, 64 bytes, 8-aligned, the caller's) in `a0`, the words as a slice (`a1`, `a2`, allocated before). It
  writes `Model.newRust`'s answer at `sret` (`ResultBytecodeAt`): `Ok` with the `Bytecode` (`Walk.BytecodeAt`, its
  blocks allocated by the call) where the words encode a program, else `Err(BytecodeShape)`, the niche tag.
-/

import Rv64mc.Spec.Walk.Repr
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Bytecode

namespace Rv64mc.Spec.Bytecode.New

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The `Result<Bytecode, VerifierError>` at `a`**: `Ok` (any tag but the niche) with the bytecode, or `Err`. -/
def ResultBytecodeAt (env : Env) (m : MachineState) (a : Word) : Option Model.BytecodeRust → Prop
  | some bc => m.getMem (a + BitVec.ofNat 64 Layouts.ResultBytecode.tagOffset) ≠
        BitVec.ofNat 64 Layouts.ResultBytecode.Err.tag ∧
      Walk.BytecodeAt env m (a + BitVec.ofNat 64 Layouts.ResultBytecode.Ok.f0) bc
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultBytecode.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultBytecode.Err.tag

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultBytecode.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    SliceArgs WordsAt m (regs .x11) (regs .x12) ws ∧ env.Live m (regs .x11) (8 * ws.length)

def Post (env : Env) (ws : List Word) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ResultBytecodeAt env m' (regs .x10) (Model.newRust ws)

/-- **The contract of `Bytecode::new`**, function `i` of `p` with `need` bytes of stack (its frame is 128 bytes; it
    calls the encoding check, `keccak_hash`, `block_members` and the allocator), for every slice. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post env ws) (Whir.SretOut Layouts.ResultBytecode.byteSize)

end Rv64mc.Spec.Bytecode.New
