/-
  Rv64mc.Spec.Walk.Execution

  The contract of `verifier::walk(bytecode, public_input, proof, checked)` (`crates/verifier/src/lib.rs`), which the
  image has with `checked` folded to `true` (its one caller is `verify_execution`), and of `verify_execution`, a tail
  call of it: the result through `sret` (`a0`), the `Bytecode` at `a1`, the public input's 32 bytes at `a2`, the
  `Proof` at `a3`, each in memory the caller owns (`Env.Owned`) and apart from the result. Where the result is `Ok`,
  the Model's `verifyExecutionRust` returns a summary. The summary's fields are not stated: `main`, the one caller,
  reads only whether it is `Ok`. It writes the result's doublewords (`Out`) besides its stack and allocations.
-/

import Rv64mc.Spec.Walk.Repr
import Rv64mc.Spec.Runtime.Mem

namespace Rv64mc.Spec.Walk.Execution

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters LeanVM.Protocol.Compile Rv64mc.Spec.Transcript

def Pre (env : Env) (bc : Model.BytecodeRust) (pi : List (BitVec 8)) (pf : Proof) (regs : Reg → Word)
    (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultSummary.byteSize ∧
    (regs .x10).toNat % 8 = 0 ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Bytecode.byteSize ∧ BytecodeAt env m (regs .x11) bc ∧
    env.Owned m (regs .x2) (regs .x12) Layouts.Digest.byteSize ∧ DigestAt m (regs .x12) pi ∧
    env.Owned m (regs .x2) (regs .x13) Layouts.Proof.byteSize ∧ ProofBodyAt env m (regs .x13) pf ∧
    Apart (regs .x10) Layouts.ResultSummary.byteSize (regs .x11) Layouts.Bytecode.byteSize ∧
    Apart (regs .x10) Layouts.ResultSummary.byteSize (regs .x12) Layouts.Digest.byteSize ∧
    Apart (regs .x10) Layouts.ResultSummary.byteSize (regs .x13) Layouts.Proof.byteSize

def Post (bc : Model.BytecodeRust) (pi : List (BitVec 8)) (pf : Proof) (regs : Reg → Word)
    (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  ResultOkAt m' (regs .x10) → (Model.verifyExecutionRust bc pi pf).isSome = true

/-- What it writes besides its stack and allocations: the result's doublewords. -/
def Out (regs : Reg → Word) (_m : MachineState) : Word → Prop :=
  Spec.Runtime.DwordsOf (regs .x10) Layouts.ResultSummary.byteSize

/-- **The contract of `walk`** (and of `verify_execution`), function `i` of `p` with `need` bytes of stack, for
    every bytecode, public input and proof. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ bc pi pf, Holds env p i need (Pre env bc pi pf) (Post bc pi pf) Out

end Rv64mc.Spec.Walk.Execution
