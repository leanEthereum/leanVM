/-
  Rv64mc.Spec.Bus.VerifyBusBalance

  The contract of `verifier::bus::verify_bus_balance(layout: &Layout, transcript: &mut Transcript)
  -> Result<BusResult, VerifierError>`: the result's slot (`sret`) in `a0`, the layout in `a1` (`LayoutAt`, with the
  bytecode it borrows), the transcript in `a2` (`TranscriptAt`), the slot and the transcript in a caller's frame
  and apart. It is the mirror's step `Model.verifyBusBalanceRust`: where the mirror returns `r` and `t'`, the slot
  holds `Ok(r)` (`BusResultAt`, its buffers allocated by the call) and the transcript is `t'`; where it fails, the
  slot holds an `Err`. It writes the slot and the transcript (`Out`).
-/

import Rv64mc.Spec.Bus.Repr
import Rv64mc.Model.Bus

namespace Rv64mc.Spec.Bus.VerifyBusBalance

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript

def Pre (env : Env) (l : Model.LayoutRust) (bc : Model.BytecodeRust) (t : Model.TState) (regs : Reg → Word)
    (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x11) Layouts.Layout.byteSize ∧ LayoutAt env m (regs .x11) l bc ∧
    TranscriptAt env m (regs .x12) t ∧ InFrame (regs .x2) (regs .x12) Layouts.Transcript.byteSize ∧
    InFrame (regs .x2) (regs .x10) Layouts.ResultBusResult.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    Apart (regs .x10) Layouts.ResultBusResult.byteSize (regs .x12) Layouts.Transcript.byteSize

def Post (env : Env) (l : Model.LayoutRust) (bc : Model.BytecodeRust) (t : Model.TState) (regs : Reg → Word)
    (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.verifyBusBalanceRust l bc).run t with
  | some (r, t') => ResultBusResultAt env m' (regs .x10) (some r) ∧ TranscriptAt env m' (regs .x12) t'
  | none => ResultBusResultAt env m' (regs .x10) none

/-- What it writes besides its stack and allocations: the result's slot and the transcript. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultBusResult.byteSize b ∨ InRange (regs .x12) Layouts.Transcript.byteSize b

/-- **The contract of `verify_bus_balance`**, function `i` of `p` with `need` bytes of stack (its frame is 1152
    bytes), for every layout, bytecode and transcript state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ l bc t, Holds env p i need (Pre env l bc t) (Post env l bc t) Out

end Rv64mc.Spec.Bus.VerifyBusBalance
