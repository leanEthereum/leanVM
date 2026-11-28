module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue
public meta import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `computed_bytecode_value`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 32-byte frame (R14, RBX pushed at offsets `24`, `16`, RAX at `8` for alignment,
`multilinear_eval_by`'s return address at `0`) and the return address. `entryS` at the entry
(`b0`: the pushes, the value kept in R14, RBX, the arguments shifted, `call`); `retS` after the
call (`b1`: the result compared with the value, `sete`, the pops, `ret`).
-/

namespace NativeRustcVmX64.Bus.ComputedBytecodeValue

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ComputedBytecodeValue
open NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(24, .r14), (16, .rbx)]

def entryS : SState := init [40] [(.rsp, .ptr 0 32)]
def retS : SState := init [40] [(.rsp, .ptr 0 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS

public theorem ok_b0 : ProOk 32 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧
    (after b0 entryS).reg .rdi = some (.reg .rsi) ∧ (after b0 entryS).reg .rsi = some (.reg .rdi) ∧
    (after b0 entryS).reg .rdx = some (.reg .rsi) ∧ (after b0 entryS).reg .rcx = some (.reg .rdx) ∧
    (after b0 entryS).reg .r8 = some (.reg .rcx) ∧ (after b0 entryS).reg .rbx = some (.reg .r9) ∧
    (after b0 entryS).reg .r14 = some (.reg .r8) := by
  decide +kernel

public theorem ok_b1 : EpiOk 32 slots (after b1 retS) = true ∧ (after b1 retS).mem = [] ∧
    (after b1 retS).reg .rax = some (.bin .merge .W8 (.bin .xor .W64 (.reg .rax) (.reg .r14))
      (.ite (.cmp .eq .W64 (.bin .or .W64 (.bin .xor .W64 (.reg .rdx) (.reg .rbx))
        (.bin .xor .W64 (.reg .rax) (.reg .r14))) (.lit 0)) (.lit 1) (.lit 0))) := by
  decide +kernel

end NativeRustcVmX64.Bus.ComputedBytecodeValue
