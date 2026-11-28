module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.GluedEval
public meta import NativeRustcVmX64.Code.Vm.GluedEval
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `glued_eval`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 32 bytes below the entry's RSP and the return address (`push rbx` at offset 24,
then either the two stack arguments of `induced_weight` at 8, 16 and its return address at 0, or
`eq_eval`'s return address at 16); region 1 the glued claim (RSI, 6064 bytes).
- `entryS` (`b0`: push RBX, test the kind), then `b1` (kind `≠ 0`: `induced_weight`'s arguments,
  the point's slice pushed, the call) or `b3` (kind `0`: `eq_eval`'s arguments, the call);
- `Field.midS 32` (`b2`, after `induced_weight`): drop the stack arguments, pop RBX, return
  (`slots32`: RBX at 24 of the 32 bytes);
- `stS` (`b4a`, after `eq_eval`): region 0 the `Option<EW>` RBX points to, `Some` stored;
  `Field.midS 16` (`b4b`): pop RBX, return (`slots16`: RBX at 8 of the 16 bytes).
-/

namespace NativeRustcVmX64.Whir.GluedEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GluedEval NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs freeRegs restores)

@[expose] public section

/-- At the entry: the frame, the glued claim. -/
def entryS : SState := init [40, 6064] [(.rsp, .ptr 0 32), (.rsi, .ptr 1 0)]
/-- After `eq_eval`: the output RBX points to. -/
def stS : SState := init [24] [(.rbx, .ptr 0 0)]

/-- The stores of `Some`. -/
def b4a : List Directive := b4.take 3
/-- The epilogue after `eq_eval`. -/
def b4b : List Directive := b4.drop 3

/-- RBX's slot among the 32 bytes below the entry's RSP. -/
def slots32 : List (Nat × Reg64) := [(24, .rbx)]
/-- RBX's slot among the 16 bytes below the entry's RSP. -/
def slots16 : List (Nat × Reg64) := [(8, .rbx)]

/-- The callee-saved registers but RBX. -/
def others : List Reg64 := [.rbp, .r12, .r13, .r14, .r15]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (midS 32)
sym_block run_b3 := exec b3 (after b0 entryS)
sym_block run_b4a := exec b4a stS
sym_block run_b4b := exec b4b (midS 16)

public theorem b1_facts : (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b1 (after b0 entryS)).mem = some (.reg .rbx, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b1 (after b0 entryS)).mem = some (.reg .rdx, i)) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b1 (after b0 entryS)).mem = some (.reg .rcx, i)) ∧
    (∀ r ∈ others, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (after b1 (after b0 entryS)).reg .rdi = some (.reg .rdi) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 0) := by
  decide +kernel

public theorem b3_facts : (∀ w ∈ (after b3 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b3 (after b0 entryS)).mem = some (.reg .rbx, i)) ∧
    (∀ r ∈ others, (after b3 (after b0 entryS)).reg r = some (.reg r)) ∧
    (after b3 (after b0 entryS)).reg .rdx = some (.reg .rdx) ∧
    (after b3 (after b0 entryS)).reg .rcx = some (.reg .rcx) ∧
    (after b3 (after b0 entryS)).reg .rbx = some (.reg .rdi) ∧
    (after b3 (after b0 entryS)).reg .rsp = some (.ptr 0 16) := by
  decide +kernel

public theorem b2_restores : restores slots32 32 (after b2 (midS 32)) = true ∧
    (after b2 (midS 32)).mem = [] := by
  decide +kernel

public theorem b4a_facts : keepsRegs stS (after b4a stS) (.rsp :: freeRegs slots16) = true ∧
    (∀ w ∈ (after b4a stS).mem, w.r = 0 ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b4a stS).mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b4a stS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 0 (8 + 8 + i) (after b4a stS).mem = some (.reg .rdx, i)) := by
  decide +kernel

public theorem b4b_restores : restores slots16 16 (after b4b (midS 16)) = true ∧
    (after b4b (midS 16)).mem = [] := by
  decide +kernel

public theorem others_spec : ∀ r, calleeSaved r = true → r ∉ slots32.map (·.2) → r ∈ others := by
  intro r h h'
  cases r <;> simp_all [others, calleeSaved, slots32]

public theorem others_spec16 : ∀ r, calleeSaved r = true → r ∉ slots16.map (·.2) → r ∈ others := by
  intro r h h'
  cases r <;> simp_all [others, calleeSaved, slots16]

end NativeRustcVmX64.Whir.GluedEval
