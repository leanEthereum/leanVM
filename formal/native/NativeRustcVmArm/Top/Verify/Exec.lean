module

public import NativeRustcVmArm.Top.Frame
public import NativeRustcVmArm.Code.Vm.Verify
public meta import NativeRustcVmArm.Code.Vm.Verify

/-!
# `verify`'s blocks, run by the symbolic executor

`verify` (`str x29, [sp, #-64]!`, `sub sp, sp, #768`: an 832-byte frame, the `TState` at its byte
8, the prologue's seven slots at its bytes 768 to 831): the states its proof starts blocks from
and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`: the prologue, ending in `bl seed`): region 0 the frame;
- `initS`, after `seed` (`b1`: `TState::new`, ending in `bl verify_execution`) and at the end
  check (`b3`): region 0 the frame (SP), region 1 the `Decoded` (X19);
- `noneS`, at the blocks without memory (`b2`, `b5`, `b7`);
- `wordS`, at `b4` (`words[0]`): region 0 the `Decoded` (X19), region 1 the decoded area's word 0,
  whose address the `Decoded`'s first word holds;
- `frameS`, at `b6` (`phase`, `bl phase_count`) and the epilogues (`b8`, `b9`): region 0 the
  frame (SP).
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(832, true)] (.ptr 0 832)

/-- After `seed`, and at the end check: the frame (region 0) and the `Decoded` (region 1). -/
def initS : SState := init [(832, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- No region. -/
def noneS : SState := init []

/-- At `words[0]`: the `Decoded` (region 0) and the decoded area's word 0 (region 1). -/
def wordS : SState :=
  init [(24, false), (8, false)] .sp [(.X19, .ptr 0 0)] (aliases := [(.load 0 0 8, (1, 0))])

/-- The frame (region 0). -/
def frameS : SState := init [(832, true)] (.ptr 0 0)

/-- The prologue's slots in the frame. -/
def slots : List (Nat × XReg) :=
  [(768, .X29), (784, .X30), (792, .X23), (800, .X22), (808, .X21), (816, .X20), (824, .X19)]

/-- The `TState::new` words `b1` writes: the frame's offset (the `TState`'s plus 8) and value. -/
def initWords : List (Nat × Sym) :=
  [(304, .lit 0), (312, .lit 0), (336, .load 1 0 8), (344, .load 1 8 8), (352, .load 1 16 8),
    (360, .lit 0), (368, .lit 0), (760, .lit 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 initS
sym_block run_b2 := exec b2 noneS
sym_block run_b3 := exec b3 initS
sym_block run_b4 := exec b4 wordS
sym_block run_b5 := exec b5 noneS
sym_block run_b6 := exec b6 frameS
sym_block run_b7 := exec b7 noneS
sym_block run_b8 := exec b8 frameS
sym_block run_b9 := exec b9 frameS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 768 ≤ w.off ∧ w.off + w.n ≤ 832 := by
  decide +kernel

public theorem b0_regs : ∀ r ∈ [XReg.X24, .X25, .X26, .X27, .X28],
    (after b0 entryS).reg r = some (.reg r) := by
  decide +kernel

public theorem b1_words : ∀ p ∈ initWords, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b1 initS).mem = some (p.2, i) := by
  decide +kernel

public theorem b1_mem : ∀ w ∈ (after b1 initS).mem, w.r = 0 ∧ 208 ≤ w.off ∧ w.off + w.n ≤ 768 := by
  decide +kernel

public theorem b1_keeps : keepsRegs initS (after b1 initS) calleeRegs = true := by
  decide +kernel

public theorem b2_keeps : keepsRegs noneS (after b2 noneS) calleeRegs = true ∧
    (after b2 noneS).mem = [] := by
  decide +kernel

public theorem b3_keeps : keepsRegs initS (after b3 initS) calleeRegs = true ∧
    (after b3 initS).mem = [] := by
  decide +kernel

public theorem b4_keeps : keepsRegs wordS (after b4 wordS) calleeRegs = true ∧
    (after b4 wordS).mem = [] := by
  decide +kernel

public theorem b5_keeps : keepsRegs noneS (after b5 noneS) calleeRegs = true ∧
    (after b5 noneS).mem = [] := by
  decide +kernel

public theorem b6_keeps : keepsRegs frameS (after b6 frameS) [.X24, .X25, .X26, .X27, .X28] = true ∧
    (after b6 frameS).mem = [] := by
  decide +kernel

public theorem b7_keeps : keepsRegs noneS (after b7 noneS) calleeRegs = true ∧
    (after b7 noneS).mem = [] := by
  decide +kernel

public theorem b8_restores : restores slots 832 (after b8 frameS) = true ∧
    (after b8 frameS).mem = [] := by
  decide +kernel

public theorem b9_restores : restores slots 832 (after b9 frameS) = true ∧
    (after b9 frameS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Top.Verify
