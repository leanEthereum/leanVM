module

public import NativeRustcVmArm.Top.Frame
public import NativeRustcVmArm.Code.Vm.LeanvmVerify
public meta import NativeRustcVmArm.Code.Vm.LeanvmVerify

/-!
# `leanvm_verify`'s blocks, run by the symbolic executor

`leanvm_verify` (`sub sp, sp, #128`: a 128-byte frame, the public input at its byte 8, the
`Decoded` at its byte 40, the prologue's slots at its bytes 64 to 127): the states its proof starts
blocks from and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`: the prologue, the context's counts read and checked): region 0 the
  frame, region 1 the context's first twelve words (X0);
- `ctxS`, at the blocks reading the context (`b3`, `b5`, `b7`): the frame (SP) and the context;
- `frameS`, at the blocks writing the frame and calling (`b12`, `b15`, `b17`) and at the epilogue
  (`b2`, after `b1`): region 0 the frame (SP);
- `noneS`, at the blocks without memory.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify

@[expose] public section

/-- At the entry: the frame (region 0) and the context (region 1, X0). -/
def entryS : SState := init [(128, true), (96, false)] (.ptr 0 128) [(.X0, .ptr 1 0)]

/-- The frame (region 0, SP) and the context (region 1, X0). -/
def ctxS : SState := init [(128, true), (96, false)] (.ptr 0 0) [(.X0, .ptr 1 0)]

/-- The frame (region 0, SP). -/
def frameS : SState := init [(128, true)] (.ptr 0 0)

/-- No region. -/
def noneS : SState := init []

/-- The prologue's slots in the frame. -/
def slots : List (Nat × XReg) :=
  [(64, .X30), (80, .X24), (88, .X23), (96, .X22), (104, .X21), (112, .X20), (120, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 noneS
sym_block run_b2 := exec b2 frameS
sym_block run_b3 := exec b3 ctxS
sym_block run_b4 := exec b4 noneS
sym_block run_b5 := exec b5 ctxS
sym_block run_b6 := exec b6 noneS
sym_block run_b7 := exec b7 ctxS
sym_block run_b8 := exec b8 noneS
sym_block run_b9 := exec b9 noneS
sym_block run_b10 := exec b10 noneS
sym_block run_b11 := exec b11 noneS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 noneS
sym_block run_b14 := exec b14 noneS
sym_block run_b15 := exec b15 frameS
sym_block run_b16 := exec b16 noneS
sym_block run_b17 := exec b17 frameS
sym_block run_b18 := exec b18 noneS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 64 ≤ w.off ∧ w.off + w.n ≤ 128 := by
  decide +kernel

/-- The callee-saved registers outside the slots. -/
@[expose] public def nonslots : List XReg := [.X25, .X26, .X27, .X28, .X29]

public theorem b0_regs : ∀ r ∈ nonslots, (after b0 entryS).reg r = some (.reg r) := by
  decide +kernel

/-- The public input's words `b12` and `b15` store: the frame's offset and register. -/
@[expose] public def pubWords : List (Nat × XReg) := [(8, .X13), (16, .X12), (24, .X11), (32, .X10)]

/-- The `Decoded`'s words `b17` stores. -/
@[expose] public def decWords : List (Nat × XReg) := [(40, .X23), (48, .X21), (56, .X19)]

public theorem b12_pub : ∀ p ∈ pubWords, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b12 frameS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b12_mem : ∀ w ∈ (after b12 frameS).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 40 := by
  decide +kernel

public theorem b15_pub : ∀ p ∈ pubWords, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b15 frameS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b15_mem : ∀ w ∈ (after b15 frameS).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 40 := by
  decide +kernel

public theorem b17_dec : ∀ p ∈ decWords, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b17 frameS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b17_mem : ∀ w ∈ (after b17 frameS).mem, w.r = 0 ∧ 40 ≤ w.off ∧ w.off + w.n ≤ 64 := by
  decide +kernel

public theorem b12_keeps : keepsRegs frameS (after b12 frameS) nonslots = true := by
  decide +kernel

public theorem b15_keeps : keepsRegs frameS (after b15 frameS) nonslots = true := by
  decide +kernel

public theorem b17_keeps : keepsRegs frameS (after b17 frameS) nonslots = true := by
  decide +kernel

public theorem b2_restores : restores slots 128 (after b2 frameS) = true ∧
    (after b2 frameS).mem = [] := by
  decide +kernel

public theorem ctx_keeps :
    (keepsRegs ctxS (after b3 ctxS) nonslots = true ∧ (after b3 ctxS).mem = []) ∧
    (keepsRegs ctxS (after b5 ctxS) nonslots = true ∧ (after b5 ctxS).mem = []) ∧
    (keepsRegs ctxS (after b7 ctxS) nonslots = true ∧ (after b7 ctxS).mem = []) := by
  decide +kernel

public theorem none_keeps : ∀ ds ∈ [b1, b4, b6, b8, b9, b10, b11, b13, b14, b16, b18],
    keepsRegs noneS (after ds noneS) nonslots = true ∧ (after ds noneS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Top.Leanvm
