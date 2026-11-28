module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.SumE
public meta import NativeRustcVmX64.Code.Vm.SumE
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `sum_e`'s blocks, run by the symbolic executor (x86-64)

- `regsS`, registers only: the entry's tests (`b0`, `b1`), the starts of the scalar path (`b2`)
  and of the unrolled loop (`b4`), the tail's test (`b6`) and start (`b7`);
- `blkS`, the unrolled loop (`b5`): region 0 the four elements it reads, R9 their address plus
  `56`;
- `tailS`, the tail loop (`b8`): region 0 the element, RSI + RDI its address plus `8`;
- `retS`, region 0 the return address at RSP (`Field.frameS 0`): the returns (`b3`, `b9`).

No block writes memory; each keeps the callee-saved registers and RSP (`*_keeps`).
-/

namespace NativeRustcVmX64.Arrays.SumE

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumE NativeRustcVmX64.Field

@[expose] public section

/-- The return address at RSP. -/
abbrev retS : SState := frameS 0
/-- Registers only. -/
def regsS : SState := init []
/-- The unrolled loop: region 0 its four elements, R9 their address plus `56`. -/
def blkS : SState := init [64] [(.r9, .ptr 0 56)]
/-- The tail loop: region 0 the element, RSI + RDI its address plus `8`. -/
def tailS : SState := init [16] [] [] [] [(.bin .add .W64 (.reg .rsi) (.reg .rdi), 0, 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 retS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 blkS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 tailS
sym_block run_b9 := exec b9 retS

public theorem b0_keeps : keepsAll regsS (after b0 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b1_keeps : keepsAll regsS (after b1 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b5_keeps : keepsAll blkS (after b5 blkS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b7_keeps : keepsAll regsS (after b7 regsS) Arrays.calleeRegs = true := by
  decide +kernel
public theorem b8_keeps : keepsAll tailS (after b8 tailS) Arrays.calleeRegs = true := by
  decide +kernel

public theorem b3_ret : keepsRegs retS (after b3 retS) Arrays.calleeRegs = true ∧
    (after b3 retS).reg .rsp = some (.ptr 0 8) ∧ (after b3 retS).mem = [] := by
  decide +kernel
public theorem b9_ret : keepsRegs retS (after b9 retS) Arrays.calleeRegs = true ∧
    (after b9 retS).reg .rsp = some (.ptr 0 8) ∧ (after b9 retS).mem = [] := by
  decide +kernel

end NativeRustcVmX64.Arrays.SumE
