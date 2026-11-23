module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.SumE
public meta import NativeRustcVmArm.Code.Vm.SumE
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `sum_e`'s blocks, run by the symbolic executor

- `regsS`, registers only: the tests (`b0`, `b1`), the scalar path's start (`b2`), the empty
  sum's return (`b3`), the lanes' combination (`b8`), the tail's start (`b9`), the return (`b11`);
- `blkS o`, an unrolled block of four elements (`b4`-`b7`): region 0 the 64 bytes it reads, X0
  its address minus `o`;
- `tailS`, the tail loop (`b10`): region 0 the element, X11 its address plus `8`.

No block writes memory; each keeps the callee-saved registers, SP and X30 (`*_keeps`).
-/

namespace NativeRustcVmArm.Arrays.SumE

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumE

@[expose] public section

/-- Registers only. -/
def regsS : SState := init [] .sp
/-- An unrolled block: region 0 its four elements, X0 their address minus `o`. -/
def blkS (o : Int) : SState := init [(64, false)] .sp [(.X0, .ptr 0 o)]
/-- The tail loop: region 0 the element, X11 its address plus `8`. -/
def tailS : SState := init [(16, false)] .sp [(.X11, .ptr 0 8)]

/-- The registers every block but the returns keeps. -/
def keptRegs : List XReg := calleeRegs ++ [.X0, .X1, .X30]
/-- The registers the returns keep. -/
def retRegs : List XReg := calleeRegs ++ [.X30]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 (blkS 0)
sym_block run_b5 := exec b5 (blkS (-64))
sym_block run_b6 := exec b6 (blkS (-128))
sym_block run_b7 := exec b7 (blkS (-192))
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 tailS
sym_block run_b11 := exec b11 regsS

public theorem b0_keeps : keepsAll regsS (after b0 regsS) keptRegs = true := by decide +kernel
public theorem b1_keeps : keepsAll regsS (after b1 regsS) keptRegs = true := by decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS) keptRegs = true := by decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) retRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll (blkS 0) (after b4 (blkS 0)) keptRegs = true := by decide +kernel
public theorem b5_keeps : keepsAll (blkS (-64)) (after b5 (blkS (-64))) keptRegs = true := by
  decide +kernel
public theorem b6_keeps : keepsAll (blkS (-128)) (after b6 (blkS (-128))) keptRegs = true := by
  decide +kernel
public theorem b7_keeps : keepsAll (blkS (-192)) (after b7 (blkS (-192))) keptRegs = true := by
  decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) keptRegs = true := by decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) keptRegs = true := by decide +kernel
public theorem b10_keeps : keepsAll tailS (after b10 tailS) keptRegs = true := by decide +kernel
public theorem b11_keeps : keepsAll regsS (after b11 regsS) retRegs = true := by decide +kernel

end NativeRustcVmArm.Arrays.SumE
