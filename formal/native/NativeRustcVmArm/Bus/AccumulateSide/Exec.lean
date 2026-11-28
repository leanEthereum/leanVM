module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.AccumulateSide
public meta import NativeRustcVmArm.Code.Vm.AccumulateSide

/-!
# `accumulate_side`'s blocks, run by the symbolic executor

Region 0 the 12096-byte frame (with the 72 bytes of stack arguments above it where a block reads
them). Region 1, where a block reads one: the side layout at X6/X19 (`sl`), its framework
placements at X21 (`sl + 16`); the framework fingerprints at X7/X26 (region 2); a table placement
at X27 - 8 (`sP`); a block at X28 - 8 (`sB`); `TABLES` (`sT`, the owner X20 below `6`); the
layout's heights and rows (`sQ`, through the frame words at 48 and 40); the output (`sO`, through
the frame word at 16; `sE`, at X10). `zS` runs a turn of the zeroing loop: region 0 the 160 bytes
it clears, at X9 + X8 + 5920, SP a variable.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide

@[expose] public section


/-- At the entry: the frame and the stack arguments, SP 12096 bytes in; the side layout at X6. -/
def s0 : SState := init [(12168, true), (888, false)] (.ptr 0 12096) [(.X6, .ptr 1 0)]
/-- In the frame. -/
def sF : SState := init [(12096, true)] (.ptr 0 0)
/-- In the frame and the stack arguments. -/
def sA : SState := init [(12168, true)] (.ptr 0 0)
/-- The framework placements at X21 (region 1, 64 bytes from `sl + 16`'s 16 before). -/
def sW : SState := init [(12096, true), (64, false)] (.ptr 0 0) [(.X21, .ptr 1 16)]
/-- Placement `0` at X21, fingerprint `0` at X7. -/
def s1 : SState :=
  init [(12096, true), (64, false), (16, false)] (.ptr 0 0) [(.X21, .ptr 1 16), (.X7, .ptr 2 0)]
/-- Placement `1` at X21 + 16, fingerprints `0`, `1` at X26. -/
def s7 : SState :=
  init [(12096, true), (64, false), (32, false)] (.ptr 0 0) [(.X21, .ptr 1 16), (.X26, .ptr 2 0)]
/-- Placement `2` at X21 + 32, fingerprints `0` to `2` at X26. -/
def s11 : SState :=
  init [(12096, true), (64, false), (48, false)] (.ptr 0 0) [(.X21, .ptr 1 16), (.X26, .ptr 2 0)]
/-- The side layout at X19. -/
def sL : SState := init [(12096, true), (888, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
/-- A table placement at X27 - 8. -/
def sP : SState := init [(12096, true), (16, false)] (.ptr 0 0) [(.X27, .ptr 1 8)]
/-- A block at X28 - 8. -/
def sB : SState := init [(12096, true), (16, false)] (.ptr 0 0) [(.X28, .ptr 1 8)]
/-- `TABLES`, the owner X20 below `6`. -/
def sT : SState :=
  init [(12096, true), (240, false)] (.ptr 0 0) [] [(NativeRustcVmArm.Vm.Symbols.rodata4Label, 1)] [(.reg .X20, 6)]
/-- The layout's heights and rows, through the frame words at 48 and 40; the owner X20 below
`6`. -/
def sQ : SState :=
  init [(12096, true), (120, false)] (.ptr 0 0) [] [] [(.reg .X20, 6)]
    [(.load 0 48 8, 1, 24), (.load 0 40 8, 1, 72)]
/-- The output through the frame word at 16. -/
def sO : SState := init [(12096, true), (24, false)] (.ptr 0 0) [] [] [] [(.load 0 16 8, 1, 0)]
/-- The output at X10. -/
def sE : SState := init [(12096, true), (24, false)] (.ptr 0 0) [(.X10, .ptr 1 0)]
/-- A turn of the zeroing loop: the 160 bytes at X9 + X8 + 5920. -/
def zS : SState :=
  init [(160, true)] (.var 0) [] [] [] [(.bin .add .W64 (.reg .X9) (.reg .X8), 0, -5920)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 s0
sym_block run_b1 := exec b1 s1
sym_block run_b2 := exec b2 sF
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 sA
sym_block run_b6 := exec b6 sF
sym_block run_b7 := exec b7 s7
sym_block run_b8 := exec b8 sF
sym_block run_b9 := exec b9 sF
sym_block run_b10 := exec b10 sF
sym_block run_b11 := exec b11 s11
sym_block run_b12 := exec b12 sF
sym_block run_b13 := exec b13 sF
sym_block run_b14 := exec b14 sF
sym_block run_b15 := exec b15 sA
sym_block run_b16 := exec b16 sW
sym_block run_b17 := exec b17 sF
sym_block run_b18 := exec b18 sW
sym_block run_b19 := exec b19 sF
sym_block run_b20 := exec b20 sW
sym_block run_b21 := exec b21 sF
sym_block run_b22 := exec b22 sF
sym_block run_b23 := exec b23 zS
sym_block run_b24 := exec b24 sF
sym_block run_b25 := exec b25 sL
sym_block run_b26 := exec b26 sF
sym_block run_b27 := exec b27 sP
sym_block run_b28 := exec b28 sB
sym_block run_b29 := exec b29 sF
sym_block run_b30 := exec b30 sB
sym_block run_b31 := exec b31 sT
sym_block run_b32 := exec b32 sF
sym_block run_b33 := exec b33 sQ
sym_block run_b34 := exec b34 sF
sym_block run_b35 := exec b35 sF
sym_block run_b36 := exec b36 sF
sym_block run_b37 := exec b37 sF
sym_block run_b38 := exec b38 sF
sym_block run_b40 := exec b40 sO
sym_block run_b42 := exec b42 sE

end NativeRustcVmArm.Bus.AccumulateSide
