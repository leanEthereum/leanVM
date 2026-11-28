module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Code.Vm.Ladder
public meta import NativeRustcVmArm.Code.Vm.Ladder
public meta import NativeRustcVmArm.Layout.Common

/-!
# `ladder`'s blocks, run by the symbolic executor

`ladder` is straight-line code: `b0` checks the window (else `b11` stores the `None` tag), `b1` to
`b7` pick the level count `n` (`3` to `6`) from `μ` and the registers of the levels past the
third, `b8` compares `n` with `QUERY_LEVELS`' entry, `b9` to `b17` load the query counts from
`QUERY_TABLE`'s entry, and `b15` stores the result.

Three environments, each from the machine state its first block starts in:
- `entryS` (at the entry, inside the window): region 0 the result (X0), region 1 the row
  `r - 1` of `QUERY_LEVELS` (`lvRow`, the address `b8` computes), `μ - 16` below `15`;
- `midS` (at `b9`): region 0 the result, region 1 the row of `QUERY_TABLE` (`qtRow`), X15 below
  `15`;
- `endS` (at `b15`): region 0 the result.
Outside the window, `outS`: region 0 the result.
-/

namespace NativeRustcVmArm.Layout.Ladder

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Ladder

@[expose] public section


/-- `r - 1`. -/
def rm1 : Sym := .bin .sub .W64 (.reg .X2) (.lit 1)
/-- `μ - 16`. -/
def mu16 : Sym := .bin .sub .W64 (.reg .X1) (.lit 16)
/-- Row `r - 1` of `QUERY_LEVELS`, as `b8` computes it. -/
def lvRow : Sym := .bin .add .W64 (.bin .mul .W64 rm1 (.lit 120)) (.label NativeRustcVmArm.Vm.Symbols.rodata12Label)
/-- Row X16 of `QUERY_TABLE`, as `b9` computes it. -/
def qtRow : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X16) (.lit 720)) (.label NativeRustcVmArm.Vm.Symbols.rodata11Label)

/-- Outside the window: the result (region 0, X0). -/
def outS : SState := init [(160, false)] .sp [(.X0, .ptr 0 0)]

/-- At the entry, inside the window. -/
def entryS : SState :=
  init [(160, false), (120, false)] .sp [(.X0, .ptr 0 0)] [] [(mu16, 15)] [(lvRow, (1, 0))]

/-- At `b9`. -/
def midS : SState :=
  init [(160, false), (720, false)] .sp [(.X0, .ptr 0 0)] [] [(.reg .X15, 15)] [(qtRow, (1, 0))]

/-- At `b15`. -/
def endS : SState := init [(160, false)] .sp [(.X0, .ptr 0 0)]

/-- The states the blocks of the window's paths start in. -/
def s1 : SState := after b0 entryS
def s3 : SState := after b1 s1
def s5 : SState := after b3 s3
def s8a : SState := after b2 s3
def s8b : SState := after b4 s5
def s8c : SState := after b6 (after b5 s5)
def s8d : SState := after b7 (after b5 s5)
def s9 : SState := after b9 midS
def s13a : SState := after b10 s9
def s12 : SState := after b12 s9
def s14a : SState := after b13 s13a
def s14b : SState := after b13 s12
def s16 : SState := after b16 s12

end

set_option Elab.async false

sym_block run_out := exec b0 outS
sym_block run_b11 := exec b11 (after b0 outS)
sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 s1
sym_block run_b2 := exec b2 s3
sym_block run_b3 := exec b3 s3
sym_block run_b4 := exec b4 s5
sym_block run_b5 := exec b5 s5
sym_block run_b6 := exec b6 (after b5 s5)
sym_block run_b7 := exec b7 (after b5 s5)
sym_block run_b8a := exec b8 s8a
sym_block run_b8b := exec b8 s8b
sym_block run_b8c := exec b8 s8c
sym_block run_b8d := exec b8 s8d
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 s9
sym_block run_b12 := exec b12 s9
sym_block run_b13a := exec b13 s13a
sym_block run_b13b := exec b13 s12
sym_block run_b14a := exec b14 s14a
sym_block run_b14b := exec b14 s14b
sym_block run_b16 := exec b16 s12
sym_block run_b14c := exec b14 s16
sym_block run_b17 := exec b17 s16
sym_block run_b15 := exec b15 endS

end NativeRustcVmArm.Layout.Ladder
