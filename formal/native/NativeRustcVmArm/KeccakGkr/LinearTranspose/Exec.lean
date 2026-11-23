module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.LinearTranspose
public meta import NativeRustcVmArm.Code.Vm.LinearTranspose

/-!
# `linear_transpose`'s blocks, run by the symbolic executor

Each block from the symbolic state its proof starts it in: the prologue and epilogue with the
80-byte frame as region 0; the blocks without memory accesses from `regsS`; the `ρ` load with
`KECCAK_RHO` as region 0; each loop body with the elements it reads and writes as regions at the
loop's pointers, the indices bounded.
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LinearTranspose

@[expose] public section

/-- `x & 63`. -/
def and63 (x : Sym) : Sym := .bin .and .W64 x (.lit 63)

/-- The entry: region 0 the frame below SP. -/
def entryS : SState := init [(80, true)] (.ptr 0 80)
/-- No regions, every register its atom. -/
def regsS : SState := init [] .sp
/-- The `ρ` load: region 0 `KECCAK_RHO` at X26, the lane X23 below 25. -/
def rhoS : SState := init [(100, false)] .sp [(.X26, .ptr 0 0)] [] [(.reg .X23, 25)]
/-- The copy loop: region 0 the source lane at X9, region 1 the element at X11 - 8. -/
def copyS : SState :=
  init [(1024, false), (16, false)] .sp [(.X9, .ptr 0 0), (.X11, .ptr 1 8)] [] [(and63 (.reg .X8), 64)]
/-- The copy loop of lane 0, two elements per iteration: region 1 the two at X10 - 16. -/
def copy2S : SState :=
  init [(1024, false), (32, false)] .sp [(.X9, .ptr 0 0), (.X10, .ptr 1 16)] []
    [(and63 (.reg .X8), 64), (and63 (.bin .add .W32 (.reg .X8) (.lit 1)), 64)]
/-- A column loop: region 0 `g` from X10 (`n` bytes), region 1 the column's element at X8 - 8. -/
def colS (n : Nat) : SState := init [(n, false), (16, false)] .sp [(.X10, .ptr 0 0), (.X8, .ptr 1 8)]
/-- The third column loop: region 0 `g` from X20 + X9 + 1024, region 1 the column's element at
X8 + X9 + 1024, reached by aliases. -/
def col2S : SState :=
  init [(22544, false), (16, false)] .sp [] [] []
    [(.bin .add .W64 (.reg .X20) (.reg .X9), (0, -1024)), (.bin .add .W64 (.reg .X8) (.reg .X9), (1, -1024))]
/-- The output loop's head: the constants X12, X13. -/
def outHeadS : SState :=
  init [] .sp [(.X12, .lit 14757395258967641293), (.X13, .lit 4096)]
/-- The output loop: regions 0, 1, 2, 3 the column element at X14 - 8, the `g` element at X16 - 8,
the other column at X15, the output element at X17 - 8. -/
def outS : SState :=
  init [(16, false), (16, false), (1024, false), (16, false)] .sp
    [(.X14, .ptr 0 8), (.X16, .ptr 1 8), (.X15, .ptr 2 0), (.X17, .ptr 3 8)] []
    [(and63 (.reg .X18), 64)]
/-- The epilogue: region 0 the frame from SP. -/
def exitS : SState := init [(80, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 regsS
sym_block e2 := exec b2 regsS
sym_block e3 := exec b3 rhoS
sym_block e4 := exec b4 regsS
sym_block e5 := exec b5 copyS
sym_block e6 := exec b6 regsS
sym_block e7 := exec b7 regsS
sym_block e8 := exec b8 copy2S
sym_block e9 := exec b9 regsS
sym_block e10 := exec b10 regsS
sym_block e11 := exec b11 (colS 20496)
sym_block e12 := exec b12 regsS
sym_block e13 := exec b13 (colS 21520)
sym_block e14 := exec b14 regsS
sym_block e15 := exec b15 col2S
sym_block e16 := exec b16 regsS
sym_block e17 := exec b17 (colS 23568)
sym_block e18 := exec b18 regsS
sym_block e19 := exec b19 (colS 24592)
sym_block e20 := exec b20 regsS
sym_block e21 := exec b21 outHeadS
sym_block e22 := exec b22 outS
sym_block e23 := exec b23 regsS
sym_block e24 := exec b24 exitS

end NativeRustcVmArm.KeccakGkr.LinearTranspose
