module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.Evaluate
public meta import NativeRustcVmArm.Code.Vm.Evaluate
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `evaluate`'s blocks, run by the symbolic executor

- `entryS`, at the entry: region 0 the 80-byte frame below SP. `b0` saves X19-X27 and X30 and
  branches on the count: `0` goes to `b14` (the sum `0`), else `b1` sets up the loop (X20, X21 the
  row, X22 the count, X23, X19 the sum, X24 term `0` plus `32`, X25 `8`).
- `termS`, at the loop head `.L5` (`b5`): region 0 term `i` (X24 its address plus `32`): its
  degree (X26), coefficient (X0, X1) and columns (X27).
- `colS`, at a column's load (`b6`, `.L9`: `b12`): region 0 the two column words (X27).
- `ldS`, at a row element's load (`b7b`, `b2b`, after `b7a`, `b2a` computed its address in X8):
  region 0 the element.
- `regsS`: blocks that touch no memory (`b3`, `b4`, `b8`, `b9`, `b10`, `b11`, `b13`, `b7a`,
  `b2a`).
- `exitS`, at the epilogue `.L12` (`b15`): region 0 the frame.
-/

namespace NativeRustcVmArm.Layout.Evaluate

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Evaluate NativeRustcVmArm.Arrays

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(80, true)] (.ptr 0 80)
/-- At the loop head: term `i` (X24 its address plus `32`). -/
def termS : SState := init [(40, false)] .sp [(.X24, .ptr 0 32)]
/-- At a column's load: the columns (X27). -/
def colS : SState := init [(16, false)] .sp [(.X27, .ptr 0 0)]
/-- At a row element's load: the element (X8). -/
abbrev elemS : SState := ldS .X8 0
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(80, true)] (.ptr 0 0)

/-- `b7`'s address computation. -/
def b7a : List Directive := b7.take 1
/-- `b7`'s load and call. -/
def b7b : List Directive := b7.drop 1
/-- `.L2`'s address computation. -/
def b2a : List Directive := b2.take 2
/-- `.L2`'s load. -/
def b2b : List Directive := b2.drop 2

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X27), (16, .X26), (24, .X25), (32, .X24), (40, .X23), (48, .X22), (56, .X21),
    (64, .X20), (72, .X19)]

/-- The callee-saved registers no slot holds. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

/-- The registers the loop keeps across most blocks. -/
def keepL : List XReg := [.X0, .X1, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27]
/-- The registers the loop head keeps. -/
def low7 : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25]

/-- `S` keeps `S₀`'s registers `rs`. -/
def keepR (S₀ S : SState) (rs : List XReg) : Bool :=
  rs.all fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b14 := exec b14 (after b0 entryS)
sym_block run_b5 := exec b5 termS
sym_block run_b4 := exec b4 regsS
sym_block run_b6 := exec b6 colS
sym_block run_b12 := exec b12 colS
sym_block run_b7a := exec b7a regsS
sym_block run_b7b := exec b7b elemS
sym_block run_b2a := exec b2a regsS
sym_block run_b2b := exec b2b elemS
sym_block run_b3 := exec b3 regsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b15 := exec b15 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 80 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel
public theorem b14_frame : (∀ p ∈ slots, p.1 + 8 ≤ 80 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b14 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b14 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b14 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b5_low7 : keepR termS (after b5 termS) low7 = true := by decide +kernel
public theorem b6_keepL : keepR colS (after b6 colS) keepL = true := by decide +kernel
public theorem b12_keepL : keepR colS (after b12 colS) keepL = true := by decide +kernel
public theorem b7a_keepL : keepR regsS (after b7a regsS) keepL = true := by decide +kernel
public theorem b7b_keepL : keepR elemS (after b7b elemS) keepL = true := by decide +kernel
public theorem b2a_keepL : keepR regsS (after b2a regsS) keepL = true := by decide +kernel
public theorem b2b_keepL : keepR elemS (after b2b elemS) keepL = true := by decide +kernel
public theorem b3_keepL : keepR regsS (after b3 regsS) keepL = true := by decide +kernel
public theorem b8_keepL : keepR regsS (after b8 regsS) keepL = true := by decide +kernel
public theorem b9_keepL : keepR regsS (after b9 regsS) keepL = true := by decide +kernel
public theorem b10_keepL : keepR regsS (after b10 regsS) keepL = true := by decide +kernel
public theorem b11_keepL : keepR regsS (after b11 regsS) keepL = true := by decide +kernel
public theorem b13_keepL : keepR regsS (after b13 regsS) keepL = true := by decide +kernel
public theorem b4_keep : keepR regsS (after b4 regsS) [.X20, .X21, .X25] = true := by
  decide +kernel

public theorem b5_keeps : keepsAll termS (after b5 termS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b6_keeps : keepsAll colS (after b6 colS) keptRegs = true := by decide +kernel
public theorem b12_keeps : keepsAll colS (after b12 colS) keptRegs = true := by decide +kernel
public theorem b7a_keeps : keepsAll regsS (after b7a regsS) keptRegs = true := by decide +kernel
public theorem b7b_keeps : keepsAll elemS (after b7b elemS) keptRegs = true := by decide +kernel
public theorem b2a_keeps : keepsAll regsS (after b2a regsS) keptRegs = true := by decide +kernel
public theorem b2b_keeps : keepsAll elemS (after b2b elemS) keptRegs = true := by decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) keptRegs = true := by decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) keptRegs = true := by decide +kernel
public theorem b10_keeps : keepsAll regsS (after b10 regsS) keptRegs = true := by decide +kernel
public theorem b11_keeps : keepsAll regsS (after b11 regsS) keptRegs = true := by decide +kernel
public theorem b13_keeps : keepsAll regsS (after b13 regsS) keptRegs = true := by decide +kernel
public theorem b15_restores : restores slots 80 (after b15 exitS) = true ∧ (after b15 exitS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Layout.Evaluate
