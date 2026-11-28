module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.ColumnKappas
public meta import NativeRustcVmX64.Code.Vm.ColumnKappas
public meta import NativeRustcVmX64.Layout.Common

/-!
# `column_kappas`'s block, run by the symbolic executor (x86-64)

From `entryS`: region 0 the frame (the pushed RBX, the return address), region 1 the
`[usize; 158]` result (RDI), region 2 the six heights (RCX). The one block `b0` pushes RBX,
stores column `c`'s log-size, `colSym (srcOf c)`: the memory's log-size (RSI), the bytecode's
(RDX), `q_keccak`'s (`heights[5] + 6`) or a table's height, pops RBX and returns.
-/

namespace NativeRustcVmX64.Layout.ColumnKappas

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ColumnKappas
open NativeRustcVmX64.Transcript (after after_eq EpiOk)

@[expose] public section

/-- At the entry: the frame (region 0, RSP at its offset `8`), the result (region 1), the heights
(region 2). -/
def entryS : SState := init [16, 1264, 48] [(.rsp, .ptr 0 8), (.rdi, .ptr 1 0), (.rcx, .ptr 2 0)]

/-- Where column `c`'s log-size comes from: `0` the memory's, `1` the bytecode's, `2`
`q_keccak`'s, `3 + t` table `t`'s height. -/
def srcOf (c : Nat) : Nat :=
  if c < 3 then 0 else if c = 3 then 1 else if c = 4 then 2 else if c < 18 then 3
  else if c < 31 then 4 else if c < 38 then 5 else if c < 52 then 6 else if c < 66 then 7 else 8

/-- The symbolic value of a source. -/
def colSym : Nat → Sym
  | 0 => .reg .rsi
  | 1 => .reg .rdx
  | 2 => .bin .add .W64 (.load 2 40 8) (.lit 6)
  | s => .load 2 (8 * (s - 3)) 8

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS

public theorem b0_facts : (∀ c < 158, ∀ i < 8, findWrite 1 (8 * c + i) (after b0 entryS).mem =
      some (colSym (srcOf c), i)) ∧
    (∀ w ∈ (after b0 entryS).mem, ∃ e ∈ [(0, 8), (1, 1264)], w.r = e.1 ∧ w.off + w.n ≤ e.2) ∧
    EpiOk 8 [] (after b0 entryS) = true := by
  decide +kernel

end NativeRustcVmX64.Layout.ColumnKappas
