module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.ColumnKappas
public meta import NativeRustcVmArm.Code.Vm.ColumnKappas
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `column_kappas`'s block, run by the symbolic executor

From `entryS`: region 0 the `[usize; 158]` result (X0), region 1 the six heights (X3). The one
block `b0` stores column `c`'s log-size, `colSym (srcOf c)`: the memory's log-size (X1), the
bytecode's (X2), `q_keccak`'s (`heights[5] + 6`) or a table's height.
-/

namespace NativeRustcVmArm.Layout.ColumnKappas

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ColumnKappas

@[expose] public section

/-- At the entry: the result (region 0), the heights (region 1). -/
def entryS : SState := init [(1264, false), (48, false)] .sp [(.X0, .ptr 0 0), (.X3, .ptr 1 0)]

/-- Where column `c`'s log-size comes from: `0` the memory's, `1` the bytecode's, `2`
`q_keccak`'s, `3 + t` table `t`'s height. -/
def srcOf (c : Nat) : Nat :=
  if c < 3 then 0 else if c = 3 then 1 else if c = 4 then 2 else if c < 18 then 3
  else if c < 31 then 4 else if c < 38 then 5 else if c < 52 then 6 else if c < 66 then 7 else 8

/-- The symbolic value of a source. -/
def colSym : Nat → Sym
  | 0 => .reg .X1
  | 1 => .reg .X2
  | 2 => .bin .add .W64 (.load 1 40 8) (.lit 6)
  | s => .load 1 (8 * (s - 3)) 8

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS

public theorem b0_facts : (∀ c < 158, ∀ i < 8, findWrite 0 (8 * c + i) (after b0 entryS).mem =
      some (colSym (srcOf c), i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1264) ∧
    keeps entryS (after b0 entryS) = true := by
  decide +kernel

end NativeRustcVmArm.Layout.ColumnKappas
