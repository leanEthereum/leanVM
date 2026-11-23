module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets
public meta import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `insertion_sort`'s blocks, run by the symbolic executor

Each block from a fresh state, its one memory access a region of its own placed by an alias:
- `regsS`: no memory (`b0`-`b3`, `b7`, `b8`, `b10`, `b12`-`b14`, `b16`-`b18`);
- `ldS p i o`: region 0 the 8 bytes at `p + 8 i` (`ldr [p, i, lsl #3]`, alias offset `o`):
  `order[i]` (`b4`), `sizes[b]` (`b6`, `b11`), `sizes[a]` (`b9`);
- `prevS`: region 0 `order[j - 1]`, `x0 + 8 j` its end (`b5`);
- `swapS`: region 0 `order[j - 1]`, `order[j]`, both `x0 + 8 j` and `x11` its middle (`b15`).
-/

namespace NativeRustcVmArm.Layout.InsertionSort

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InsertionSortOfStackOffsets

@[expose] public section

/-- `[p, i, lsl #3]`'s address. -/
def idx (p i : XReg) : Sym := mkBin .add .W64 (.reg p) (mkUn (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg i))

/-- `p + (i << 3)`, as `add xd, p, i, lsl #3` computes it. -/
def shl3 (p i : XReg) : Sym := .bin .add .W64 (.reg p) (.un (.shift .LSL 3) .W64 (.reg i))

/-- Registers only. -/
def regsS : SState := init [] .sp
/-- A load at `[p, i, lsl #3]`: the word (region 0). -/
def ldS (p i : XReg) : SState := init [(8, false)] .sp [] [] [] [(idx p i, 0, 0)]
/-- `b5`: `order[j - 1]` (region 0), `x0 + 8 j` its end. -/
def prevS : SState := init [(8, false)] .sp [] [] [] [(shl3 .X0 .X10, 0, 8)]
/-- `b15`: `order[j - 1]`, `order[j]` (region 0), `x0 + 8 j` and `x11` its middle. -/
def swapS : SState := init [(16, false)] .sp [] [] [] [(idx .X0 .X10, 0, 8), (.reg .X11, 0, 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 (ldS .X0 .X8)
sym_block run_b5 := exec b5 prevS
sym_block run_b6 := exec b6 (ldS .X2 .X12)
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 (ldS .X2 .X9)
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 (ldS .X2 .X12)
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 swapS
sym_block run_b16 := exec b16 regsS
sym_block run_b18 := exec b18 regsS

public theorem b15_facts : (∀ w ∈ (after b15 swapS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b15 swapS).mem = some (.reg .X9, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b15 swapS).mem = some (.reg .X12, i)) := by
  decide +kernel

end NativeRustcVmArm.Layout.InsertionSort
