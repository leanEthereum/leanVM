module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled
public meta import NativeRustcVmArm.Code.Vm.FormBufAddScaled
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `FormBuf::add_scaled`'s blocks, run by the symbolic executor

- `entryS`, at the entry: region 0 the 48-byte frame below SP. `b0` branches on the count: `0`
  goes to `b7` (returns `1`), else `b1` saves X19-X23 and X30 and sets up the loop (X21 the term,
  X22 the buffer, X20, X19 the weight, X8 `40` times the count less one).
- `termS`, at the loop head `.L2` (`b2`): region 0 the term (X21); its coefficient times the
  weight (`EW::mul`).
- `regsS`: `b3` (the call of `add_term`), `b4` (its result), `b5` (the next term).
- `exitS`, at the epilogue `.L4` (`b6`): region 0 the frame.
-/

namespace NativeRustcVmArm.Layout.FormBufAddScaled

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormBufAddScaled NativeRustcVmArm.Arrays

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)
/-- At the loop head: the term (X21). -/
def termS : SState := init [(40, false)] .sp [(.X21, .ptr 0 0)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(48, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X23), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

/-- The callee-saved registers no slot holds. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b7 := exec b7 (after b0 entryS)
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 termS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b7_keeps : keeps entryS (after b7 (after b0 entryS)) = true ∧
    (after b7 (after b0 entryS)).mem = [] := by decide +kernel

public theorem b2_keeps : keepsAll termS (after b2 termS) keptRegs = true := by decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) keptRegs = true := by decide +kernel
public theorem b6_restores : restores slots 48 (after b6 exitS) = true ∧ (after b6 exitS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Layout.FormBufAddScaled
