module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement
public meta import NativeRustcVmX64.Code.Vm.LayoutWPlacement
public meta import NativeRustcVmX64.Layout.Common

/-!
# `LayoutW::placement`'s blocks, run by the symbolic executor (x86-64)

`entryS`, at the entry: region 0 the `144` bytes of the layout from `entryAddr = rdi + 8 (rsi +
2 rsi)` (the column's `PlacementAt` at their offset `120`). `b0` loads `present` and branches to
`b2` (`0`: returns zeros) or falls to `b1` (returns the variable count and the index). The `ret`s
run from `retS`.
-/

namespace NativeRustcVmX64.Layout.LayoutWPlacement

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LayoutWPlacement
open NativeRustcVmX64.Transcript (after after_eq exec_after EpiOk)

@[expose] public section

/-- `3 rsi`, as `leaq (%rsi,%rsi,2)` computes it. -/
def raxS : Sym := .bin .add .W64 (.reg .rsi) (.bin .mul .W64 (.reg .rsi) (.lit 2))

/-- `rdi + 8 rax`, the column's entry minus `120`. -/
def entryAddr : Sym := .bin .add .W64 (.reg .rdi) (.bin .mul .W64 raxS (.lit 8))

/-- `120 + entryAddr`, as `addq $120, %rcx` leaves it: the column's entry. -/
def rcxS : Sym := .bin .add .W64 (.lit 120) entryAddr

/-- At the entry: region 0 from `entryAddr`. -/
def entryS : SState := init [144] [] [] [] [(entryAddr, 0, 0), (rcxS, 0, 120)]

/-- `b1` but its `ret`. -/
def b1a : List Directive := b1.take 4

/-- `b1`'s `ret`. -/
def b1r : List Directive := b1.drop 4

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1a := exec b1a (after b0 entryS)
sym_block run_b1r := exec b1r retS
sym_block run_b2 := exec b2 retS

public theorem ok_b0 : keeps entryS (after b0 entryS) = true ∧ (after b0 entryS).mem = [] ∧
    (after b0 entryS).reg .rsp = some (.reg .rsp) := by
  decide +kernel

public theorem ok_b1a : keeps entryS (after b1a (after b0 entryS)) = true ∧
    (after b1a (after b0 entryS)).mem = [] ∧
    (after b1a (after b0 entryS)).reg .rsp = some (.reg .rsp) ∧
    (after b1a (after b0 entryS)).reg .rax = some (.load 0 128 8) ∧
    (after b1a (after b0 entryS)).reg .rdx = some (.load 0 136 8) := by
  decide +kernel

public theorem ok_b1r : EpiOk 0 [] (after b1r retS) = true ∧ (after b1r retS).mem = [] ∧
    (after b1r retS).reg .rax = some (.reg .rax) ∧ (after b1r retS).reg .rdx = some (.reg .rdx) := by
  decide +kernel

public theorem ok_b2 : EpiOk 0 [] (after b2 retS) = true ∧ (after b2 retS).mem = [] ∧
    (after b2 retS).reg .rax = some (.lit 0) ∧ (after b2 retS).reg .rdx = some (.lit 0) := by
  decide +kernel

end NativeRustcVmX64.Layout.LayoutWPlacement
