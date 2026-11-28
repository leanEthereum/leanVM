module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes
public meta import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `read_announced_sizes`' blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`: the prologue, `announced` zeroed, the call of `read_scalars`):
  region 0 the 208-byte frame below SP;
- `frS`, after the call (`b1`-`b12`, `b14`-`b16`): region 0 the frame, SP its base; `announced`
  at `0` (eight elements), the rows `b10` copies at `128`, the slots from `176`;
- `layS`, `b13`: region 0 the layout's first 24 bytes (X19), its `stack_log` at `16`.
-/

namespace NativeRustcVmArm.Layout.ReadAnnouncedSizes

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadAnnouncedSizes
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll restores)

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(208, true)] (.ptr 0 208)
/-- In the body: the frame, SP its base. -/
def frS : SState := init [(208, true)] (.ptr 0 0)
/-- `b13`: the layout's first 24 bytes. -/
def layS : SState := init [(24, false)] .sp [] [] [] [(.reg .X19, 0, 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(176, .X30), (184, .X21), (192, .X20), (200, .X19)]

/-- The registers the body keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 layS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 208 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 208) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem keeps_b1_b9 :
    keepsAll frS { after b1 frS with mem := [] } keptRegs = true ∧ (after b1 frS).mem = [] ∧
    keepsAll frS { after b2 frS with mem := [] } keptRegs = true ∧ (after b2 frS).mem = [] ∧
    keepsAll frS { after b3 frS with mem := [] } keptRegs = true ∧ (after b3 frS).mem = [] ∧
    keepsAll frS { after b4 frS with mem := [] } keptRegs = true ∧ (after b4 frS).mem = [] ∧
    keepsAll frS { after b5 frS with mem := [] } keptRegs = true ∧ (after b5 frS).mem = [] ∧
    keepsAll frS { after b6 frS with mem := [] } keptRegs = true ∧ (after b6 frS).mem = [] ∧
    keepsAll frS { after b7 frS with mem := [] } keptRegs = true ∧ (after b7 frS).mem = [] ∧
    keepsAll frS { after b8 frS with mem := [] } keptRegs = true ∧ (after b8 frS).mem = [] ∧
    keepsAll frS { after b9 frS with mem := [] } keptRegs = true ∧ (after b9 frS).mem = [] ∧
    keepsAll frS { after b11 frS with mem := [] } keptRegs = true ∧ (after b11 frS).mem = [] ∧
    keepsAll frS { after b12 frS with mem := [] } keptRegs = true ∧ (after b12 frS).mem = [] := by
  decide +kernel

public theorem b10_facts : keepsAll frS { after b10 frS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b10 frS).mem, w.r = 0 ∧ 128 ≤ w.off ∧ w.off + w.n ≤ 176) ∧
    (∀ t < 6, ∀ i < 8, findWrite 0 (128 + 8 * t + i) (after b10 frS).mem =
      some (.load 0 (16 * (t + 1)) 8, i)) := by
  decide +kernel

public theorem b13_keeps : keepsAll layS { after b13 layS with mem := [] } keptRegs = true ∧
    (after b13 layS).mem = [] := by decide +kernel

public theorem restores_b14_b16 : restores slots 208 (after b14 frS) = true ∧
    (after b14 frS).mem = [] ∧ restores slots 208 (after b15 frS) = true ∧
    (after b15 frS).mem = [] ∧ restores slots 208 (after b16 frS) = true ∧
    (after b16 frS).mem = [] := by decide +kernel

/-- `b0`'s arguments of `read_scalars`: X0 the `TState`, X1 the frame, X2 `8`; X19 the layout, X20
the bytecode's length. -/
public theorem b0_regs : (after b0 entryS).sp = .ptr 0 0 ∧
    (after b0 entryS).reg .X0 = some (.reg .X0) ∧ (after b0 entryS).reg .X1 = some (.ptr 0 0) ∧
    (after b0 entryS).reg .X2 = some (.lit 8) ∧ (after b0 entryS).reg .X19 = some (.reg .X2) ∧
    (after b0 entryS).reg .X20 = some (.reg .X1) := by decide +kernel

/-- `b10`: X1 `announced[0]`'s low limb, X21 `announced[7]`'s; X0, X19, X20 kept. -/
public theorem b10_regs : (after b10 frS).reg .X1 = some (.load 0 0 8) ∧
    (after b10 frS).reg .X21 = some (.load 0 112 8) ∧
    ([XReg.X0, .X19, .X20].all fun r ↦ (frS.reg r).isSome && (after b10 frS).reg r == frS.reg r) =
      true := by decide +kernel

/-- `b11`'s arguments of `build_layout`: X0 the bytecode's length, X2 the rows, X3 the layout. -/
public theorem b11_regs : (after b11 frS).reg .X0 = some (.reg .X20) ∧
    (after b11 frS).reg .X2 = some (.ptr 0 128) ∧ (after b11 frS).reg .X3 = some (.reg .X19) ∧
    ([XReg.X1, .X19, .X20, .X21].all fun r ↦
      (frS.reg r).isSome && (after b11 frS).reg r == frS.reg r) = true := by decide +kernel

/-- `b12`, `b13` keep X21 (and `b12` X0, X19). -/
public theorem b12_b13_regs :
    ([XReg.X0, .X19, .X21].all fun r ↦ (frS.reg r).isSome && (after b12 frS).reg r == frS.reg r) =
      true ∧
    ([XReg.X21].all fun r ↦ (layS.reg r).isSome && (after b13 layS).reg r == layS.reg r) = true ∧
    (after b13 layS).reg .X0 = some (.ite (SBool.cmp .ult .W64
      (.bin .sub .W64 (.load 0 16 8) (.lit 16)) (.lit 15)).not (.lit 0) (.lit 1)) := by
  decide +kernel

/-- `b14` returns X0 and X21 (the rate) in X1. -/
public theorem b14_regs : (after b14 frS).reg .X0 = some (.reg .X0) ∧
    (after b14 frS).reg .X1 = some (.reg .X21) := by decide +kernel

end NativeRustcVmArm.Layout.ReadAnnouncedSizes
