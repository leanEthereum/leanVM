module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.ConstraintsW
public meta import NativeRustcVmX64.Code.Vm.ConstraintsW
public meta import NativeRustcVmX64.Layout.Common

/-!
# `constraints_w`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the five pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1` the prologue or `b5` the return of `0`);
- `rowS n` at `b2`-`b4`: region 0 the row's first `n` bytes (RSI), the blocks run on from it as
  far as the row's length allows (`b2`; `b2`, `b3`; `b2`-`b4`);
- `regsS` at `b6`-`b8`: no region;
- `Field.midS 48` at the calls (`b9`, `b10b`) and the epilogue (`b11b`);
- `outS` at the stores (`b10a`, `b11a`): the frame and `out` (RBX).
-/

namespace NativeRustcVmX64.Layout.ConstraintsW

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ConstraintsW NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (after freeRegs keepsAll keepsRegs restores)

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48
/-- The row's first `n` bytes (region 0, RSI). -/
def rowS (n : Nat) : SState := init [n] [(.rsi, .ptr 0 0)]
/-- Registers only. -/
def regsS : SState := init []
/-- The frame and `out` (region 1, RBX). -/
def outS : SState := init [56, 32] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- `b10`'s stores. -/
def b10a : List Directive := b10.take 4
/-- `b10`'s second product and call. -/
def b10b : List Directive := b10.drop 4
/-- `b11`'s stores. -/
def b11a : List Directive := b11.take 2
/-- `b11`'s epilogue. -/
def b11b : List Directive := b11.drop 2

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r13), (16, .r12), (8, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_b2 := exec b2 (rowS 96)
sym_block run_b2' := exec b2 (rowS 208)
sym_block run_b3 := exec b3 (after b2 (rowS 208))
sym_block run_b2'' := exec b2 (rowS 224)
sym_block run_b3'' := exec b3 (after b2 (rowS 224))
sym_block run_b4 := exec b4 (after b3 (after b2 (rowS 224)))
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 (midS 48)
sym_block run_b10a := exec b10a outS
sym_block run_b10b := exec b10b (midS 48)
sym_block run_b11a := exec b11a outS
sym_block run_b11b := exec b11b (midS 48)

public theorem b0_keeps : (after b0 entryS).mem = [] ∧ (after b0 entryS).reg .rsp = some (.ptr 0 48) ∧
    keeps entryS (after b0 entryS) = true := by
  decide +kernel

public theorem b5_ret : (after b5 (after b0 entryS)).reg .rsp = some (.ptr 0 ((48 + 8 : Nat) : Int)) ∧
    keeps entryS (after b5 (after b0 entryS)) = true ∧ (after b5 (after b0 entryS)).mem = [] ∧
    (after b5 (after b0 entryS)).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) ∧
    (after b1 (after b0 entryS)).reg .rbx = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .rsi = some (.reg .rsi) ∧
    (after b1 (after b0 entryS)).reg .rdx = some (.reg .rdx) := by
  decide +kernel

public theorem b2_keeps : keepsAll (rowS 96) (after b2 (rowS 96)) (freeRegs slots) = true ∧
    (after b2 (rowS 96)).reg .r15 = some (.load 0 80 8) ∧
    (after b2 (rowS 96)).reg .r14 = some (.load 0 88 8) ∧
    (after b2 (rowS 96)).reg .rbx = some (.reg .rbx) := by
  decide +kernel

public theorem b3_keeps : keepsAll (rowS 208) (after b3 (after b2 (rowS 208))) (freeRegs slots) = true ∧
    (after b3 (after b2 (rowS 208))).reg .r15 = some (.load 0 80 8) ∧
    (after b3 (after b2 (rowS 208))).reg .r14 = some (.load 0 88 8) ∧
    (after b3 (after b2 (rowS 208))).reg .rdx = some (.load 0 192 8) ∧
    (after b3 (after b2 (rowS 208))).reg .rcx = some (.load 0 200 8) ∧
    (after b3 (after b2 (rowS 208))).reg .rbx = some (.reg .rbx) := by
  decide +kernel

public theorem b4_keeps : keepsAll (rowS 224) (after b4 (after b3 (after b2 (rowS 224))))
      (freeRegs slots) = true ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .r15 = some (.load 0 80 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .r14 = some (.load 0 88 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .rdx = some (.load 0 192 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .rcx = some (.load 0 200 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .r13 = some (.load 0 208 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .r12 = some (.load 0 216 8) ∧
    (after b4 (after b3 (after b2 (rowS 224)))).reg .rbx = some (.reg .rbx) := by
  decide +kernel

public theorem b6_keeps : keepsAll regsS (after b6 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b7_keeps : keepsAll regsS (after b7 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b9_call : keepsRegs (midS 48) (after b9 (midS 48)) (freeRegs slots) = true ∧
    (after b9 (midS 48)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b9 (midS 48)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b9 (midS 48)).reg .rdi = some (.reg .r15) ∧
    (after b9 (midS 48)).reg .rsi = some (.reg .r14) ∧
    (after b9 (midS 48)).reg .rdx = some (.reg .rdx) ∧
    (after b9 (midS 48)).reg .rcx = some (.reg .rcx) := by
  decide +kernel

public theorem b10a_store : keepsRegs outS (after b10a outS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b10a outS).mem, w.r = 1 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b10a outS).mem =
      some (.bin .xor .W64 (.reg .rax) (.reg .r13), i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b10a outS).mem =
      some (.bin .xor .W64 (.reg .rdx) (.reg .r12), i)) := by
  decide +kernel

public theorem b10b_call : keepsRegs (midS 48) (after b10b (midS 48)) (freeRegs slots) = true ∧
    (after b10b (midS 48)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b10b (midS 48)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b10b (midS 48)).reg .rdi = some (.reg .r15) ∧
    (after b10b (midS 48)).reg .rsi = some (.reg .r14) ∧
    (after b10b (midS 48)).reg .rdx = some (.bin .xor .W64 (.reg .r13) (.lit 1)) ∧
    (after b10b (midS 48)).reg .rcx = some (.reg .r12) := by
  decide +kernel

public theorem b11a_store : keepsRegs outS (after b11a outS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b11a outS).mem, w.r = 1 ∧ w.off + w.n ≤ 32) ∧
    firstOverlap 1 0 16 (after b11a outS).mem = none ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b11a outS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 1 (16 + 8 + i) (after b11a outS).mem = some (.reg .rdx, i)) := by
  decide +kernel

public theorem b11b_restores : restores slots 48 (after b11b (midS 48)) = true ∧
    (after b11b (midS 48)).mem = [] ∧ (after b11b (midS 48)).reg .rax = some (.lit 2) := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide

end NativeRustcVmX64.Layout.ConstraintsW
