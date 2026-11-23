module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.StackPoint
public meta import NativeRustcVmX64.Code.Vm.StackPoint
public meta import NativeRustcVmX64.Layout.Common

/-!
# `stack_point`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the five pushes (offsets `8`-`48`; the
last, RAX, a scratch slot), the call's return-address slot at `0`, the return address above.
- `entryS` at the entry (`b0`, the prologue and the length check);
- `Field.midS 48` at the blocks without memory but the frame (`b1`-`b4`, `b6`, `b8`, `b9`, `b10`);
- `pairS` at the pair loop `.L5` (`b5`): `out[i]`, `out[i + 1]` (region 1, R9 + R14 at its offset
  `24`), `point[i]`, `point[i + 1]` (region 2, RDX + R14 at its offset `24`);
- `oneS` at `.L7` after the shift (`b7b`): `out[i]` (region 1, R9 + R10), `point[i]` (region 2,
  RDX + R10).
-/

namespace NativeRustcVmX64.Layout.StackPoint

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.StackPoint NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (after freeRegs keepsAll keepsRegs restores)

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48

/-- At `.L5`: the frame, `out[i..i+2]` (R9 + R14 at offset `24`), `point[i..i+2]`. -/
def pairS : SState :=
  init [56, 32, 32] [(.rsp, .ptr 0 8)] [] []
    [(.bin .add .W64 (.reg .r9) (.reg .r14), 1, 24), (.bin .add .W64 (.reg .rdx) (.reg .r14), 2, 24)]

/-- At `.L7` after the shift: the frame, `out[i]` (R9 + R10), `point[i]` (RDX + R10). -/
def oneS : SState :=
  init [56, 16, 16] [(.rsp, .ptr 0 8)] [] []
    [(.bin .add .W64 (.reg .r9) (.reg .r10), 1, 0), (.bin .add .W64 (.reg .rdx) (.reg .r10), 2, 0)]

/-- `b7`'s shift. -/
def b7a : List Directive := b7.take 2
/-- `b7`'s copy. -/
def b7b : List Directive := b7.drop 2

/-- The pushed callee-saved registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (midS 48)
sym_block run_b2 := exec b2 (midS 48)
sym_block run_b3 := exec b3 (midS 48)
sym_block run_b4 := exec b4 (midS 48)
sym_block run_b5 := exec b5 pairS
sym_block run_b6 := exec b6 (midS 48)
sym_block run_b7a := exec b7a (midS 48)
sym_block run_b7b := exec b7b oneS
sym_block run_b8 := exec b8 (midS 48)
sym_block run_b9 := exec b9 (midS 48)
sym_block run_b10 := exec b10 (midS 48)

/-- `stack_point`'s tail length: `stack_log - vc`, `0` below. -/
@[expose] public def tlS : Sym :=
  .ite (.cmp .ult .W64 (.reg .r8) (.reg .rdi)) (.lit 0) (.bin .sub .W64 (.reg .r8) (.reg .rdi))

/-- The stack point's length. -/
@[expose] public def nS : Sym := .bin .add .W64 tlS (.reg .rcx)

/-- `b0`'s check: the length does not wrap and is below `67`. -/
@[expose] public def okS : SBool :=
  .cmp .eq .W8 (.bin .or .W8
    (.bin .merge .W8 (.reg .r11) (.ite (.not (.cmp .ult .W64 nS (.lit 67))) (.lit 1) (.lit 0)))
    (.bin .merge .W8 (.reg .r10) (.ite (.cmp .ult .W64 nS (.reg .rcx)) (.lit 1) (.lit 0)))) (.lit 0)

public theorem b0_facts : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b0 entryS).reg .rsp = some (.ptr 0 8) ∧
    keepsRegs entryS (after b0 entryS) [.rcx, .rdx, .rsi, .rdi, .r9] = true ∧
    (after b0 entryS).reg .r8 = some tlS ∧ (after b0 entryS).reg .rbx = some nS ∧
    (after b0 entryS).reg .rax = some (.lit 0) ∧ (after b0 entryS).flags.zf = some okS := by
  decide +kernel

/-- The registers the body keeps. -/
@[expose] public def keepB : List Reg64 := [.rcx, .rdx, .rsi, .rdi, .r8, .r9, .rbx]

public theorem b1_facts : keepsAll (midS 48) (after b1 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b1 (midS 48)) keepB = true ∧
    (after b1 (midS 48)).reg .rax = some (.bin .add .W64 (.reg .r9) (.bin .shl .W64 (.reg .rcx) (.lit 4))) ∧
    (after b1 (midS 48)).flags.zf = some (.cmp .eq .W64 (.bin .and .W64 (.reg .rcx) (.reg .rcx)) (.lit 0)) := by
  decide +kernel

/-- The registers the copy keeps. -/
@[expose] public def keepC : List Reg64 := keepB ++ [.rax]

public theorem b2_facts : keepsAll (midS 48) (after b2 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b2 (midS 48)) keepC = true ∧
    (after b2 (midS 48)).flags.zf = some (.cmp .eq .W64 (.reg .rcx) (.lit 1)) := by
  decide +kernel

public theorem b3_facts : keepsAll (midS 48) (after b3 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b3 (midS 48)) keepC = true ∧
    (after b3 (midS 48)).reg .r10 = some (.lit 0) := by
  decide +kernel

public theorem b4_facts : keepsAll (midS 48) (after b4 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b4 (midS 48)) keepC = true ∧
    (after b4 (midS 48)).reg .r11 = some (.bin .and .W32 (.un .trunc .W32 (.reg .rcx)) (.lit 62)) ∧
    (after b4 (midS 48)).reg .r14 = some (.lit 24) ∧ (after b4 (midS 48)).reg .r10 = some (.lit 0) := by
  decide +kernel

public theorem b5_facts : keepsRegs pairS (after b5 pairS) (.rsp :: freeRegs slots) = true ∧
    keepsRegs pairS (after b5 pairS) (keepC ++ [.r11]) = true ∧
    (∀ w ∈ (after b5 pairS).mem, w.r = 1 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b5 pairS).mem = some (.load 2 0 8, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b5 pairS).mem = some (.load 2 (0 + 8) 8, i)) ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b5 pairS).mem = some (.load 2 16 8, i)) ∧
    (∀ i < 8, findWrite 1 (16 + 8 + i) (after b5 pairS).mem = some (.load 2 (16 + 8) 8, i)) ∧
    (after b5 pairS).reg .r14 = some (.bin .add .W64 (.lit 32) (.reg .r14)) ∧
    (after b5 pairS).reg .r10 = some (.bin .add .W64 (.lit 2) (.reg .r10)) ∧
    (after b5 pairS).flags.zf = some (.cmp .eq .W64 (.reg .r11) (.bin .add .W64 (.lit 2) (.reg .r10))) := by
  decide +kernel

public theorem b6_facts : keepsAll (midS 48) (after b6 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b6 (midS 48)) (keepC ++ [.r10]) = true ∧
    (after b6 (midS 48)).flags.zf = some (.cmp .eq .W8 (.bin .and .W8 (.reg .rcx) (.lit 1)) (.lit 0)) := by
  decide +kernel

public theorem b7a_facts : keepsAll (midS 48) (after b7a (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b7a (midS 48)) keepC = true ∧
    (after b7a (midS 48)).reg .r10 = some (.bin .shl .W64 (.reg .r10) (.lit 4)) := by
  decide +kernel

public theorem b7b_facts : keepsRegs oneS (after b7b oneS) (.rsp :: freeRegs slots) = true ∧
    keepsRegs oneS (after b7b oneS) [.rsi, .rdi, .r8, .r9, .rbx, .rax] = true ∧
    (∀ w ∈ (after b7b oneS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b7b oneS).mem = some (.load 2 0 8, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b7b oneS).mem = some (.load 2 (0 + 8) 8, i)) := by
  decide +kernel

public theorem b8_call : keepsRegs (midS 48) (after b8 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b8 (midS 48)) [.rbx] = true ∧
    (after b8 (midS 48)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b8 (midS 48)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b8 (midS 48)).reg .rdi = some (.ite (.cmp .ult .W64 (.reg .rdi) (.lit 64))
      (.bin .shr .W64 (.reg .rsi) (.un .trunc .W32 (.reg .rdi))) (.lit 0)) ∧
    (after b8 (midS 48)).reg .rsi = some (.reg .rax) ∧
    (after b8 (midS 48)).reg .rdx = some (.reg .r8) := by
  decide +kernel

public theorem b9_facts : keepsAll (midS 48) (after b9 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b9 (midS 48)) [.rbx] = true ∧
    (after b9 (midS 48)).reg .rax = some (.lit 1) := by
  decide +kernel

public theorem b10_restores : restores slots 48 (after b10 (midS 48)) = true ∧
    (after b10 (midS 48)).mem = [] ∧ (after b10 (midS 48)).reg .rax = some (.reg .rax) ∧
    (after b10 (midS 48)).reg .rdx = some (.reg .rbx) := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide

end NativeRustcVmX64.Layout.StackPoint
