module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.SelectorPoint
public meta import NativeRustcVmX64.Code.Vm.SelectorPoint
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `selector_point`'s blocks, run by the symbolic executor (x86-64)

Region 0 contains the return address and the contract's reserved 16 bytes below RSP
(`Field.frameS 16`). Raw `bt` does not access this region.
- `Field.frameS 16` at the entry (`b0`) and the return without a last entry (`b8`);
- `regsS`, registers only: the tests (`b1`, `b4`), the pair loop's start (`b2`);
- `pairS`, the pair loop (`b3`): region 1 the two entries written, RSI their address;
- `oddS`, the last entry's bit (`b5`): region 0 only;
- `lastS`, the last entry and the return (`b7` `b8`, `b6` `b7` `b8`): region 1 the entry, RSI its
  address.

An entry is `bitSym z`: bit `z` of RDI (the carry of raw `bt`, `setb`) where R8 < 64, else
RCX (zero).
-/

namespace NativeRustcVmX64.Arrays.SelectorPoint

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SelectorPoint NativeRustcVmX64.Field

@[expose] public section

/-- Registers only. -/
def regsS : SState := init []
/-- The pair loop: region 1 the two entries, RSI their address. -/
def pairS : SState := init [24, 32] [(.rsp, .ptr 0 16), (.rsi, .ptr 1 0)]
/-- The last entry's bit. -/
def oddS : SState := init [24] [(.rsp, .ptr 0 16)]
/-- The last entry and the return: region 1 the entry, RSI its address. -/
def lastS : SState := init [24, 16] [(.rsp, .ptr 0 16), (.rsi, .ptr 1 0)]

/-- `setb` after raw `bt` of RDI by `z`. -/
def setbSym (z : Sym) : Sym :=
  .bin .merge .W8 (.lit 0) (.ite (.cmp .bit .W64 (.reg .rdi) z) (.lit 1) (.lit 0))
/-- The pair loop's entry: the bit where R8 < 64, else RCX. -/
def bitSym (z : Sym) : Sym :=
  .ite (.not (.cmp .ult .W64 (.reg .r8) (.lit 64))) (.reg .rcx) (setbSym z)
/-- The first entry's bit index. -/
def z9 : Sym := .reg .r8
/-- The second entry's bit index. -/
def z11 : Sym := .un (.zext .W8) .W32 (.un .trunc .W32 (.bin .add .W64 (.reg .r8) (.lit 1)))

/-- The callee-saved registers and the ones the pair loop keeps. -/
def pairRegs : List Reg64 := [.rax, .rcx, .rdx, .rdi, .rsp] ++ Arrays.calleeRegs

end

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 16)
sym_block run_b8 := exec b8 (frameS 16)
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 pairS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 oddS
sym_block run_b78 := exec (b7 ++ b8) lastS
sym_block run_b678 := exec (b6 ++ b7 ++ b8) lastS

public theorem b0_facts : keepsAll (frameS 16) (after b0 (frameS 16))
    ([.rdx, .rsi, .rdi] ++ Arrays.calleeRegs) = true := by
  decide +kernel

public theorem b8_facts : (after b8 (frameS 16)).reg .rsp = some (.ptr 0 ((16 + 8 : Nat) : Int)) ∧
    (after b8 (frameS 16)).mem = [] ∧
    keepsRegs (frameS 16) (after b8 (frameS 16)) Arrays.calleeRegs = true := by
  decide +kernel

public theorem b1_keeps : keepsAll regsS (after b1 regsS)
    ([.rsi, .rdi] ++ Arrays.calleeRegs) = true := by
  decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS)
    ([.rdx, .rsi, .rdi] ++ Arrays.calleeRegs) = true := by
  decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS)
    ([.rcx, .rdx, .rsi, .rdi, .r8] ++ Arrays.calleeRegs) = true := by
  decide +kernel

public theorem b3_facts : keepsRegs pairS (after b3 pairS) pairRegs = true ∧
    (∀ w ∈ (after b3 pairS).mem, (w.r = 0 ∧ w.off + w.n ≤ 16) ∨ (w.r = 1 ∧ w.off + w.n ≤ 32)) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b3 pairS).mem = some (bitSym z9, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b3 pairS).mem = some (.lit 0, i)) ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b3 pairS).mem = some (bitSym z11, i)) ∧
    (∀ i < 8, findWrite 1 (16 + 8 + i) (after b3 pairS).mem = some (.lit 0, i)) := by
  decide +kernel

public theorem b5_facts : keepsRegs oddS (after b5 oddS) ([.rsi, .rsp] ++ Arrays.calleeRegs) = true ∧
    (∀ w ∈ (after b5 oddS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (after b5 oddS).reg .rdi = some (.ite (.cmp .ult .W64 (.reg .r8) (.lit 64))
      (setbSym z9) (.lit 0)) := by
  decide +kernel

public theorem b78_facts : keepsRegs lastS (after (b7 ++ b8) lastS) Arrays.calleeRegs = true ∧
    (after (b7 ++ b8) lastS).reg .rsp = some (.ptr 0 ((16 + 8 : Nat) : Int)) ∧
    (∀ w ∈ (after (b7 ++ b8) lastS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after (b7 ++ b8) lastS).mem = some (.reg .rdi, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after (b7 ++ b8) lastS).mem = some (.lit 0, i)) := by
  decide +kernel

public theorem b678_facts : keepsRegs lastS (after (b6 ++ b7 ++ b8) lastS) Arrays.calleeRegs = true ∧
    (after (b6 ++ b7 ++ b8) lastS).reg .rsp = some (.ptr 0 ((16 + 8 : Nat) : Int)) ∧
    (∀ w ∈ (after (b6 ++ b7 ++ b8) lastS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after (b6 ++ b7 ++ b8) lastS).mem =
      some (.bin .and .W32 (.reg .rdi) (.lit 1), i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after (b6 ++ b7 ++ b8) lastS).mem = some (.lit 0, i)) := by
  decide +kernel

end NativeRustcVmX64.Arrays.SelectorPoint
