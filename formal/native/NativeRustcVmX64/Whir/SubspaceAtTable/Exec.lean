module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable
public meta import NativeRustcVmX64.Code.Vm.SubspaceAtTable
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `subspace_at_table`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 336-byte frame (`Field.frameS 336`, `Field.midS 336`: the pushes from offset 288,
the 280 bytes of locals, the calls' return-address slot at 0) and the return address. From RSP
(offset `8`): the count at `8(%rsp)` (offset 16), the output pointer at `16(%rsp)` (24), the `what`
buffer (`len` at 32, 31 items from 40).
- `b0a` (`entryS`): the prologue; `b0b` (`gotMidS 336 "memset"`): the arguments and the slot-backed call zeroing the items;
- `b1`, `b2` (`midS`): the count's store and test, the loop's registers;
- the loop: `b3` (`ldS`: region 1 the table's pair at `r15 + 2·r14`) calls `kmul` (`What_i`);
  `b4a` (`stS`: region 0 the item `32 + rsp + r14` points to) stores it; `b4b`, `b5` (`midS`)
  call `kmul` (`W²`, `root·W`); `b6` (`regsS`) takes the next `W`, counts;
- `b7` (`gotMidS 336 "memcpy"`) stores the count in the buffer and calls through its GOT slot; `b8` is the epilogue.
-/

namespace NativeRustcVmX64.Whir.SubspaceAtTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceAtTable NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs keepsAll freeRegs restores)

@[expose] public section

/-- The pair's address in `b3`: `r15 + 2·r14`. -/
def ldAddr : Sym := .bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg .r14) (.lit 2))
/-- The item's address in `b4a`: `rsp + r14 + 32`. -/
def stAddr : Sym := .bin .add .W64 (.bin .add .W64 (.reg .rsp) (.reg .r14)) (.lit 32)

/-- At the entry. -/
abbrev entryS : SState := frameS 336
/-- At the loop head: the frame, the pair (region 1). -/
def ldS : SState := init [344, 16] [(.rsp, .ptr 0 8)] [] [] [(ldAddr, 1, 0)]
/-- At `b4a`: the item (region 0). -/
def stS : SState := init [8] [] [] [] [(stAddr, 0, 0)]
/-- Registers only. -/
def regsS : SState := init []

/-- The prologue. -/
def b0a : List Directive := b0.take 8
/-- The arguments and `memset`. -/
def b0b : List Directive := b0.drop 8
/-- The item's store. -/
def b4a : List Directive := b4.take 1
/-- `kmul(W, W)`. -/
def b4b : List Directive := b4.drop 1

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(328, .rbp), (320, .r15), (312, .r14), (304, .r13), (296, .r12), (288, .rbx)]

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (gotMidS 336 "memset")
sym_block run_b1 := exec b1 (midS 336)
sym_block run_b2 := exec b2 (midS 336)
sym_block run_b3 := exec b3 ldS
sym_block run_b4a := exec b4a stS
sym_block run_b4b := exec b4b (midS 336)
sym_block run_b5 := exec b5 (midS 336)
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 (gotMidS 336 "memcpy")
sym_block run_b8 := exec b8 (midS 336)

public theorem b0a_entry : (∀ p ∈ slots, p.1 + 8 ≤ 336 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0a entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 336) ∧
    (after b0a entryS).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b0b_call : keepsRegs (gotMidS 336 "memset") (after b0b (gotMidS 336 "memset")) (freeRegs slots) = true ∧
    (after b0b (gotMidS 336 "memset")).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b0b (gotMidS 336 "memset")).mem, w.r = 0 ∧ w.off + w.n ≤ 32) := by
  decide +kernel

public theorem b0a_args : ∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx],
    (after b0a entryS).reg r = some (.reg r) := by
  decide +kernel

public theorem b1_write : keepsRegs (midS 336) (after b1 (midS 336)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b1 (midS 336)).mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel

public theorem b2_keeps : keepsAll (midS 336) (after b2 (midS 336)) (freeRegs slots) = true := by
  decide +kernel

public theorem b3_call : keepsRegs ldS (after b3 ldS) (freeRegs slots) = true ∧
    (after b3 ldS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b3 ldS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b4a_write : keepsRegs stS (after b4a stS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b4a stS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b4b_call : keepsRegs (midS 336) (after b4b (midS 336)) (freeRegs slots) = true ∧
    (after b4b (midS 336)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b4b (midS 336)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b5_call : keepsRegs (midS 336) (after b5 (midS 336)) (freeRegs slots) = true ∧
    (after b5 (midS 336)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b5 (midS 336)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b6_keeps : keepsAll regsS (after b6 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b7_call : keepsRegs (gotMidS 336 "memcpy") (after b7 (gotMidS 336 "memcpy")) (freeRegs slots) = true ∧
    (after b7 (gotMidS 336 "memcpy")).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b7 (gotMidS 336 "memcpy")).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 32 ≤ w.off) ∧
      w.off + w.n ≤ 40) := by
  decide +kernel

public theorem b8_restores : restores slots 336 (after b8 (midS 336)) = true ∧
    (after b8 (midS 336)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 288 ≤ p.1 ∧ p.1 + 8 ≤ 336 := by decide

end NativeRustcVmX64.Whir.SubspaceAtTable
