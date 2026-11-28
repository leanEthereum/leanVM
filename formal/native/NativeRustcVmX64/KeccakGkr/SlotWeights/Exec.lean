module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SlotWeights
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names
public meta import NativeRustcVmX64.Code.Vm.SlotWeights
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `slot_weights`' blocks, run by the symbolic executor (x86-64)

Region 0 the 160-byte frame (RBP to RBX pushed at offsets `152` to `112`, the locals from `8`:
the segment loop's counter at `32`, `count` at `24`, `first` at `16`, the weights' address at
`40`, the four segments at `48`, `eq_kernel`'s result at `8`; a callee's return address at `0`)
and the return address; the rows' address, the stack argument, region 1 (reached as
`160(%rsp)`: the frame offset `168` is an alias of region 1's base). From `entryS`: `b0` (the
prologue, `call eq_kernel`). From `callS`: `b1` (its result), `b2` (the rows' cursor), `b8` (the
segment loop's test), `b15` (the epilogue), and the blocks without memory accesses `b3`, `b5`,
`b6`, `b11`, `b12` (`b7`, `b10` are alignment only). The zeroing loop's body `b4` from `zeroS`
(region 1 the 64 bytes it zeroes, `RAX + RDX` an alias of its base plus `56`); a segment's start
`b9` from `segS` (its offset `16 RCX` at most `16`); the weight's load and `call EW::mul` `b13`
from `mulS` (region 1 the weight, `[RSP + 40] + RBX` its alias); the product's store, `b14`, in two
parts: `p1` (the row's address, the element's offset) from `callS`, `p2` (the stores) from
`storeS` (region 1 the element, `RCX + R12` its alias).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SlotWeights NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- At the entry. -/
def entryS : SState := init [168, 8] [(.rsp, .ptr 0 160)] [] [] [(.ptr 0 168, 1, 0)]
/-- In the body: RSP at offset `8`, region 1 the rows' address. -/
def callS : SState := init [168, 8] [(.rsp, .ptr 0 8)] [] [] [(.ptr 0 168, 1, 0)]
/-- The zeroing loop's body: region 1 the 64 bytes at `RAX + RDX - 56`. -/
def zeroS : SState :=
  init [168, 64] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .rax) (.reg .rdx), 1, 56)]
/-- A segment's start: the segment's offset `16 RCX` at most `16`. -/
def segS : SState :=
  init [168, 8] [(.rsp, .ptr 0 8)] [] [(.bin .shl .W64 (.reg .rcx) (.lit 4), 17)]
    [(.ptr 0 168, 1, 0)]
/-- The weight's load: region 1 the weight at `RAX + RBX`. -/
def mulS : SState :=
  init [168, 16] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.load 0 40 8) (.reg .rbx), 1, 0)]
/-- The product's stores: region 1 the element at `RCX + R12`. -/
def storeS : SState :=
  init [168, 16] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .rcx) (.reg .r12), 1, 0)]

/-- rustc's `logSteps.saturating_sub(4)`. -/
def packS : Sym :=
  .ite (.cmp .ult .W64 (.reg .rdi) (.lit 4)) (.lit 0) (.bin .sub .W64 (.reg .rdi) (.lit 4))

/-- The address of the point's segment coordinates. -/
def ptrS : Sym :=
  .ite (SBool.cmp .ult .W64 (.reg .rdx) packS).not
    (.bin .add .W64 (.reg .rsi) (.bin .shl .W64 packS (.lit 4))) (.lit 8)

/-- The number of the point's segment coordinates. -/
def lenS : Sym :=
  .ite (SBool.cmp .ult .W64 (.reg .rdx) packS).not (.bin .sub .W64 (.reg .rdx) packS) (.lit 0)

/-- The row of a product: `25 (first + segment) + j / 64`. -/
def rowS : Sym :=
  .bin .add .W64 (.reg .r14) (.bin .shr .W64 (.reg .r15) (.lit 6))

/-- `25 (first + segment)`, as `b9` computes it. -/
def r14S : Sym :=
  let a := Sym.bin .add .W64 (.reg .rcx) (.load 0 16 8)
  let b := Sym.bin .add .W64 a (.bin .mul .W64 a (.lit 4))
  .bin .add .W64 b (.bin .mul .W64 b (.lit 4))

/-- The element's offset in its row, as `b14` computes it. -/
def colS : Sym :=
  .bin .shl .W32 (.bin .and .W32 (.un .trunc .W32 (.reg .r15)) (.lit 63)) (.lit 4)

/-- `b14`'s first part: the row's address, the element's offset. -/
def p1 : List Directive := b14.take 5
/-- `b14`'s second part: the stores. -/
def p2 : List Directive := b14.drop 5

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 callS
sym_block e2 := exec b2 callS
sym_block e3 := exec b3 callS
sym_block e4 := exec b4 zeroS
sym_block e5 := exec b5 callS
sym_block e6 := exec b6 callS
sym_block e8 := exec b8 callS
sym_block e9 := exec b9 segS
sym_block e11 := exec b11 callS
sym_block e12 := exec b12 callS
sym_block e13 := exec b13 mulS
sym_block ep1 := exec p1 callS
sym_block ep2 := exec p2 storeS
sym_block e15 := exec b15 callS

public section

theorem p1_length : p1.length = 5 := by decide +kernel

/-- The prologue: the slots pushed, `first`, `count`, the weights' address saved, `eq_kernel`'s
arguments. -/
theorem ok_b0 : ProOk 160 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 160) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b0 entryS).mem = some (.reg .r8, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b0 entryS).mem = some (.reg .r9, i)) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b0 entryS).mem = some (.reg .rcx, i)) ∧
    (after b0 entryS).reg .rdi = some ptrS ∧ (after b0 entryS).reg .rsi = some lenS ∧
    (after b0 entryS).reg .rdx = some (.ptr 0 48) ∧ (after b0 entryS).reg .rcx = some (.lit 4) := by
  rw [after_eq e0]; decide +kernel

theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.EqKernel.entryLabel) := e0.trans (by rw [after_eq e0])

/-- `eq_kernel`'s result stored at `8`. -/
theorem ok_b1 : MidOk 160 8 slots (after b1 callS) = true ∧
    (∀ w ∈ (after b1 callS).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b1 callS).mem = some (.reg .rax, i)) := by
  rw [after_eq e1]; decide +kernel

theorem exit_b1 : exec b1 callS = some (after b1 callS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.SlotWeights.label_11) :=
  e1.trans (by rw [after_eq e1])

theorem ok_b2 : MidOk 160 8 slots (after b2 callS) = true ∧ (after b2 callS).mem = [] ∧
    (after b2 callS).reg .rax = some (.bin .add .W64 (.lit 56) (.load 1 0 8)) ∧
    (after b2 callS).reg .rcx = some (.lit 0) := by
  rw [after_eq e2]; decide +kernel

theorem exit_b2 : exec b2 callS = some (after b2 callS, .fall) := e2.trans (by rw [after_eq e2])

theorem ok_b3 : MidOk 160 8 slots (after b3 callS) = true ∧ (after b3 callS).mem = [] ∧
    (after b3 callS).reg .rax = some (.reg .rax) ∧
    (after b3 callS).reg .rcx = some (.reg .rcx) ∧ (after b3 callS).reg .rdx = some (.lit 0) := by
  rw [after_eq e3]; decide +kernel

theorem exit_b3 : exec b3 callS = some (after b3 callS, .fall) := e3.trans (by rw [after_eq e3])

/-- The zeroing loop's body: four zero elements. -/
theorem ok_b4 : MidOk 160 8 slots (after b4 zeroS) = true ∧
    (after b4 zeroS).reg .rax = some (.reg .rax) ∧
    (after b4 zeroS).reg .rcx = some (.reg .rcx) ∧
    (after b4 zeroS).reg .rdx = some (.bin .add .W64 (.lit 64) (.reg .rdx)) ∧
    (∀ w ∈ (after b4 zeroS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    (∀ e < 4, ∀ t < 8, findWrite 1 (16 * e + t) (after b4 zeroS).mem = some (.lit 0, t) ∧
      findWrite 1 (16 * e + 8 + t) (after b4 zeroS).mem = some (.lit 0, t)) := by
  rw [after_eq e4]; decide +kernel

theorem exit_b4 : exec b4 zeroS = some (after b4 zeroS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 64) (.reg .rdx)) (.lit 1024)).not
      NativeRustcVmX64.Vm.SlotWeights.label_3) := e4.trans (by rw [after_eq e4])

theorem ok_b5 : MidOk 160 8 slots (after b5 callS) = true ∧ (after b5 callS).mem = [] ∧
    (after b5 callS).reg .rax = some (.bin .add .W64 (.lit 1024) (.reg .rax)) ∧
    (after b5 callS).reg .rcx = some (.bin .add .W64 (.lit 1024) (.reg .rcx)) := by
  rw [after_eq e5]; decide +kernel

theorem exit_b5 : exec b5 callS = some (after b5 callS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 1024) (.reg .rcx)) (.lit 65536)).not
      NativeRustcVmX64.Vm.SlotWeights.label_2) := e5.trans (by rw [after_eq e5])

theorem ok_b6 : MidOk 160 8 slots (after b6 callS) = true ∧ (after b6 callS).mem = [] ∧
    (after b6 callS).reg .rcx = some (.lit 0) := by
  rw [after_eq e6]; decide +kernel

theorem exit_b6 : exec b6 callS = some (after b6 callS, .jump NativeRustcVmX64.Vm.SlotWeights.label_7) :=
  e6.trans (by rw [after_eq e6])

theorem ok_b8 : MidOk 160 8 slots (after b8 callS) = true ∧ (after b8 callS).mem = [] ∧
    (after b8 callS).reg .rcx = some (.bin .add .W64 (.load 0 32 8) (.lit 1)) := by
  rw [after_eq e8]; decide +kernel

theorem exit_b8 : exec b8 callS = some (after b8 callS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.load 0 32 8) (.lit 1)) (.load 0 24 8))
      NativeRustcVmX64.Vm.SlotWeights.label_11) := e8.trans (by rw [after_eq e8])

/-- A segment's start: its scale, the row base, the counters, the segment saved at `32`. -/
theorem ok_b9 : MidOk 160 8 slots (after b9 segS) = true ∧
    (∀ w ∈ (after b9 segS).mem, w.r = 0 ∧ 32 ≤ w.off ∧ w.off + w.n ≤ 40) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b9 segS).mem = some (.reg .rcx, i)) ∧
    (after b9 segS).reg .r13 = some (.loadx 0 48 (.bin .shl .W64 (.reg .rcx) (.lit 4)) 8) ∧
    (after b9 segS).reg .rbp = some (.loadx 0 56 (.bin .shl .W64 (.reg .rcx) (.lit 4)) 8) ∧
    (after b9 segS).reg .r14 = some r14S ∧ (after b9 segS).reg .r15 = some (.lit 0) ∧
    (after b9 segS).reg .rbx = some (.lit 0) := by
  rw [after_eq e9]; decide +kernel

theorem exit_b9 : exec b9 segS = some (after b9 segS, .jump NativeRustcVmX64.Vm.SlotWeights.label_8) :=
  e9.trans (by rw [after_eq e9])

theorem ok_b11 : MidOk 160 8 slots (after b11 callS) = true ∧ (after b11 callS).mem = [] ∧
    (after b11 callS).reg .rbx = some (.bin .add .W64 (.lit 16) (.reg .rbx)) ∧
    (after b11 callS).reg .r15 = some (.bin .add .W64 (.reg .r15) (.lit 1)) ∧
    (after b11 callS).reg .r13 = some (.reg .r13) ∧ (after b11 callS).reg .rbp = some (.reg .rbp) ∧
    (after b11 callS).reg .r14 = some (.reg .r14) := by
  rw [after_eq e11]; decide +kernel

theorem exit_b11 : exec b11 callS = some (after b11 callS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rbx)) (.lit 25600))
      NativeRustcVmX64.Vm.SlotWeights.label_6) := e11.trans (by rw [after_eq e11])

theorem ok_b12 : MidOk 160 8 slots (after b12 callS) = true ∧ (after b12 callS).mem = [] ∧
    (after b12 callS).reg .r12 = some rowS ∧
    (after b12 callS).reg .r13 = some (.reg .r13) ∧ (after b12 callS).reg .rbp = some (.reg .rbp) ∧
    (after b12 callS).reg .r14 = some (.reg .r14) ∧ (after b12 callS).reg .r15 = some (.reg .r15) ∧
    (after b12 callS).reg .rbx = some (.reg .rbx) := by
  rw [after_eq e12]; decide +kernel

theorem exit_b12 : exec b12 callS = some (after b12 callS,
    .cond ((SBool.cmp .ult .W64 rowS (.lit 63)).not.and (SBool.cmp .eq .W64 rowS (.lit 63)).not)
      NativeRustcVmX64.Vm.SlotWeights.label_10) := e12.trans (by rw [after_eq e12]; rfl)

/-- The weight's load and the call of `EW::mul`. -/
theorem ok_b13 : MidOk 160 0 slots (after b13 mulS) = true ∧
    (∀ w ∈ (after b13 mulS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b13 mulS).reg .rdi = some (.reg .r13) ∧ (after b13 mulS).reg .rsi = some (.reg .rbp) ∧
    (after b13 mulS).reg .rdx = some (.load 1 0 8) ∧ (after b13 mulS).reg .rcx = some (.load 1 8 8) ∧
    (after b13 mulS).reg .r12 = some (.reg .r12) ∧ (after b13 mulS).reg .r13 = some (.reg .r13) ∧
    (after b13 mulS).reg .rbp = some (.reg .rbp) ∧ (after b13 mulS).reg .r14 = some (.reg .r14) ∧
    (after b13 mulS).reg .r15 = some (.reg .r15) ∧ (after b13 mulS).reg .rbx = some (.reg .rbx) := by
  rw [after_eq e13]; decide +kernel

theorem exit_b13 : exec b13 mulS = some (after b13 mulS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := e13.trans (by rw [after_eq e13])

theorem ok_p1 : MidOk 160 8 slots (after p1 callS) = true ∧ (after p1 callS).mem = [] ∧
    (after p1 callS).reg .rcx = some colS ∧
    (after p1 callS).reg .r12 =
      some (.bin .add .W64 (.load 1 0 8) (.bin .shl .W64 (.reg .r12) (.lit 10))) ∧
    (after p1 callS).reg .rax = some (.reg .rax) ∧ (after p1 callS).reg .rdx = some (.reg .rdx) ∧
    (after p1 callS).reg .r13 = some (.reg .r13) ∧ (after p1 callS).reg .rbp = some (.reg .rbp) ∧
    (after p1 callS).reg .r14 = some (.reg .r14) ∧ (after p1 callS).reg .r15 = some (.reg .r15) ∧
    (after p1 callS).reg .rbx = some (.reg .rbx) := by
  rw [after_eq ep1]; decide +kernel

theorem exit_p1 : exec p1 callS = some (after p1 callS, .fall) := ep1.trans (by rw [after_eq ep1])

theorem ok_p2 : MidOk 160 8 slots (after p2 storeS) = true ∧
    (after p2 storeS).reg .r13 = some (.reg .r13) ∧ (after p2 storeS).reg .rbp = some (.reg .rbp) ∧
    (after p2 storeS).reg .r14 = some (.reg .r14) ∧ (after p2 storeS).reg .r15 = some (.reg .r15) ∧
    (after p2 storeS).reg .rbx = some (.reg .rbx) ∧
    (∀ w ∈ (after p2 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after p2 storeS).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 1 (0 + 8 + t) (after p2 storeS).mem = some (.reg .rdx, t)) := by
  rw [after_eq ep2]; decide +kernel

theorem exit_p2 : exec p2 storeS = some (after p2 storeS, .jump NativeRustcVmX64.Vm.SlotWeights.label_10) :=
  ep2.trans (by rw [after_eq ep2])

/-- The epilogue: AL the low bit of `eq_kernel`'s result. -/
theorem ok_b15 : EpiOk 160 slots (after b15 callS) = true ∧ (after b15 callS).mem = [] ∧
    (after b15 callS).reg .rax =
      some (.bin .merge .W8 (.load 0 8 8) (.bin .and .W8 (.load 0 8 8) (.lit 1))) := by
  rw [after_eq e15]; decide +kernel

theorem exit_b15 : exec b15 callS = some (after b15 callS, .ret (.load 0 160 8)) :=
  e15.trans (by rw [after_eq e15])

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
