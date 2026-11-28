module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.ClimbLevel
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names
public meta import NativeRustcVmX64.Code.Vm.ClimbLevel
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `climb_level`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 208-byte frame and the return address: RBP to RBX pushed at offsets `200` to `160`,
the locals the reader at `40`, the nodes' end at `48`, their address less 40 at `56`, `40 n` at
`64`, `i + 1` at `72`, node `i + 1`'s address at `80`, `hash_pair`'s output at `88`,
`Reader::digest`'s at `120`, the sibling's digest at `8`, a callee's return address at `0`; RSP at
offset `8` in the body. `entryS` at the entry (`b0`), `frS` for the blocks without an access
outside the frame; `cmpS` (region 1 node `i`'s key at RBP, region 2 node `j`'s at RAX plus 40) or
`selfS` (one region, `j = i`) for the scan's comparison (`b6`); `fndS` (region 1 node `j` at RAX,
region 2 sibling `i`) for the sibling found (`b7`); `rdS` (region 1 node `i`'s key, region 2
sibling `i`) for the sibling read (`b12`); `stS` (region 1 parent `p`) for the parent stored
(`b19`).
-/

namespace NativeRustcVmX64.Wire.ClimbLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ClimbLevel
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)
open NativeRustcVmX64.Sumcheck (WordW WordsW)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(200, .rbp), (192, .r15), (184, .r14), (176, .r13), (168, .r12), (160, .rbx)]

/-- `r + 4 r`, as `leaq (%r,%r,4)` computes it. -/
def five (r : Reg64) : Sym := .bin .add .W64 (.reg r) (.bin .mul .W64 (.reg r) (.lit 4))

/-- The address of slot `r` of the nodes at `b` (`(%b,%rcx,8)` after `leaq (%r,%r,4), %rcx`). -/
def slotA (b r : Reg64) : Sym := .bin .add .W64 (.reg b) (.bin .mul .W64 (five r) (.lit 8))

/-- At the entry: the frame, RSP at its offset 208. -/
def entryS : SState := init [216] [(.rsp, .ptr 0 208)]

/-- In the frame, RSP at its offset 8. -/
def frS : SState := init [216] [(.rsp, .ptr 0 8)]

/-- The frame, node `i`'s key at RBP, node `j`'s at RAX plus 40. -/
def cmpS : SState :=
  init [216, 8, 8] [(.rsp, .ptr 0 8)] [] [] [(.reg .rbp, 1, 0), (.reg .rax, 2, -40)]

/-- The frame, node `i`'s key at RBP and at RAX plus 40. -/
def selfS : SState :=
  init [216, 8] [(.rsp, .ptr 0 8)] [] [] [(.reg .rbp, 1, 0), (.reg .rax, 1, -40)]

/-- The frame, node `j` at RAX, sibling `i` at R15 plus `40 i`. -/
def fndS : SState :=
  init [216, 40, 40] [(.rsp, .ptr 0 8)] [] [] [(.reg .rax, 1, 0), (slotA .r15 .r12, 2, 0)]

/-- The frame, node `i`'s key at RBP, sibling `i` at R15 plus `40 i`. -/
def rdS : SState :=
  init [216, 8, 40] [(.rsp, .ptr 0 8)] [] [] [(.reg .rbp, 1, 0), (slotA .r15 .r12, 2, 0)]

/-- The frame, parent `p` at R14 plus `40 p`. -/
def stS : SState := init [216, 40] [(.rsp, .ptr 0 8)] [] [] [(slotA .r14 .rbx, 1, 0)]

/-- A block in the frame's body without writes. -/
def FrOk (S : SState) : Bool := MidOk 208 8 slots S && S.mem.isEmpty

/-- The registers `xs` kept. -/
def Keeps (xs : List Reg64) (S : SState) : Bool := xs.all fun x ↦ S.reg x == some (.reg x)

/-- Every write of region 0 within offsets `lo` to `hi`. -/
def FrW (lo hi : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || (decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi))

/-- Every write within its region `r` of `sz` bytes or region 0. -/
def InR (r sz : Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 || (w.r == r && decide (w.off + w.n ≤ sz))

/-- `8 n` times five, as `b1` computes `40 n`. -/
def n40 : Sym :=
  .bin .add .W64 (.bin .shl .W64 (.reg .rdx) (.lit 3))
    (.bin .mul .W64 (.bin .shl .W64 (.reg .rdx) (.lit 3)) (.lit 4))

/-- The registers of the loop. -/
def loopRegs : List Reg64 := [.rbx, .rbp, .r12, .r14, .r15]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 cmpS
sym_block run_b6s := exec b6 selfS
sym_block run_b7 := exec b7 fndS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 rdS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 stS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS

/-! ## The prologue, the set-up, the epilogue -/

public theorem ok_b0 : ProOk 208 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 208) ∧
    WordW 0 40 (.reg .rdi) (after b0 entryS) ∧
    (after b0 entryS).reg .rax = some (.lit 1) ∧
    Keeps [.rsi, .rdx, .rcx, .r8] (after b0 entryS) = true := by
  decide +kernel
public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)) NativeRustcVmX64.Vm.ClimbLevel.label_1) :=
  run_b0.trans (by rw [show after b0 entryS = _ from after_eq run_b0])

public theorem ok_b1 : MidOk 208 8 slots (after b1 frS) = true ∧ FrW 48 72 (after b1 frS) = true ∧
    WordW 0 48 (.bin .add .W64 (.reg .rsi) n40) (after b1 frS) ∧
    WordW 0 56 (.bin .add .W64 (.reg .rsi) (.lit 18446744073709551576)) (after b1 frS) ∧
    WordW 0 64 n40 (after b1 frS) ∧
    (after b1 frS).reg .rbx = some (.lit 0) ∧ (after b1 frS).reg .r12 = some (.lit 0) ∧
    (after b1 frS).reg .rbp = some (.reg .rsi) ∧ (after b1 frS).reg .r14 = some (.reg .r8) ∧
    (after b1 frS).reg .r15 = some (.reg .rcx) := by
  decide +kernel
public theorem exit_b1 : exec b1 frS = some (after b1 frS, .jump NativeRustcVmX64.Vm.ClimbLevel.label_3) :=
  run_b1.trans (by rw [show after b1 frS = _ from after_eq run_b1])

public theorem ok_b24 : EpiOk 208 slots (after b24 frS) = true ∧ (after b24 frS).mem = [] ∧
    (after b24 frS).reg .rdx = some (.reg .rbx) ∧ Keeps [.rax] (after b24 frS) = true := by
  decide +kernel
public theorem exit_b24 : exec b24 frS = some (after b24 frS, .ret (.load 0 208 8)) :=
  run_b24.trans (by rw [show after b24 frS = _ from after_eq run_b24])

public theorem ok_b20 : FrOk (after b20 frS) = true ∧ (after b20 frS).reg .rbx = some (.lit 0) ∧
    Keeps [.rax] (after b20 frS) = true := by
  decide +kernel
public theorem exit_b20 : exec b20 frS = some (after b20 frS, .jump NativeRustcVmX64.Vm.ClimbLevel.label_11) :=
  run_b20.trans (by rw [show after b20 frS = _ from after_eq run_b20])

public theorem ok_b21 : FrOk (after b21 frS) = true ∧ (after b21 frS).reg .rax = some (.lit 1) ∧
    Keeps [.rbx] (after b21 frS) = true := by
  decide +kernel
public theorem exit_b21 : exec b21 frS = some (after b21 frS, .jump NativeRustcVmX64.Vm.ClimbLevel.label_11) :=
  run_b21.trans (by rw [show after b21 frS = _ from after_eq run_b21])

public theorem ok_b23 : FrOk (after b23 frS) = true ∧ (after b23 frS).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem exit_b23 : exec b23 frS = some (after b23 frS, .fall) :=
  run_b23.trans (by rw [show after b23 frS = _ from after_eq run_b23])

/-! ## The loop's head and the scan -/

public theorem ok_b3 : FrOk (after b3 frS) = true ∧
    (after b3 frS).reg .rbp = some (.load 0 80 8) ∧ (after b3 frS).reg .r12 = some (.load 0 72 8) ∧
    Keeps [.rbx, .r14, .r15] (after b3 frS) = true := by
  decide +kernel
public theorem exit_b3 : exec b3 frS = some (after b3 frS,
    .cond (.cmp .eq .W64 (.load 0 80 8) (.load 0 48 8)) NativeRustcVmX64.Vm.ClimbLevel.label_8) :=
  run_b3.trans (by rw [show after b3 frS = _ from after_eq run_b3])

public theorem ok_b4 : MidOk 208 8 slots (after b4 frS) = true ∧ FrW 72 88 (after b4 frS) = true ∧
    WordW 0 72 (.bin .add .W64 (.reg .r12) (.lit 1)) (after b4 frS) ∧
    WordW 0 80 (.bin .add .W64 (.reg .rbp) (.lit 40)) (after b4 frS) ∧
    (after b4 frS).reg .rax = some (.load 0 56 8) ∧ (after b4 frS).reg .rcx = some (.load 0 64 8) ∧
    Keeps loopRegs (after b4 frS) = true := by
  decide +kernel
public theorem exit_b4 : exec b4 frS = some (after b4 frS, .fall) :=
  run_b4.trans (by rw [show after b4 frS = _ from after_eq run_b4])

public theorem ok_b5 : FrOk (after b5 frS) = true ∧
    Keeps (.rax :: .rcx :: loopRegs) (after b5 frS) = true := by
  decide +kernel
public theorem exit_b5 : exec b5 frS = some (after b5 frS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rcx) (.reg .rcx)) (.lit 0)) NativeRustcVmX64.Vm.ClimbLevel.label_9) :=
  run_b5.trans (by rw [show after b5 frS = _ from after_eq run_b5])

public theorem ok_b6 : MidOk 208 8 slots (after b6 cmpS) = true ∧ (after b6 cmpS).mem = [] ∧
    (after b6 cmpS).reg .rax = some (.bin .add .W64 (.lit 40) (.reg .rax)) ∧
    (after b6 cmpS).reg .rcx = some (.bin .add .W64 (.lit 18446744073709551576) (.reg .rcx)) ∧
    (after b6 cmpS).reg .r13 = some (.load 1 0 8) ∧ Keeps loopRegs (after b6 cmpS) = true := by
  decide +kernel
public theorem exit_b6 : exec b6 cmpS = some (after b6 cmpS,
    .cond (.not (.cmp .eq .W64 (.bin .xor .W64 (.load 2 0 8) (.load 1 0 8)) (.lit 1)))
      NativeRustcVmX64.Vm.ClimbLevel.label_4) :=
  run_b6.trans (by rw [show after b6 cmpS = _ from after_eq run_b6])

public theorem ok_b6s : MidOk 208 8 slots (after b6 selfS) = true ∧ (after b6 selfS).mem = [] ∧
    (after b6 selfS).reg .rax = some (.bin .add .W64 (.lit 40) (.reg .rax)) ∧
    (after b6 selfS).reg .rcx = some (.bin .add .W64 (.lit 18446744073709551576) (.reg .rcx)) ∧
    Keeps loopRegs (after b6 selfS) = true := by
  decide +kernel
public theorem exit_b6s : exec b6 selfS = some (after b6 selfS, .cond (.lit true) NativeRustcVmX64.Vm.ClimbLevel.label_4) :=
  run_b6s.trans (by rw [show after b6 selfS = _ from after_eq run_b6s])

/-! ## The sibling found -/

public theorem ok_b7 : MidOk 208 8 slots (after b7 fndS) = true ∧ FrW 8 40 (after b7 fndS) = true ∧
    InR 2 40 (after b7 fndS) = true ∧
    WordsW 0 8 (fun i ↦ .load 1 (8 + 8 * i) 8) (after b7 fndS) ∧
    WordW 2 0 (.reg .r13) (after b7 fndS) ∧
    WordsW 2 8 (fun i ↦ .load 1 (8 + 8 * i) 8) (after b7 fndS) ∧
    Keeps (.r13 :: loopRegs) (after b7 fndS) = true := by
  decide +kernel
public theorem exit_b7 : exec b7 fndS = some (after b7 fndS,
    .cond (.not (.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 1)) (.lit 0))) NativeRustcVmX64.Vm.ClimbLevel.label_7) :=
  run_b7.trans (by rw [show after b7 fndS = _ from after_eq run_b7])

public theorem ok_b8 : FrOk (after b8 frS) = true ∧ Keeps (.r13 :: loopRegs) (after b8 frS) = true := by
  decide +kernel
public theorem exit_b8 : exec b8 frS = some (after b8 frS, .jump NativeRustcVmX64.Vm.ClimbLevel.label_13) :=
  run_b8.trans (by rw [show after b8 frS = _ from after_eq run_b8])

/-! ## The sibling read -/

public theorem ok_b9 : FrOk (after b9 frS) = true ∧
    Keeps (.rax :: .rcx :: loopRegs) (after b9 frS) = true := by
  decide +kernel
public theorem exit_b9 : exec b9 frS = some (after b9 frS, .fall) :=
  run_b9.trans (by rw [show after b9 frS = _ from after_eq run_b9])

public theorem ok_b10 : MidOk 208 0 slots (after b10 frS) = true ∧
    (∀ w ∈ (after b10 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b10 frS).reg .rdi = some (.ptr 0 120) ∧ (after b10 frS).reg .rsi = some (.load 0 40 8) ∧
    Keeps loopRegs (after b10 frS) = true := by
  decide +kernel
public theorem exit_b10 : exec b10 frS = some (after b10 frS,
    .call NativeRustcVmX64.Vm.ReaderDigest.entryLabel) :=
  run_b10.trans (by rw [show after b10 frS = _ from after_eq run_b10])

public theorem ok_b11 : FrOk (after b11 frS) = true ∧ Keeps loopRegs (after b11 frS) = true := by
  decide +kernel
public theorem exit_b11 : exec b11 frS = some (after b11 frS,
    .cond (.cmp .eq .W8 (.load 0 120 1) (.lit 0)) NativeRustcVmX64.Vm.ClimbLevel.label_10) :=
  run_b11.trans (by rw [show after b11 frS = _ from after_eq run_b11])

public theorem ok_b12 : MidOk 208 8 slots (after b12 rdS) = true ∧ FrW 8 40 (after b12 rdS) = true ∧
    InR 2 40 (after b12 rdS) = true ∧
    WordsW 0 8 (fun i ↦ .load 0 (128 + 8 * i) 8) (after b12 rdS) ∧
    WordW 2 0 (.load 1 0 8) (after b12 rdS) ∧
    WordsW 2 8 (fun i ↦ .load 0 (128 + 8 * i) 8) (after b12 rdS) ∧
    (after b12 rdS).reg .r13 = some (.load 1 0 8) ∧ Keeps loopRegs (after b12 rdS) = true := by
  decide +kernel
public theorem exit_b12 : exec b12 rdS = some (after b12 rdS,
    .cond (.not (.cmp .eq .W8 (.bin .and .W8 (.load 1 0 8) (.lit 1)) (.lit 0))) NativeRustcVmX64.Vm.ClimbLevel.label_16) :=
  run_b12.trans (by rw [show after b12 rdS = _ from after_eq run_b12])

/-! ## The parent -/

public theorem ok_b13 : MidOk 208 0 slots (after b13 frS) = true ∧
    (∀ w ∈ (after b13 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b13 frS).reg .rdi = some (.ptr 0 88) ∧
    (after b13 frS).reg .rsi = some (.bin .add .W64 (.lit 8) (.reg .rbp)) ∧
    (after b13 frS).reg .rdx = some (.ptr 0 8) ∧
    (after b13 frS).reg .rbp = some (.bin .add .W64 (.lit 8) (.reg .rbp)) ∧
    Keeps [.rbx, .r12, .r13, .r14, .r15] (after b13 frS) = true := by
  decide +kernel
public theorem exit_b13 : exec b13 frS = some (after b13 frS,
    .call NativeRustcVmX64.Vm.HashPair.entryLabel) :=
  run_b13.trans (by rw [show after b13 frS = _ from after_eq run_b13])

public theorem ok_b17 : MidOk 208 0 slots (after b17 frS) = true ∧
    (∀ w ∈ (after b17 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b17 frS).reg .rdi = some (.ptr 0 88) ∧
    (after b17 frS).reg .rsi = some (.ptr 0 8) ∧
    (after b17 frS).reg .rdx = some (.bin .add .W64 (.lit 8) (.reg .rbp)) ∧
    (after b17 frS).reg .rbp = some (.bin .add .W64 (.lit 8) (.reg .rbp)) ∧
    Keeps [.rbx, .r12, .r13, .r14, .r15] (after b17 frS) = true := by
  decide +kernel
public theorem exit_b17 : exec b17 frS = some (after b17 frS,
    .call NativeRustcVmX64.Vm.HashPair.entryLabel) :=
  run_b17.trans (by rw [show after b17 frS = _ from after_eq run_b17])

public theorem ok_b14 : FrOk (after b14 frS) = true ∧
    Keeps (.r13 :: loopRegs) (after b14 frS) = true := by
  decide +kernel
public theorem exit_b14 : exec b14 frS = some (after b14 frS,
    .cond (.cmp .ult .W64 (.reg .rbx) (.lit 256)) NativeRustcVmX64.Vm.ClimbLevel.label_17) :=
  run_b14.trans (by rw [show after b14 frS = _ from after_eq run_b14])

public theorem ok_b18 : FrOk (after b18 frS) = true ∧
    Keeps (.r13 :: loopRegs) (after b18 frS) = true := by
  decide +kernel
public theorem exit_b18 : exec b18 frS = some (after b18 frS,
    .cond (.not (.cmp .ult .W64 (.reg .rbx) (.lit 256))) NativeRustcVmX64.Vm.ClimbLevel.label_15) :=
  run_b18.trans (by rw [show after b18 frS = _ from after_eq run_b18])

public theorem ok_b19 : MidOk 208 8 slots (after b19 stS) = true ∧ InR 1 40 (after b19 stS) = true ∧
    (∀ w ∈ (after b19 stS).mem, w.r = 1) ∧
    WordW 1 0 (.bin .shr .W64 (.reg .r13) (.lit 1)) (after b19 stS) ∧
    WordsW 1 8 (fun i ↦ .load 0 (88 + 8 * i) 8) (after b19 stS) ∧
    (after b19 stS).reg .rbx = some (.bin .add .W64 (.reg .rbx) (.lit 1)) ∧
    Keeps [.rbp, .r12, .r14, .r15] (after b19 stS) = true := by
  decide +kernel
public theorem exit_b19 : exec b19 stS = some (after b19 stS, .jump NativeRustcVmX64.Vm.ClimbLevel.label_7) :=
  run_b19.trans (by rw [show after b19 stS = _ from after_eq run_b19])

end NativeRustcVmX64.Wire.ClimbLevel
