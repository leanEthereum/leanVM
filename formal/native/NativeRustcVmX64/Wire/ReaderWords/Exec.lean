module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ReaderWords
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names
public meta import NativeRustcVmX64.Code.Vm.ReaderWords
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Reader::words`' blocks, run by the symbolic executor (x86-64)

Region 0 the 48-byte frame (R15, R14, R12, RBX pushed at offsets `40` to `16`, RAX at `8`,
`Reader::le`'s return address at `0`) and the return address. `entryS`, region 1 the reader
(RDI): the prologue and the bound check (`b0`, `b1`), the empty check (`b2`), the loop's set-up
(`b3`), each run from the last; the epilogue (`b9`) after each check. `loopS`, region 1 the next
output word (RBX plus R12, an alias): the call (`b4`), its check (`b5`), the store and the count
(`b6`); from `frS` the call's check (`b5`), `Some` (`b7`), `None` (`b8`) and the epilogue (`b9`).
-/

namespace NativeRustcVmX64.Wire.ReaderWords

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReaderWords
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

/-- `8 n`, as `b0` computes it from RDX. -/
def eightN : Sym := .bin .mul .W64 (.reg .rdx) (.lit 8)

/-- At the entry: the frame, RSP at its offset 48; the reader. -/
def entryS : SState := init [56, 24] [(.rsp, .ptr 0 48), (.rdi, .ptr 1 0)]

/-- In the loop: the frame, RSP at its offset 8; the next output word at RBX plus R12. -/
def loopS : SState :=
  init [56, 8] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .rbx) (.reg .r12), 1, 0)]

/-- In the frame, RSP at its offset 8. -/
def frS : SState := init [56] [(.rsp, .ptr 0 8)]

/-- The bound check against the length: the frame, the reader. -/
def chkS : SState := init [56, 24] [(.rsp, .ptr 0 8), (.rdi, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 chkS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 loopS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 loopS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS

public theorem ok_b0 : ProOk 48 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b0 entryS).reg .rax = some (.lit 0) ∧ (after b0 entryS).reg .r15 = some eightN ∧
    (after b0 entryS).reg .rcx = some (.bin .add .W64 eightN (.load 1 16 8)) ∧
    (after b0 entryS).reg .rdi = some (.ptr 1 0) ∧ (after b0 entryS).reg .rdx = some (.reg .rdx) ∧
    (after b0 entryS).reg .rsi = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (.cmp .addC .W64 eightN (.load 1 16 8)) NativeRustcVmX64.Vm.ReaderWords.label_8) :=
  run_b0.trans (by rw [show after b0 entryS = _ from after_eq run_b0]; rfl)

public theorem ok_b1 : MidOk 48 8 slots (after b1 chkS) = true ∧ (after b1 chkS).mem = [] ∧
    (after b1 chkS).reg .rax = some (.reg .rax) ∧ (after b1 chkS).reg .r14 = some (.ptr 1 0) ∧
    (after b1 chkS).reg .r15 = some (.reg .r15) ∧ (after b1 chkS).reg .rdx = some (.reg .rdx) ∧
    (after b1 chkS).reg .rsi = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b1 : exec b1 chkS = some (after b1 chkS,
    .cond (.and (.not (.cmp .ult .W64 (.reg .rcx) (.load 1 8 8)))
      (.not (.cmp .eq .W64 (.reg .rcx) (.load 1 8 8)))) NativeRustcVmX64.Vm.ReaderWords.label_8) :=
  run_b1.trans (by rw [show after b1 chkS = _ from after_eq run_b1])

/-- A block from `frS` keeping memory, RSP and the callee-saved registers. -/
@[expose] public def FrOk (S : SState) : Bool := MidOk 48 8 slots S && S.mem.isEmpty

public theorem ok_b2 : FrOk (after b2 frS) = true ∧
    (after b2 frS).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) ∧
    (∀ x ∈ [Reg64.rsi, .rdx, .r14, .r15], (after b2 frS).reg x = some (.reg x)) := by
  decide +kernel
public theorem exit_b2 : exec b2 frS = some (after b2 frS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)) NativeRustcVmX64.Vm.ReaderWords.label_8) :=
  run_b2.trans (by rw [show after b2 frS = _ from after_eq run_b2])

public theorem ok_b3 : FrOk (after b3 frS) = true ∧
    (after b3 frS).reg .rbx = some (.reg .rsi) ∧ (after b3 frS).reg .r12 = some (.lit 0) ∧
    (∀ x ∈ [Reg64.r14, .r15], (after b3 frS).reg x = some (.reg x)) := by
  decide +kernel
public theorem exit_b3 : exec b3 frS = some (after b3 frS, .fall) :=
  run_b3.trans (by rw [show after b3 frS = _ from after_eq run_b3])

public theorem ok_b4 : MidOk 48 0 slots (after b4 loopS) = true ∧
    (∀ w ∈ (after b4 loopS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b4 loopS).reg .rdi = some (.reg .r14) ∧ (after b4 loopS).reg .rsi = some (.lit 8) ∧
    (∀ x ∈ [Reg64.rbx, .r12, .r14, .r15], (after b4 loopS).reg x = some (.reg x)) := by
  decide +kernel
public theorem exit_b4 : exec b4 loopS = some (after b4 loopS,
    .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b4.trans (by rw [show after b4 loopS = _ from after_eq run_b4])

public theorem ok_b5 : FrOk (after b5 frS) = true ∧
    (∀ x ∈ [Reg64.rax, .rdx, .rbx, .r12, .r14, .r15], (after b5 frS).reg x = some (.reg x)) := by
  decide +kernel
public theorem exit_b5 : exec b5 frS = some (after b5 frS,
    .cond (.not (.cmp .eq .W64 (.reg .rax) (.lit 1))) NativeRustcVmX64.Vm.ReaderWords.label_5) :=
  run_b5.trans (by rw [show after b5 frS = _ from after_eq run_b5])

public theorem ok_b6 : MidOk 48 8 slots (after b6 loopS) = true ∧
    (after b6 loopS).mem = [⟨1, 0, 8, .reg .rdx⟩] ∧
    (after b6 loopS).reg .r12 = some (.bin .add .W64 (.lit 8) (.reg .r12)) ∧
    (∀ x ∈ [Reg64.rbx, .r14, .r15], (after b6 loopS).reg x = some (.reg x)) := by
  decide +kernel
public theorem exit_b6 : exec b6 loopS = some (after b6 loopS,
    .cond (.not (.cmp .eq .W64 (.reg .r15) (.bin .add .W64 (.lit 8) (.reg .r12))))
      NativeRustcVmX64.Vm.ReaderWords.label_4) :=
  run_b6.trans (by rw [show after b6 loopS = _ from after_eq run_b6])

public theorem ok_b7 : FrOk (after b7 frS) = true ∧
    (after b7 frS).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) := by
  decide +kernel
public theorem exit_b7 : exec b7 frS = some (after b7 frS, .jump NativeRustcVmX64.Vm.ReaderWords.label_8) :=
  run_b7.trans (by rw [show after b7 frS = _ from after_eq run_b7])

public theorem ok_b8 : FrOk (after b8 frS) = true ∧ (after b8 frS).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem exit_b8 : exec b8 frS = some (after b8 frS, .fall) :=
  run_b8.trans (by rw [show after b8 frS = _ from after_eq run_b8])

public theorem ok_b9 : EpiOk 48 slots (after b9 frS) = true ∧ (after b9 frS).mem = [] ∧
    (after b9 frS).reg .rax = some (.reg .rax) := by
  decide +kernel
public theorem exit_b9 : exec b9 frS = some (after b9 frS, .ret (.load 0 48 8)) :=
  run_b9.trans (by rw [show after b9 frS = _ from after_eq run_b9])

end NativeRustcVmX64.Wire.ReaderWords
