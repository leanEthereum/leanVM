module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.Decode
public import NativeRustcVmX64.Code.Vm.Decode.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names
public meta import NativeRustcVmX64.Code.Vm.Decode
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `decode`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 80-byte frame below the entry's RSP and the return address (`Frame`, `F = 80`):
the six pushed registers from `32`, the reader at `8` (its slice's address, its length, its
cursor), RSP at offset `8` in the body, a callee's return address at `0`. Region 1, where a block
stores into the decoded area, is the word it stores: the stream's count (`b5`, at R13), the phase
count (`b8`, at R13 plus `8` RAX).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)
open NativeRustcVmX64.Sumcheck (WordW)

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(72, .rbp), (64, .r15), (56, .r14), (48, .r13), (40, .r12), (32, .rbx)]

/-- At the entry: the frame, RSP at its end. -/
def entryS : SState := init [88] [(.rsp, .ptr 0 80)]

/-- In the frame, RSP at its offset `8`. -/
def frS : SState := init [88] [(.rsp, .ptr 0 8)]

/-- The stream's count (region 1, 8 bytes at R13). -/
def cntS : SState := init [88, 8] [(.rsp, .ptr 0 8)] (aliases := [(.reg .r13, 1, 0)])

/-- The phase count's address: R13 plus `8` RAX. -/
def pcAddr : Sym := .bin .add .W64 (.reg .r13) (.bin .mul .W64 (.reg .rax) (.lit 8))

/-- The phase count (region 1, 8 bytes). -/
def pcS : SState := init [88, 8] [(.rsp, .ptr 0 8)] (aliases := [(pcAddr, 1, 0)])

/-- A block from `frS` keeping memory and the callee-saved registers, RSP at `8`. -/
def FrOk (S : SState) : Bool := MidOk 80 8 slots S && S.mem.isEmpty

/-- `b8`'s quotient: the phases the decoded area has room for, plus one. -/
def quot : Sym :=
  let x := Sym.bin .add .W64 (.un .not .W64 (.reg .rax)) (.reg .r14)
  let h := Sym.bin .mulhi .W64 x (.lit 6019990451287497113)
  .bin .add .W64 (.bin .shr .W64 (.bin .add .W64 h (.bin .shr .W64 (.bin .sub .W64 x h) (.lit 1)))
    (.lit 15)) (.lit 1)

/-- `b6`'s test: the read's flag and the phase count below `9`. -/
def c6 : SBool :=
  let cl := Sym.bin .merge .W8 (.reg .rcx)
    (.ite (.cmp .ult .W64 (.reg .rdx) (.lit 9)) (.lit 1) (.lit 0))
  (SBool.cmp .eq .W8 (.bin .merge .W8 cl (.bin .and .W8 cl (.reg .rax))) (.lit 1)).not

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 cntS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 pcS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 80 0 slots (after b0 entryS) = true ∧
    WordW 0 8 (.reg .rdi) (after b0 entryS) ∧ WordW 0 16 (.reg .rsi) (after b0 entryS) ∧
    WordW 0 24 (.lit 0) (after b0 entryS) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ (w.off + w.n ≤ 32 ∨ 32 ≤ w.off ∧ w.off + w.n ≤ 80)) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 8) ∧ (after b0 entryS).reg .rsi = some (.lit 4) ∧
    (after b0 entryS).reg .rbx = some (.reg .r8) ∧ (after b0 entryS).reg .r13 = some (.reg .rdx) ∧
    (after b0 entryS).reg .r14 = some (.reg .rcx) ∧ (after b0 entryS).reg .r15 = some (.reg .rsi) := by
  decide +kernel

public theorem exit_b1 : exec b1 frS = some (after b1 frS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : FrOk (after b1 frS) = true ∧
    (∀ x ∈ [Reg64.rdx, .rbx, .r13, .r14, .r15], (after b1 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b2 : exec b2 frS = some (after b2 frS,
    .cond (SBool.cmp .ult .W64 (.bin .add .W64 (.reg .rdx) (.reg .rdx)) (.reg .r14)).not
      NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : FrOk (after b2 frS) = true ∧ (after b2 frS).reg .rcx = some (.reg .rdx) ∧
    (after b2 frS).reg .rdx = some (.bin .add .W64 (.reg .rdx) (.reg .rdx)) ∧
    (∀ x ∈ [Reg64.rbx, .r13, .r14, .r15], (after b2 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b3 : exec b3 frS = some (after b3 frS,
    .call NativeRustcVmX64.Vm.ReaderWords.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 80 0 slots (after b3 frS) = true ∧
    (∀ w ∈ (after b3 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 frS).reg .rsi = some (.bin .add .W64 (.reg .r13) (.lit 8)) ∧
    (after b3 frS).reg .rdi = some (.ptr 0 8) ∧ (after b3 frS).reg .r12 = some (.reg .rcx) ∧
    (∀ x ∈ [Reg64.rdx, .rbx, .r13, .r14, .r15], (after b3 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b4 : exec b4 frS = some (after b4 frS,
    .cond (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : FrOk (after b4 frS) = true ∧
    (∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], (after b4 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b5 : exec b5 cntS = some (after b5 cntS,
    .call NativeRustcVmX64.Vm.ReaderLe.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 80 0 slots (after b5 cntS) = true ∧
    (after b5 cntS).mem = [⟨0, 0, 8, .retAddr⟩, ⟨1, 0, 8, .reg .r12⟩] ∧
    WordW 1 0 (.reg .r12) (after b5 cntS) ∧
    (after b5 cntS).reg .rsi = some (.lit 4) ∧ (after b5 cntS).reg .rdi = some (.ptr 0 8) ∧
    (∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], (after b5 cntS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b6 : exec b6 frS = some (after b6 frS, .cond c6 NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : FrOk (after b6 frS) = true ∧
    (∀ x ∈ [Reg64.rdx, .rbx, .r12, .r13, .r14, .r15], (after b6 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b7 : exec b7 frS = some (after b7 frS,
    .cond (SBool.cmp .ult .W64 (.bin .or .W64 (.bin .shr .W64 (.reg .r15) (.lit 3)) (.lit 1))
      (.reg .r14)).not NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : FrOk (after b7 frS) = true ∧
    (after b7 frS).reg .rax = some (.bin .or .W64 (.bin .shr .W64 (.reg .r15) (.lit 3)) (.lit 1)) ∧
    (∀ x ∈ [Reg64.rdx, .rbx, .r12, .r13, .r14, .r15], (after b7 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b8 : exec b8 pcS = some (after b8 pcS, .fall) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 80 8 slots (after b8 pcS) = true ∧
    (after b8 pcS).mem = [⟨1, 0, 8, .reg .rdx⟩] ∧ WordW 1 0 (.reg .rdx) (after b8 pcS) ∧
    (after b8 pcS).reg .r12 = some (.reg .rdx) ∧
    (after b8 pcS).reg .r13 = some (.bin .add .W64 (.bin .add .W64 (.reg .r13)
      (.bin .mul .W64 (.reg .rax) (.lit 8))) (.lit 18446744073709156336)) ∧
    (after b8 pcS).reg .r14 = some quot ∧ (after b8 pcS).reg .rbp = some (.lit 0) ∧
    (∀ x ∈ [Reg64.rbx, .r15], (after b8 pcS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b9 : exec b9 frS = some (after b9 frS,
    .cond (SBool.cmp .eq .W64 (.reg .r12) (.reg .rbp)) NativeRustcVmX64.Vm.Decode.label_7) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : FrOk (after b9 frS) = true ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], (after b9 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b10 : exec b10 frS = some (after b10 frS,
    .cond (SBool.cmp .eq .W64 (.reg .r14) (.bin .add .W64 (.reg .rbp) (.lit 1))) NativeRustcVmX64.Vm.Decode.label_9) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : FrOk (after b10 frS) = true ∧
    (after b10 frS).reg .rbp = some (.bin .add .W64 (.reg .rbp) (.lit 1)) ∧
    (∀ x ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], (after b10 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b11 : exec b11 frS = some (after b11 frS,
    .call NativeRustcVmX64.Vm.PhaseM.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 80 0 slots (after b11 frS) = true ∧
    (∀ w ∈ (after b11 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b11 frS).reg .r13 = some (.bin .add .W64 (.lit 395288) (.reg .r13)) ∧
    (after b11 frS).reg .rsi = some (.bin .add .W64 (.lit 395288) (.reg .r13)) ∧
    (after b11 frS).reg .rdi = some (.ptr 0 8) ∧ (after b11 frS).reg .rdx = some (.reg .rbx) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15], (after b11 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b12 : exec b12 frS = some (after b12 frS,
    .cond (SBool.cmp .eq .W8 (.bin .and .W8 (.un .trunc .W32 (.reg .rax))
      (.un .trunc .W32 (.reg .rax))) (.lit 0)).not NativeRustcVmX64.Vm.Decode.label_6) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : FrOk (after b12 frS) = true ∧ (after b12 frS).reg .rax = some (.lit 0) ∧
    (∀ x ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], (after b12 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b13 : exec b13 frS = some (after b13 frS, .jump NativeRustcVmX64.Vm.Decode.label_10) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : FrOk (after b13 frS) = true ∧ (after b13 frS).reg .rax = some (.reg .rax) ∧
    (∀ x ∈ [Reg64.rbx, .r15], (after b13 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b14 : exec b14 frS = some (after b14 frS, .fall) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : FrOk (after b14 frS) = true ∧ (after b14 frS).reg .rax = some (.lit 0) ∧
    (∀ x ∈ [Reg64.rbx, .r15], (after b14 frS).reg x = some (.reg x)) := by
  decide +kernel

public theorem exit_b15 : exec b15 frS = some (after b15 frS, .ret (.load 0 80 8)) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : EpiOk 80 slots (after b15 frS) = true ∧ (after b15 frS).mem = [] ∧
    (after b15 frS).reg .rax = some (.reg .rax) := by
  decide +kernel

public theorem exit_b16 : exec b16 frS = some (after b16 frS, .jump NativeRustcVmX64.Vm.Decode.label_10) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : FrOk (after b16 frS) = true ∧
    (after b16 frS).reg .rax = some (.bin .merge .W8 (.reg .rax)
      (.ite (.cmp .eq .W64 (.load 0 24 8) (.reg .r15)) (.lit 1) (.lit 0))) ∧
    (∀ x ∈ [Reg64.rbx, .r15], (after b16 frS).reg x = some (.reg x)) := by
  decide +kernel

end NativeRustcVmX64.Wire.Decode
