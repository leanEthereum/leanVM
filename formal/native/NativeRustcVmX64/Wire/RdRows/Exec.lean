module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.RdRows
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names
public meta import NativeRustcVmX64.Code.Vm.RdRows
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `rd_rows`' blocks, run by the symbolic executor (x86-64)

Region 0 the 80-byte frame and the return address: RBP to RBX pushed at offsets `72` to `32`, the
locals `lw` at `8`, the reader at `16`, `8 lw` at `24` (rows of no word), `Reader::words`' return
address at `0`; RSP at offset `8` in the body. `entryS` at the entry (`b0`: the prologue, the
width check), `frS` for every block without an access outside the frame, `zS` (region 1 the word
at R14 plus RAX) for the one-word zero loops (`b7`, `b16`), `rowS` (region 1 the row's first word,
at R13) for the flag (`b10`), `octS` (region 1 the 64 bytes at RAX) for the eight-word zero loop
(`b20`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .rbp), (64, .r15), (56, .r14), (48, .r13), (40, .r12), (32, .rbx)]

/-- At the entry: the frame, RSP at its offset 80. -/
def entryS : SState := init [88] [(.rsp, .ptr 0 80)]

/-- In the frame, RSP at its offset 8. -/
def frS : SState := init [88] [(.rsp, .ptr 0 8)]

/-- The frame and the `sz` bytes at `y` (region 1). -/
def rgS (y : Sym) (sz : Nat) : SState := init [88, sz] [(.rsp, .ptr 0 8)] [] [] [(y, 1, 0)]

/-- The frame and the word at R14 plus RAX. -/
def zS : SState := rgS (.bin .add .W64 (.reg .r14) (.reg .rax)) 8

/-- The frame and the row's first word (R13). -/
def rowS : SState := rgS (.reg .r13) 8

/-- The frame and the 64 bytes at RAX. -/
def octS : SState := rgS (.reg .rax) 64

/-- A block in the frame's body without writes. -/
def FrOk (S : SState) : Bool := MidOk 80 8 slots S && S.mem.isEmpty

/-- The registers `xs` kept. -/
def Keeps (xs : List Reg64) (S : SState) : Bool := xs.all fun x ↦ S.reg x == some (.reg x)

/-- The local `lw`. -/
def lwS : Sym := .load 0 8 8

/-- `8 lw`, as `b12` computes it. -/
def e8 : Sym := .bin .mul .W64 lwS (.lit 8)

/-- `8 lw - 8`. -/
def e8m : Sym := .bin .add .W64 e8 (.lit 18446744073709551608)

/-- `lw % 8`, as `b12` computes it. -/
def rem8 : Sym :=
  .bin .and .W32 (.bin .add .W32 (.bin .shr .W32 e8m (.lit 3)) (.lit 1)) (.lit 7)

/-- The registers of the rows' loops. -/
def loopRegs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 zS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 rowS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 zS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 octS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS

/-! ## The prologue and the epilogue -/

public theorem ok_b0 : ProOk 80 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (∀ t < 8, findWrite 0 (8 + t) (after b0 entryS).mem = some (.reg .rdx, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) (after b0 entryS).mem = some (.reg .rdi, t)) ∧
    (after b0 entryS).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 2)) ∧
    Keeps [.rdi, .rsi, .rdx, .rcx, .r8] (after b0 entryS) = true := by
  decide +kernel
public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (.not (.cmp .ult .W64 (.reg .rdx) (.reg .rcx))) NativeRustcVmX64.Vm.RdRows.label_2) :=
  run_b0.trans (by rw [show after b0 entryS = _ from after_eq run_b0])

public theorem ok_b1 : FrOk (after b1 frS) = true ∧
    (after b1 frS).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 2)) := by
  decide +kernel
public theorem exit_b1 : exec b1 frS = some (after b1 frS, .fall) :=
  run_b1.trans (by rw [show after b1 frS = _ from after_eq run_b1])

public theorem ok_b2 : EpiOk 80 slots (after b2 frS) = true ∧ (after b2 frS).mem = [] ∧
    (after b2 frS).reg .rax = some (.un .trunc .W32 (.reg .rbx)) := by
  decide +kernel
public theorem exit_b2 : exec b2 frS = some (after b2 frS, .ret (.load 0 80 8)) :=
  run_b2.trans (by rw [show after b2 frS = _ from after_eq run_b2])

public theorem ok_b11 : FrOk (after b11 frS) = true ∧ Keeps [.rbx] (after b11 frS) = true := by
  decide +kernel
public theorem exit_b11 : exec b11 frS = some (after b11 frS, .jump NativeRustcVmX64.Vm.RdRows.label_21) :=
  run_b11.trans (by rw [show after b11 frS = _ from after_eq run_b11])

public theorem ok_b24 : FrOk (after b24 frS) = true ∧
    (after b24 frS).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) := by
  decide +kernel
public theorem exit_b24 : exec b24 frS = some (after b24 frS, .jump NativeRustcVmX64.Vm.RdRows.label_21) :=
  run_b24.trans (by rw [show after b24 frS = _ from after_eq run_b24])

/-! ## The set-up -/

public theorem ok_b3 : FrOk (after b3 frS) = true ∧
    (after b3 frS).reg .rbp = some (.reg .rcx) ∧
    (after b3 frS).reg .r12 = some (.bin .add .W64 (.reg .r8) (.bin .shl .W64 (.reg .rsi) (.lit 9))) ∧
    (after b3 frS).reg .r14 = some (.reg .r8) ∧
    Keeps [.rbx, .r15, .rcx] (after b3 frS) = true := by
  decide +kernel
public theorem exit_b3 : exec b3 frS = some (after b3 frS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rcx) (.reg .rcx)) (.lit 0)) NativeRustcVmX64.Vm.RdRows.label_9) :=
  run_b3.trans (by rw [show after b3 frS = _ from after_eq run_b3])

public theorem ok_b4 : FrOk (after b4 frS) = true ∧
    (after b4 frS).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) ∧
    (after b4 frS).reg .r15 = some (.bin .shl .W64 (.reg .r15) (.lit 3)) ∧
    Keeps [.rbp, .r12, .r14] (after b4 frS) = true := by
  decide +kernel
public theorem exit_b4 : exec b4 frS = some (after b4 frS, .fall) :=
  run_b4.trans (by rw [show after b4 frS = _ from after_eq run_b4])

public theorem ok_b12 : MidOk 80 8 slots (after b12 frS) = true ∧
    (after b12 frS).mem = [⟨0, 24, 8, e8⟩] ∧
    (after b12 frS).reg .r13 = some rem8 ∧
    (after b12 frS).reg .rbp = some (.bin .shl .W32 rem8 (.lit 3)) ∧
    (after b12 frS).reg .r15 = some e8m ∧
    Keeps [.rbx, .r12, .r14] (after b12 frS) = true := by
  decide +kernel
public theorem exit_b12 : exec b12 frS = some (after b12 frS, .fall) :=
  run_b12.trans (by rw [show after b12 frS = _ from after_eq run_b12])

/-! ## Rows of `rw > 0` words -/

public theorem ok_b5 : FrOk (after b5 frS) = true ∧ Keeps loopRegs (after b5 frS) = true := by
  decide +kernel
public theorem exit_b5 : exec b5 frS = some (after b5 frS,
    .cond (.cmp .eq .W64 (.load 0 8 8) (.reg .rbp)) NativeRustcVmX64.Vm.RdRows.label_7) :=
  run_b5.trans (by rw [show after b5 frS = _ from after_eq run_b5])

public theorem ok_b6 : FrOk (after b6 frS) = true ∧ (after b6 frS).reg .rax = some (.lit 0) ∧
    Keeps loopRegs (after b6 frS) = true := by
  decide +kernel
public theorem exit_b6 : exec b6 frS = some (after b6 frS, .fall) :=
  run_b6.trans (by rw [show after b6 frS = _ from after_eq run_b6])

public theorem ok_b7 : MidOk 80 8 slots (after b7 zS) = true ∧
    (after b7 zS).mem = [⟨1, 0, 8, .lit 0⟩] ∧
    (after b7 zS).reg .rax = some (.bin .add .W64 (.lit 8) (.reg .rax)) ∧
    Keeps loopRegs (after b7 zS) = true := by
  decide +kernel
public theorem exit_b7 : exec b7 zS = some (after b7 zS,
    .cond (.not (.cmp .eq .W64 (.reg .r15) (.bin .add .W64 (.lit 8) (.reg .rax)))) NativeRustcVmX64.Vm.RdRows.label_6) :=
  run_b7.trans (by rw [show after b7 zS = _ from after_eq run_b7])

public theorem ok_b8 : MidOk 80 0 slots (after b8 frS) = true ∧
    (∀ w ∈ (after b8 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b8 frS).reg .rdi = some (.load 0 16 8) ∧
    (after b8 frS).reg .rsi = some (.bin .add .W64 (.reg .r14) (.reg .r15)) ∧
    (after b8 frS).reg .rdx = some (.reg .rbp) ∧
    (after b8 frS).reg .r13 = some (.bin .add .W64 (.reg .r14) (.reg .r15)) ∧
    Keeps [.rbx, .rbp, .r12, .r14, .r15] (after b8 frS) = true := by
  decide +kernel
public theorem exit_b8 : exec b8 frS = some (after b8 frS,
    .call NativeRustcVmX64.Vm.ReaderWords.entryLabel) :=
  run_b8.trans (by rw [show after b8 frS = _ from after_eq run_b8])

public theorem ok_b9 : FrOk (after b9 frS) = true ∧ Keeps loopRegs (after b9 frS) = true := by
  decide +kernel
public theorem exit_b9 : exec b9 frS = some (after b9 frS,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.RdRows.label_20) :=
  run_b9.trans (by rw [show after b9 frS = _ from after_eq run_b9])

public theorem ok_b10 : MidOk 80 8 slots (after b10 rowS) = true ∧ (after b10 rowS).mem = [] ∧
    (after b10 rowS).reg .rbx = some (.ite (.not (.cmp .eq .W64 (.load 1 0 8) (.lit 0))) (.lit 0)
      (.un (.zext .W8) .W32 (.reg .rbx))) ∧
    (after b10 rowS).reg .r14 = some (.bin .add .W64 (.lit 512) (.reg .r14)) ∧
    Keeps [.rbp, .r12, .r15] (after b10 rowS) = true := by
  decide +kernel
public theorem exit_b10 : exec b10 rowS = some (after b10 rowS,
    .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 512) (.reg .r14)) (.reg .r12)))
      NativeRustcVmX64.Vm.RdRows.label_4) :=
  run_b10.trans (by rw [show after b10 rowS = _ from after_eq run_b10])

/-! ## Rows of no word -/

public theorem ok_b13 : FrOk (after b13 frS) = true ∧
    (after b13 frS).reg .rsi = some (.bin .add .W64 (.reg .r14) (.load 0 24 8)) ∧
    Keeps loopRegs (after b13 frS) = true := by
  decide +kernel
public theorem exit_b13 : exec b13 frS = some (after b13 frS,
    .cond (.cmp .eq .W64 (.load 0 8 8) (.lit 0)) NativeRustcVmX64.Vm.RdRows.label_17) :=
  run_b13.trans (by rw [show after b13 frS = _ from after_eq run_b13])

public theorem ok_b14 : FrOk (after b14 frS) = true ∧ (after b14 frS).reg .rax = some (.reg .r14) ∧
    Keeps (.rsi :: loopRegs) (after b14 frS) = true := by
  decide +kernel
public theorem exit_b14 : exec b14 frS = some (after b14 frS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0)) NativeRustcVmX64.Vm.RdRows.label_15) :=
  run_b14.trans (by rw [show after b14 frS = _ from after_eq run_b14])

public theorem ok_b15 : FrOk (after b15 frS) = true ∧ (after b15 frS).reg .rax = some (.lit 0) ∧
    Keeps (.rsi :: loopRegs) (after b15 frS) = true := by
  decide +kernel
public theorem exit_b15 : exec b15 frS = some (after b15 frS, .fall) :=
  run_b15.trans (by rw [show after b15 frS = _ from after_eq run_b15])

public theorem ok_b16 : MidOk 80 8 slots (after b16 zS) = true ∧
    (after b16 zS).mem = [⟨1, 0, 8, .lit 0⟩] ∧
    (after b16 zS).reg .rax = some (.bin .add .W64 (.lit 8) (.reg .rax)) ∧
    Keeps (.rsi :: loopRegs) (after b16 zS) = true := by
  decide +kernel
public theorem exit_b16 : exec b16 zS = some (after b16 zS,
    .cond (.not (.cmp .eq .W64 (.reg .rbp) (.bin .add .W64 (.lit 8) (.reg .rax)))) NativeRustcVmX64.Vm.RdRows.label_13) :=
  run_b16.trans (by rw [show after b16 zS = _ from after_eq run_b16])

public theorem ok_b17 : FrOk (after b17 frS) = true ∧
    (after b17 frS).reg .rax = some (.bin .add .W64 (.reg .r14) (.reg .rax)) ∧
    Keeps (.rsi :: loopRegs) (after b17 frS) = true := by
  decide +kernel
public theorem exit_b17 : exec b17 frS = some (after b17 frS, .fall) :=
  run_b17.trans (by rw [show after b17 frS = _ from after_eq run_b17])

public theorem ok_b18 : FrOk (after b18 frS) = true ∧
    Keeps (.rax :: .rsi :: loopRegs) (after b18 frS) = true := by
  decide +kernel
public theorem exit_b18 : exec b18 frS = some (after b18 frS,
    .cond (.cmp .ult .W64 (.reg .r15) (.lit 56)) NativeRustcVmX64.Vm.RdRows.label_17) :=
  run_b18.trans (by rw [show after b18 frS = _ from after_eq run_b18])

public theorem ok_b19 : FrOk (after b19 frS) = true ∧
    Keeps (.rax :: .rsi :: loopRegs) (after b19 frS) = true := by
  decide +kernel
public theorem exit_b19 : exec b19 frS = some (after b19 frS, .fall) :=
  run_b19.trans (by rw [show after b19 frS = _ from after_eq run_b19])

public theorem ok_b20 : MidOk 80 8 slots (after b20 octS) = true ∧
    (∀ w ∈ (after b20 octS).mem, w.r = 1 ∧ w.n = 8 ∧ w.v = .lit 0 ∧ w.off % 8 = 0 ∧
      w.off + 8 ≤ 64) ∧
    (∀ t < 8, ∀ u < 8, findWrite 1 (8 * t + u) (after b20 octS).mem = some (.lit 0, u)) ∧
    (after b20 octS).reg .rax = some (.bin .add .W64 (.lit 64) (.reg .rax)) ∧
    Keeps (.rsi :: loopRegs) (after b20 octS) = true := by
  decide +kernel
public theorem exit_b20 : exec b20 octS = some (after b20 octS,
    .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 64) (.reg .rax)) (.reg .rsi))) NativeRustcVmX64.Vm.RdRows.label_16) :=
  run_b20.trans (by rw [show after b20 octS = _ from after_eq run_b20])

public theorem ok_b21 : MidOk 80 0 slots (after b21 frS) = true ∧
    (∀ w ∈ (after b21 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b21 frS).reg .rdi = some (.load 0 16 8) ∧ (after b21 frS).reg .rdx = some (.lit 0) ∧
    Keeps (.rsi :: loopRegs) (after b21 frS) = true := by
  decide +kernel
public theorem exit_b21 : exec b21 frS = some (after b21 frS,
    .call NativeRustcVmX64.Vm.ReaderWords.entryLabel) :=
  run_b21.trans (by rw [show after b21 frS = _ from after_eq run_b21])

public theorem ok_b22 : FrOk (after b22 frS) = true ∧ Keeps loopRegs (after b22 frS) = true := by
  decide +kernel
public theorem exit_b22 : exec b22 frS = some (after b22 frS,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.RdRows.label_21) :=
  run_b22.trans (by rw [show after b22 frS = _ from after_eq run_b22])

public theorem ok_b23 : FrOk (after b23 frS) = true ∧
    (after b23 frS).reg .r14 = some (.bin .add .W64 (.lit 512) (.reg .r14)) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r15] (after b23 frS) = true := by
  decide +kernel
public theorem exit_b23 : exec b23 frS = some (after b23 frS,
    .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 512) (.reg .r14)) (.reg .r12)))
      NativeRustcVmX64.Vm.RdRows.label_10) :=
  run_b23.trans (by rw [show after b23 frS = _ from after_eq run_b23])

end NativeRustcVmX64.Wire.RdRows
