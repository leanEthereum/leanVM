module

public import NativeRustcVmX64.Layout.BuildFrame
public import NativeRustcVmX64.Code.Vm.StackOffsets
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.StackOffsets.Names
public meta import NativeRustcVmX64.Code.Vm.StackOffsets
public meta import NativeRustcVmX64.Layout.BuildFrame

/-!
# `stack_offsets`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 1328-byte frame below the entry's RSP and the return address (`Frame`, `F = 1328`:
RSP at offset `8` in the body, a callee's return address at `0`): the order array at `16` (1264
bytes), the six pushed registers from `1280`.

- `entryS` at the entry: `b0` (`offsets` long enough?), `b1` (`None`), `b2` (the prologue, the
  call of `memset` on the order array);
- `bodyS` in the body: every block of registers only, the calls (`b13`, `b23`) and the epilogue
  (`b25`);
- `quadS` (`b8`, eight words of the order array at R13), `ordOneS` (`b11`'s store into the order
  array at `R13 + 8 RDX`): the only region, part of the frame (`SubOk`);
- `oneS p i` (one word at `p + 8 i`, region 1: `b20`'s store into `offsets`, `b21`'s load of
  `sizes[i]`), `ordS` (`b19`'s load of `order[j]` at the byte offset RSI, bounded).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Transcript
open NativeRustcVmX64.Layout.BuildFrame (Keeps SubOk)

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(1320, .rbp), (1312, .r15), (1304, .r14), (1296, .r13), (1288, .r12), (1280, .rbx)]

/-- `p + 8 i`. -/
def idx (p i : Reg64) : Sym := .bin .add .W64 (.reg p) (.bin .mul .W64 (.reg i) (.lit 8))

/-- At the entry: RSP at the frame's offset `1328`. -/
def entryS : SState :=
  (init [1336, 8] [(.rsp, .ptr 0 1328)] [] [] [(.gotSlot "memset", 1, 0)]).withKnownBytes
    1 0 8 (.label "memset")
/-- In the body: RSP at offset `8`. -/
def bodyS : SState := init [1336] [(.rsp, .ptr 0 8)]
/-- Eight words of the order array at R13 (region 0). -/
def quadS : SState := init [64] [(.r13, .ptr 0 0)]
/-- The word of the order array at `R13 + 8 RDX` (region 0). -/
def ordOneS : SState := init [8] (aliases := [(idx .r13 .rdx, (0, 0))])
/-- The word at `p + 8 i` (region 1). -/
def oneS (p i : Reg64) : SState :=
  init [1336, 8] [(.rsp, .ptr 0 8)] (aliases := [(idx p i, (1, 0))])
/-- `order[j]` at byte `16 + RSI` of the frame, RSI below `1264`. -/
def ordS : SState := init [1336] [(.rsp, .ptr 0 8)] (bounds := [(.reg .rsi, 1264)])

/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `8 n`, as `b3` computes it from R15 = `n`. -/
abbrev e8n : Sym := .bin .mul .W64 (.reg .r15) (.lit 8)

/-- `8 n - 8`. -/
abbrev eM8 : Sym := .bin .add .W64 (.reg .rbp) (.lit 18446744073709551608)
/-- `n`, as `b4` computes it: `(8 n - 8) / 8 + 1`. -/
abbrev eN : Sym := .bin .add .W64 (.bin .shr .W64 eM8 (.lit 3)) (.lit 1)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b0 entryS)
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 quadS
sym_block run_b9 := exec b9 bodyS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 ordOneS
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 bodyS
sym_block run_b14 := exec b14 bodyS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 bodyS
sym_block run_b18 := exec b18 bodyS
sym_block run_b19 := exec b19 ordS
sym_block run_b20 := exec b20 (oneS .r14 .rcx)
sym_block run_b21 := exec b21 (oneS .r12 .rcx)
sym_block run_b22 := exec b22 bodyS
sym_block run_b23 := exec b23 bodyS
sym_block run_b24 := exec b24 bodyS
sym_block run_b25 := exec b25 bodyS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (SBool.cmp .ult .W64 (.reg .rcx) (.reg .rsi)).not NativeRustcVmX64.Vm.StackOffsets.label_3) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem exit_b1 : exec b1 (after b0 entryS) =
    some (after b1 (after b0 entryS), .ret (.load 0 1328 8)) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : EpiOk 1328 [] (after b1 (after b0 entryS)) = true ∧
    (after b1 (after b0 entryS)).mem = [] ∧ (after b1 (after b0 entryS)).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem exit_b2 : exec b2 (after b0 entryS) =
    some (after b2 (after b0 entryS), .call NativeRustcVmX64.Vm.Memset.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : ProOk 1328 0 slots (after b2 (after b0 entryS)) = true ∧
    (after b2 (after b0 entryS)).reg .rdi = some (.ptr 0 16) ∧
    (after b2 (after b0 entryS)).reg .rsi = some (.lit 0) ∧
    (after b2 (after b0 entryS)).reg .rdx = some (.lit 1264) ∧
    (after b2 (after b0 entryS)).reg .rbx = some (.reg .rcx) ∧
    (after b2 (after b0 entryS)).reg .r12 = some (.reg .rdi) ∧
    (after b2 (after b0 entryS)).reg .r13 = some (.ptr 0 16) ∧
    (after b2 (after b0 entryS)).reg .r14 = some (.reg .rdx) ∧
    (after b2 (after b0 entryS)).reg .r15 = some (.reg .rsi) ∧
    (∀ w ∈ (after b2 (after b0 entryS)).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 1280 ≤ w.off)) := by
  decide +kernel

public theorem exit_b3 : exec b3 bodyS = some (after b3 bodyS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .r15) (.reg .r15)) (.lit 0))
      NativeRustcVmX64.Vm.StackOffsets.label_6) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 1328 8 slots (after b3 bodyS) = true ∧ (after b3 bodyS).mem = [] ∧
    (after b3 bodyS).reg .rbp = some e8n ∧
    Keeps (after b3 bodyS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b4 : exec b4 bodyS = some (after b4 bodyS,
    .cond (SBool.cmp .ult .W64 eM8 (.lit 56)).not NativeRustcVmX64.Vm.StackOffsets.label_7) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 1328 8 slots (after b4 bodyS) = true ∧ (after b4 bodyS).mem = [] ∧
    (after b4 bodyS).reg .rax =
      some (.bin .and .W32 (.un .trunc .W32 eN) (.lit 7)) ∧
    (after b4 bodyS).reg .rcx = some eM8 ∧ (after b4 bodyS).reg .rdx = some eN ∧
    Keeps (after b4 bodyS) cs = true := by
  decide +kernel

public theorem exit_b5 : exec b5 bodyS = some (after b5 bodyS, .jump NativeRustcVmX64.Vm.StackOffsets.label_10) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 1328 8 slots (after b5 bodyS) = true ∧ (after b5 bodyS).mem = [] ∧
    (after b5 bodyS).reg .rcx = some (.lit 0) ∧
    Keeps (after b5 bodyS) (.rax :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b6 : exec b6 bodyS = some (after b6 bodyS, .jump NativeRustcVmX64.Vm.StackOffsets.label_13) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 1328 8 slots (after b6 bodyS) = true ∧ (after b6 bodyS).mem = [] ∧
    (after b6 bodyS).reg .rdi = some (.ptr 0 16) ∧ (after b6 bodyS).reg .rsi = some (.lit 0) ∧
    (after b6 bodyS).reg .rdx = some (.reg .r12) ∧ (after b6 bodyS).reg .rcx = some (.lit 0) ∧
    Keeps (after b6 bodyS) cs = true := by
  decide +kernel

public theorem exit_b7 : exec b7 bodyS = some (after b7 bodyS, .fall) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk 1328 8 slots (after b7 bodyS) = true ∧ (after b7 bodyS).mem = [] ∧
    (after b7 bodyS).reg .rdx = some (.bin .and .W64 (.reg .rdx) (.lit 18446744073709551608)) ∧
    (after b7 bodyS).reg .r13 = some (.ptr 0 16) ∧ (after b7 bodyS).reg .rcx = some (.lit 0) ∧
    Keeps (after b7 bodyS) [.rax, .rbx, .rbp, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b8 : exec b8 quadS = some (after b8 quadS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .rcx) (.lit 8)) (.reg .rdx)).not
      NativeRustcVmX64.Vm.StackOffsets.label_8) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : SubOk slots (after b8 quadS) = true ∧
    (∀ t < 8, findWrite 0 t (after b8 quadS).mem = some (.reg .rcx, t)) ∧
    (∀ k ∈ [1, 2, 3, 4, 5, 6], ∀ t < 8, findWrite 0 (8 * k + t) (after b8 quadS).mem =
      some (.bin .add .W64 (.reg .rcx) (.lit k), t)) ∧
    (∀ t < 8, findWrite 0 (56 + t) (after b8 quadS).mem =
      some (.bin .add .W64 (.lit 7) (.reg .rcx), t)) ∧
    (after b8 quadS).reg .rcx = some (.bin .add .W64 (.reg .rcx) (.lit 8)) ∧
    (after b8 quadS).reg .r13 = some (.ptr 0 64) ∧
    Keeps (after b8 quadS) [.rax, .rdx, .rbx, .rbp, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b9 : exec b9 bodyS = some (after b9 bodyS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rax) (.reg .rax)) (.lit 0))
      NativeRustcVmX64.Vm.StackOffsets.label_12) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 1328 8 slots (after b9 bodyS) = true ∧ (after b9 bodyS).mem = [] ∧
    Keeps (after b9 bodyS) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b10 : exec b10 bodyS = some (after b10 bodyS, .fall) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 1328 8 slots (after b10 bodyS) = true ∧
    (after b10 bodyS).mem = [] ∧ (after b10 bodyS).reg .rdx = some (.lit 0) ∧
    Keeps (after b10 bodyS) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b11 : exec b11 ordOneS = some (after b11 ordOneS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.bin .add .W64 (.reg .rdx) (.lit 1))).not
      NativeRustcVmX64.Vm.StackOffsets.label_11) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : SubOk slots (after b11 ordOneS) = true ∧
    (∀ t < 8, findWrite 0 t (after b11 ordOneS).mem =
      some (.bin .add .W64 (.reg .rcx) (.reg .rdx), t)) ∧
    (after b11 ordOneS).reg .rdx = some (.bin .add .W64 (.reg .rdx) (.lit 1)) ∧
    Keeps (after b11 ordOneS) (.rax :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b12 : exec b12 bodyS = some (after b12 bodyS, .fall) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 1328 8 slots (after b12 bodyS) = true ∧
    (after b12 bodyS).mem = [] ∧ (after b12 bodyS).reg .rdi = some (.ptr 0 16) ∧
    (after b12 bodyS).reg .rsi = some (.reg .r15) ∧ (after b12 bodyS).reg .rdx = some (.reg .r12) ∧
    (after b12 bodyS).reg .rcx = some (.reg .r15) ∧ Keeps (after b12 bodyS) cs = true := by
  decide +kernel

public theorem exit_b13 : exec b13 bodyS = some (after b13 bodyS,
    .call NativeRustcVmX64.Vm.InsertionSortOfStackOffsets.entryLabel) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 1328 0 slots (after b13 bodyS) = true ∧
    (∀ w ∈ (after b13 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps (after b13 bodyS) (.rdi :: .rsi :: .rdx :: .rcx :: cs) = true := by
  decide +kernel

public theorem exit_b14 : exec b14 bodyS = some (after b14 bodyS, .jump NativeRustcVmX64.Vm.StackOffsets.label_14) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 1328 8 slots (after b14 bodyS) = true ∧
    (after b14 bodyS).mem = [] ∧ (after b14 bodyS).reg .rax = some (.lit 0) ∧
    (after b14 bodyS).reg .rsi = some (.lit 0) ∧ (after b14 bodyS).reg .rdx = some (.lit 0) ∧
    Keeps (after b14 bodyS) cs = true := by
  decide +kernel

public theorem exit_b16 : exec b16 bodyS = some (after b16 bodyS, .fall) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : MidOk 1328 8 slots (after b16 bodyS) = true ∧
    (after b16 bodyS).mem = [] ∧ (after b16 bodyS).reg .rcx = some (.lit 0) ∧
    Keeps (after b16 bodyS) (.rax :: .rsi :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b17 : exec b17 bodyS = some (after b17 bodyS,
    .cond (SBool.cmp .addC .W64 (.bin .shl .W64 (.lit 1) (.reg .rcx)) (.reg .rdx))
      NativeRustcVmX64.Vm.StackOffsets.label_20) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 1328 8 slots (after b17 bodyS) = true ∧
    (after b17 bodyS).mem = [] ∧
    (after b17 bodyS).reg .rsi = some (.bin .add .W64 (.lit 8) (.reg .rsi)) ∧
    (after b17 bodyS).reg .rdx =
      some (.bin .add .W64 (.bin .shl .W64 (.lit 1) (.reg .rcx)) (.reg .rdx)) ∧
    Keeps (after b17 bodyS) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b18 : exec b18 bodyS = some (after b18 bodyS,
    .cond (SBool.cmp .eq .W64 (.reg .rbp) (.reg .rsi)) NativeRustcVmX64.Vm.StackOffsets.label_22) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 1328 8 slots (after b18 bodyS) = true ∧
    (after b18 bodyS).mem = [] ∧ Keeps (after b18 bodyS) (.rax :: .rsi :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b19 : exec b19 ordS = some (after b19 ordS,
    .cond (SBool.cmp .ult .W64 (.loadx 0 16 (.reg .rsi) 8) (.reg .rbx)).not NativeRustcVmX64.Vm.StackOffsets.label_20) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 1328 8 slots (after b19 ordS) = true ∧
    (after b19 ordS).mem = [] ∧ (after b19 ordS).reg .rcx = some (.loadx 0 16 (.reg .rsi) 8) ∧
    Keeps (after b19 ordS) (.rax :: .rsi :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b20 : exec b20 (oneS .r14 .rcx) = some (after b20 (oneS .r14 .rcx),
    .cond (SBool.cmp .ult .W64 (.reg .rcx) (.reg .r15)).not NativeRustcVmX64.Vm.StackOffsets.label_17) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : MidOk 1328 8 slots (after b20 (oneS .r14 .rcx)) = true ∧
    (∀ w ∈ (after b20 (oneS .r14 .rcx)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 8) ∧
    (∀ t < 8, findWrite 1 t (after b20 (oneS .r14 .rcx)).mem = some (.reg .rdx, t)) ∧
    Keeps (after b20 (oneS .r14 .rcx)) (.rax :: .rcx :: .rsi :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b21 : exec b21 (oneS .r12 .rcx) = some (after b21 (oneS .r12 .rcx),
    .cond ((SBool.cmp .ult .W64 (.load 1 0 8) (.lit 63)).or
      (SBool.cmp .eq .W64 (.load 1 0 8) (.lit 63))) NativeRustcVmX64.Vm.StackOffsets.label_19) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : MidOk 1328 8 slots (after b21 (oneS .r12 .rcx)) = true ∧
    (after b21 (oneS .r12 .rcx)).mem = [] ∧
    (after b21 (oneS .r12 .rcx)).reg .rcx = some (.load 1 0 8) ∧
    Keeps (after b21 (oneS .r12 .rcx)) (.rax :: .rsi :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b22 : exec b22 bodyS = some (after b22 bodyS, .jump NativeRustcVmX64.Vm.StackOffsets.label_21) :=
  run_b22.trans (by rw [after_eq run_b22])
public theorem ok_b22 : MidOk 1328 8 slots (after b22 bodyS) = true ∧
    (after b22 bodyS).mem = [] ∧ Keeps (after b22 bodyS) (.rax :: cs) = true := by
  decide +kernel

public theorem exit_b23 : exec b23 bodyS = some (after b23 bodyS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b23.trans (by rw [after_eq run_b23])
public theorem ok_b23 : MidOk 1328 0 slots (after b23 bodyS) = true ∧
    (∀ w ∈ (after b23 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b23 bodyS).reg .rdi = some (.ite (SBool.cmp .ult .W64 (.reg .rdx) (.lit 1)).not
      (.bin .sub .W64 (.reg .rdx) (.lit 1)) (.lit 0)) ∧
    Keeps (after b23 bodyS) cs = true := by
  decide +kernel

public theorem exit_b24 : exec b24 bodyS = some (after b24 bodyS, .fall) :=
  run_b24.trans (by rw [after_eq run_b24])
public theorem ok_b24 : MidOk 1328 8 slots (after b24 bodyS) = true ∧
    (after b24 bodyS).mem = [] ∧ (after b24 bodyS).reg .rax = some (.lit 1) ∧
    (after b24 bodyS).reg .rdx = some (.reg .rax) ∧ Keeps (after b24 bodyS) cs = true := by
  decide +kernel

public theorem exit_b25 : exec b25 bodyS = some (after b25 bodyS, .ret (.load 0 1328 8)) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : EpiOk 1328 slots (after b25 bodyS) = true ∧ (after b25 bodyS).mem = [] ∧
    Keeps (after b25 bodyS) [.rax, .rdx] = true := by
  decide +kernel

end NativeRustcVmX64.Layout.StackOffsets
