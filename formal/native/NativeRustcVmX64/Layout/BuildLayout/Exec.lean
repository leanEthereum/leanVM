module

public import NativeRustcVmX64.Layout.BuildFrame
public import NativeRustcVmX64.Code.Vm.BuildLayout
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names
public import NativeRustcVmX64.Code.Vm.ColumnKappas.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names
public meta import NativeRustcVmX64.Code.Vm.BuildLayout
public meta import NativeRustcVmX64.Layout.BuildFrame

/-!
# `build_layout`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 1360-byte frame below the entry's RSP and the return address (RSP at offset `8`
in the body, a callee's return address at `0`): row counts `3` to `5` and the bytecode's log-size
kept at `16` to `40`, `kappas` at `48`, the six pushed registers from `1312`.

- `entryS`: `b0` (the prologue, the power-of-two test);
- `bodyS`: `b1` (`bit_length(n)`), `b2` (the log-sizes' checks), `b16` (`placements_of`), `b17`,
  `b19`, `b20` (the epilogue);
- `rowS`: region 1 the six row counts at R14 (`b3` to `b8`, the checks);
- `layS`: region 1 the layout's first 120 bytes at R13 (`b9` to `b15`: the sizes, heights, rows,
  each height a call of `bit_length`, then `column_kappas`; `b18` the stack's log-size).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript
open NativeRustcVmX64.Layout.BuildFrame (Keeps)

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(1352, .rbp), (1344, .r15), (1336, .r14), (1328, .r13), (1320, .r12), (1312, .rbx)]

/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

def entryS : SState := init [1368] [(.rsp, .ptr 0 1360)]
def bodyS : SState := init [1368] [(.rsp, .ptr 0 8)]
def rowS : SState := init [1368, 48] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]
def layS : SState := init [1368, 120] [(.rsp, .ptr 0 8), (.r13, .ptr 1 0)]

/-- `x - 1`. -/
abbrev dec (x : Sym) : Sym := .bin .add .W64 x (.lit 18446744073709551615)
/-- `b0`'s test: `n ^ (n - 1) ≤ n - 1`, `n` not a power of two. -/
abbrev c0 : SBool :=
  (SBool.cmp .ult .W64 (.bin .xor .W64 (.reg .rdi) (dec (.reg .rdi))) (dec (.reg .rdi))).or
    (SBool.cmp .eq .W64 (.bin .xor .W64 (.reg .rdi) (dec (.reg .rdi))) (dec (.reg .rdi)))
/-- The bit length less `5`. -/
abbrev rM5 : Sym := .bin .add .W64 (.lit 18446744073709551611) (.reg .rax)
/-- A flag byte. -/
abbrev flag (b : SBool) : Sym := .ite b.not (.lit 1) (.lit 0)
/-- `b2`'s test: the memory's log-size outside `1 … 30` or the bit length below `5`. -/
abbrev c2 : SBool :=
  (SBool.cmp .eq .W8 (.bin .or .W8
    (.bin .merge .W8 (dec (.reg .rbx)) (flag (.cmp .ult .W64 (dec (.reg .rbx)) (.lit 30))))
    (.bin .merge .W8 (.reg .rcx) (flag (.cmp .ult .W64 rM5 (.lit 18446744073709551612)))))
    (.lit 0)).not
/-- A row count past `2 ^ 30`. -/
abbrev cRow (o : Nat) : SBool :=
  (SBool.cmp .ult .W64 (.load 1 o 8) (.lit 1073741824)).not.and
    (SBool.cmp .eq .W64 (.load 1 o 8) (.lit 1073741824)).not
/-- `b8`'s test: the last row count past `2 ^ 30` or the bytecode's log-size past `30`. -/
abbrev c8 : SBool :=
  (SBool.cmp .eq .W8 (.bin .or .W8
    (.bin .merge .W8 (.reg .rdx) (flag (.cmp .ult .W32 (.reg .rax) (.lit 31))))
    (.bin .merge .W8 (.reg .rcx) (flag (.cmp .ult .W64 (.load 1 40 8) (.lit 1073741825)))))
    (.lit 0)).not
/-- `x - 1`, saturating. -/
abbrev sat (x z : Sym) : Sym := .ite (.cmp .ult .W64 x (.lit 1)) z (.bin .sub .W64 x (.lit 1))

/-- The writes all in region `r` miss the words at the offsets `os`. -/
def Misses (r : Nat) (os : List Nat) (S : SState) : Bool :=
  S.mem.all fun w ↦ w.r != r || os.all fun o ↦ decide (w.off + w.n ≤ o ∨ o + 8 ≤ w.off)

/-- The words of region 1 written: `v` at `o`. -/
def W1 (S : SState) (o : Nat) (v : Sym) : Prop := ∀ t < 8, findWrite 1 (o + t) S.mem = some (v, t)

/-- The words of region 0 written: `v` at `o`. -/
def W0 (S : SState) (o : Nat) (v : Sym) : Prop := ∀ t < 8, findWrite 0 (o + t) S.mem = some (v, t)

instance (S : SState) (o : Nat) (v : Sym) : Decidable (W1 S o v) := by unfold W1; infer_instance
instance (S : SState) (o : Nat) (v : Sym) : Decidable (W0 S o v) := by unfold W0; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 bodyS
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 rowS
sym_block run_b4 := exec b4 rowS
sym_block run_b5 := exec b5 rowS
sym_block run_b6 := exec b6 rowS
sym_block run_b7 := exec b7 rowS
sym_block run_b8 := exec b8 rowS
sym_block run_b9 := exec b9 layS
sym_block run_b10 := exec b10 layS
sym_block run_b11 := exec b11 layS
sym_block run_b12 := exec b12 layS
sym_block run_b13 := exec b13 layS
sym_block run_b14 := exec b14 layS
sym_block run_b15 := exec b15 layS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 bodyS
sym_block run_b18 := exec b18 layS
sym_block run_b19 := exec b19 bodyS
sym_block run_b20 := exec b20 bodyS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 1360 8 slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .r14 = some (.reg .rdx) ∧ Keeps (after b0 entryS) [.rdi, .rsi, .rcx] = true := by
  decide +kernel

public theorem exit_b1 : exec b1 bodyS = some (after b1 bodyS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk 1360 0 slots (after b1 bodyS) = true ∧
    (∀ w ∈ (after b1 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 bodyS).reg .rbx = some (.reg .rsi) ∧ (after b1 bodyS).reg .r13 = some (.reg .rcx) ∧
    Keeps (after b1 bodyS) [.rdi, .r14] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS, .cond c2 NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : MidOk 1360 8 slots (after b2 bodyS) = true ∧ (after b2 bodyS).mem = [] ∧
    (after b2 bodyS).reg .rax = some rM5 ∧ Keeps (after b2 bodyS) cs = true := by
  decide +kernel

public theorem exit_b3 : exec b3 rowS = some (after b3 rowS, .cond (cRow 0) NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 1360 8 slots (after b3 rowS) = true ∧ (after b3 rowS).mem = [] ∧
    (after b3 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b3 rowS).reg .r12 = some (.load 1 0 8) ∧
    Keeps (after b3 rowS) [.rax, .rbx, .rbp, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b4 : exec b4 rowS = some (after b4 rowS, .cond (cRow 8) NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 1360 8 slots (after b4 rowS) = true ∧ (after b4 rowS).mem = [] ∧
    (after b4 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b4 rowS).reg .rbp = some (.load 1 8 8) ∧
    Keeps (after b4 rowS) [.rax, .rbx, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 rowS = some (after b5 rowS, .cond (cRow 16) NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 1360 8 slots (after b5 rowS) = true ∧ (after b5 rowS).mem = [] ∧
    (after b5 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b5 rowS).reg .r15 = some (.load 1 16 8) ∧
    Keeps (after b5 rowS) [.rax, .rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

public theorem exit_b6 : exec b6 rowS = some (after b6 rowS, .cond (cRow 24) NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 1360 8 slots (after b6 rowS) = true ∧ (after b6 rowS).mem = [] ∧
    (after b6 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b6 rowS).reg .r8 = some (.load 1 24 8) ∧
    Keeps (after b6 rowS) [.rax, .rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b7 : exec b7 rowS = some (after b7 rowS, .cond (cRow 32) NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk 1360 8 slots (after b7 rowS) = true ∧ (after b7 rowS).mem = [] ∧
    (after b7 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b7 rowS).reg .rdi = some (.load 1 32 8) ∧
    Keeps (after b7 rowS) [.rax, .rbx, .rbp, .r12, .r13, .r15, .r8] = true := by
  decide +kernel

public theorem exit_b8 : exec b8 rowS = some (after b8 rowS, .cond c8 NativeRustcVmX64.Vm.BuildLayout.label_17) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 1360 8 slots (after b8 rowS) = true ∧ (after b8 rowS).mem = [] ∧
    (after b8 rowS).reg .r14 = some (.ptr 1 0) ∧
    (after b8 rowS).reg .rsi = some (.load 1 40 8) ∧
    Keeps (after b8 rowS) [.rax, .rbx, .rbp, .r12, .r13, .r15, .r8, .rdi] = true := by
  decide +kernel

public theorem exit_b9 : exec b9 layS = some (after b9 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 1360 0 slots (after b9 layS) = true ∧
    (∀ w ∈ (after b9 layS).mem, w.r = 0 → w.off + w.n ≤ 48) ∧
    W1 (after b9 layS) 0 (.reg .rbx) ∧ W1 (after b9 layS) 8 (.reg .rax) ∧
    W0 (after b9 layS) 16 (.reg .r8) ∧ W0 (after b9 layS) 24 (.reg .rdi) ∧
    W0 (after b9 layS) 32 (.reg .rsi) ∧ W0 (after b9 layS) 40 (.reg .rax) ∧
    (after b9 layS).reg .rdi = some (sat (.reg .r12) (.lit 0)) ∧
    (after b9 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b9 layS) [.rbx, .rbp, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b10 : exec b10 layS = some (after b10 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 1360 0 slots (after b10 layS) = true ∧
    (∀ w ∈ (after b10 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8] (after b10 layS) = true ∧
    W1 (after b10 layS) 72 (.reg .r12) ∧ W1 (after b10 layS) 24 (.reg .rax) ∧
    (after b10 layS).reg .rdi = some (sat (.reg .rbp) (.lit 0)) ∧
    (after b10 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b10 layS) [.rbx, .rbp, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 layS = some (after b11 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 1360 0 slots (after b11 layS) = true ∧
    (∀ w ∈ (after b11 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8, 72, 24] (after b11 layS) = true ∧
    W1 (after b11 layS) 80 (.reg .rbp) ∧ W1 (after b11 layS) 32 (.reg .rax) ∧
    (after b11 layS).reg .rdi = some (sat (.reg .r15) (.lit 0)) ∧
    (after b11 layS).reg .r12 = some (.lit 0) ∧
    (after b11 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b11 layS) [.rbx, .rbp, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b12 : exec b12 layS = some (after b12 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 1360 0 slots (after b12 layS) = true ∧
    (∀ w ∈ (after b12 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8, 72, 24, 80, 32] (after b12 layS) = true ∧
    W1 (after b12 layS) 88 (.reg .r15) ∧ W1 (after b12 layS) 40 (.reg .rax) ∧
    (after b12 layS).reg .rdi = some (sat (.load 0 16 8) (.reg .r12)) ∧
    (after b12 layS).reg .r15 = some (.load 0 16 8) ∧
    (after b12 layS).reg .r12 = some (.lit 0) ∧
    (after b12 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b12 layS) [.rbx, .rbp, .r14] = true := by
  decide +kernel

public theorem exit_b13 : exec b13 layS = some (after b13 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 1360 0 slots (after b13 layS) = true ∧
    (∀ w ∈ (after b13 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8, 72, 24, 80, 32, 88, 40] (after b13 layS) = true ∧
    W1 (after b13 layS) 96 (.reg .r15) ∧ W1 (after b13 layS) 48 (.reg .rax) ∧
    (after b13 layS).reg .rdi = some (sat (.load 0 24 8) (.reg .r12)) ∧
    (after b13 layS).reg .r15 = some (.load 0 24 8) ∧
    (after b13 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b13 layS) [.rbx, .rbp, .r12, .r14] = true := by
  decide +kernel

public theorem exit_b14 : exec b14 layS = some (after b14 layS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 1360 0 slots (after b14 layS) = true ∧
    (∀ w ∈ (after b14 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8, 72, 24, 80, 32, 88, 40, 96, 48] (after b14 layS) = true ∧
    W1 (after b14 layS) 104 (.reg .r15) ∧ W1 (after b14 layS) 56 (.reg .rax) ∧
    (after b14 layS).reg .rdi = some (sat (.load 0 32 8) (.reg .r12)) ∧
    (after b14 layS).reg .r15 = some (.load 0 32 8) ∧
    (after b14 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b14 layS) [.rbx, .rbp, .r12, .r14] = true := by
  decide +kernel

public theorem exit_b15 : exec b15 layS = some (after b15 layS,
    .call NativeRustcVmX64.Vm.ColumnKappas.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 1360 0 slots (after b15 layS) = true ∧
    (∀ w ∈ (after b15 layS).mem, w.r = 0 → w.off + w.n ≤ 8) ∧
    Misses 1 [0, 8, 72, 24, 80, 32, 88, 40, 96, 48, 104, 56] (after b15 layS) = true ∧
    W1 (after b15 layS) 112 (.reg .r15) ∧
    W1 (after b15 layS) 64 (.ite (SBool.cmp .ult .W64 (.reg .rax) (.lit 10)).not (.reg .rax) (.lit 9)) ∧
    (after b15 layS).reg .rdi = some (.ptr 0 48) ∧ (after b15 layS).reg .rsi = some (.reg .rbx) ∧
    (after b15 layS).reg .rdx = some (.load 0 40 8) ∧ (after b15 layS).reg .rcx = some (.ptr 1 24) ∧
    (after b15 layS).reg .r12 = some (.ptr 0 48) ∧
    (after b15 layS).reg .r13 = some (.ptr 1 0) ∧
    Keeps (after b15 layS) [.rbx, .rbp, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b16 : exec b16 bodyS = some (after b16 bodyS,
    .call NativeRustcVmX64.Vm.PlacementsOf.entryLabel) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : MidOk 1360 0 slots (after b16 bodyS) = true ∧
    (∀ w ∈ (after b16 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b16 bodyS).reg .rsi = some (.bin .add .W64 (.reg .r13) (.lit 120)) ∧
    (after b16 bodyS).reg .rdi = some (.reg .r12) ∧ Keeps (after b16 bodyS) cs = true := by
  decide +kernel

public theorem exit_b17 : exec b17 bodyS = some (after b17 bodyS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.BuildLayout.label_18) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 1360 8 slots (after b17 bodyS) = true ∧ (after b17 bodyS).mem = [] ∧
    Keeps (after b17 bodyS) (.rax :: .rdx :: cs) = true := by
  decide +kernel

public theorem exit_b18 : exec b18 layS = some (after b18 layS, .jump NativeRustcVmX64.Vm.BuildLayout.label_18) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 1360 8 slots (after b18 layS) = true ∧
    (∀ w ∈ (after b18 layS).mem, w.r = 1) ∧
    Misses 1 [0, 8, 72, 24, 80, 32, 88, 40, 96, 48, 104, 56, 112, 64] (after b18 layS) = true ∧
    W1 (after b18 layS) 16 (.reg .rdx) ∧ Keeps (after b18 layS) [.rax] = true := by
  decide +kernel

public theorem exit_b19 : exec b19 bodyS = some (after b19 bodyS, .fall) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 1360 8 slots (after b19 bodyS) = true ∧ (after b19 bodyS).mem = [] ∧
    (after b19 bodyS).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem exit_b20 : exec b20 bodyS = some (after b20 bodyS, .ret (.load 0 1360 8)) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : EpiOk 1360 slots (after b20 bodyS) = true ∧ (after b20 bodyS).mem = [] ∧
    (after b20 bodyS).reg .rax = some (.bin .merge .W8 (.reg .rax) (.bin .and .W8 (.reg .rax) (.lit 1))) := by
  decide +kernel

end NativeRustcVmX64.Layout.BuildLayout
