module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Layout.Stack.Common
public import NativeRustcVmX64.Code.Vm.Ladder
public import NativeRustcVmX64.Code.Vm.Ladder.Names
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.Ladder
public meta import NativeRustcVmX64.Layout.Stack.Common

/-!
# `ladder`'s blocks, run by the symbolic executor (x86-64)

`ladder` is a leaf: `b0` pushes RBP, R15 to R12, RBX (at `64` to `24` of the 72-byte frame) and
checks the window (else `b11`, `b16` store the `None` tag); `b1` to `b7` pick the level count `n`
(`3` to `6`, in RCX) and the registers of the levels past the third; `b8` compares `n` with
`QUERY_LEVELS`' entry; `b9`, `b10`, `b12`, `b17`, `b18` load the query counts from
`QUERY_TABLE`'s entry; `b13`, `b14` zero the missing ones; `b15` stores the result, `b16` its tag
and returns.

Three environments, each from the machine state its first block starts in:
- `outS` (at the entry, outside the window): region 0 the frame, region 1 the result (RDI);
- `entryA` (at the entry, inside): region 0 the frame, region 1 `QUERY_LEVELS`' entry word (the
  address `b8` computes, `lvSym`), up to `b9` (`H3` to `H6`, by the count);
- `midS` (at `b9`): region 0 the frame (RSP at its base), region 1 the result (RDI), region 2
  `QUERY_TABLE`'s entry row (`qtSym`, as `b9` computes it), to the return (`P3` to `P6`).
-/

namespace NativeRustcVmX64.Layout.Ladder

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Ladder NativeRustcVmX64.Transcript
open NativeRustcVmX64.Layout.Stack (WritesW)

@[expose] public section


/-- The frame's slots. -/
def slots : Slots := [(64, .rbp), (56, .r15), (48, .r14), (40, .r13), (32, .r12), (24, .rbx)]

/-- `x + c`. -/
abbrev addS (r : Reg64) (c : Nat) : Sym := .bin .add .W64 (.reg r) (.lit c)

/-- `QUERY_LEVELS`' entry `(r - 1, μ - 16)`, as `b8` computes it. -/
def lvSym : Sym :=
  .bin .add .W64 (.bin .add .W64 (.bin .add .W64
    (.bin .mul .W64 (addS .rdx 18446744073709551615) (.lit 120))
    (.label NativeRustcVmX64.Vm.Symbols.rodata12Label)) (.bin .mul .W64 (.reg .rsi) (.lit 8))) (.lit 18446744073709551488)

/-- `QUERY_TABLE`'s entry row `(r - 1, μ - 16)`, as `b9` computes it from R15 = `r - 1` and
R14 = `μ - 16`. -/
def qtSym : Sym :=
  .bin .add .W64 (.bin .mul .W64 (.reg .r15) (.lit 720)) (.bin .add .W64 (.label NativeRustcVmX64.Vm.Symbols.rodata11Label)
    (.bin .shl .W64 (.bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .r14) (.lit 2))) (.lit 4)))

/-- `b0`'s window test: outside. -/
def winSym : SBool :=
  .cmp .eq .W8 (.bin .and .W8
    (.bin .merge .W8 (.reg .rax)
      (.ite (.cmp .ult .W64 (addS .rsi 18446744073709551600) (.lit 15)) (.lit 1) (.lit 0)))
    (.bin .merge .W8 (.reg .rcx)
      (.ite (.cmp .ult .W64 (addS .rdx 18446744073709551615) (.lit 4)) (.lit 1) (.lit 0))))
    (.lit 0)

/-- `b1`, `b3`, `b5`'s test: `μ ≥ c`, signed. -/
def geSym (c : Nat) : SBool :=
  (SBool.msb .W64 (.bin .sub .W64 (.reg .rsi) (.lit c))).beq (.cmp .subV .W64 (.reg .rsi) (.lit c))

/-- `b8`'s test: the count is not `QUERY_LEVELS`' entry. -/
def cntSym (n : Nat) : SBool := (SBool.cmp .eq .W64 (.load 1 0 8) (.lit n)).not

/-- `b9`, `b12`, `b17`'s tests on `n - 1`. -/
def nm1 : Sym := addS .rcx 18446744073709551615

def outS : SState := init [80, 160] [(.rsp, .ptr 0 72), (.rdi, .ptr 1 0)]
def entryA : SState := init [80, 8] [(.rsp, .ptr 0 72)] [] [] [(lvSym, (1, 0))]
def midS : SState := init [80, 160, 48] [(.rsp, .ptr 0 0), (.rdi, .ptr 1 0)] [] [] [(qtSym, (2, 0))]

def O0 : SState := after b0 outS
def O11 : SState := after b11 O0
def A0 : SState := after b0 entryA
def A1 : SState := after b1 A0
def A2 : SState := after b2 A1
def A3 : SState := after b3 A1
def A4 : SState := after b4 A3
def A5 : SState := after b5 A3
def A6 : SState := after b6 A5
def A7 : SState := after b7 A5
def H3 : SState := after b8 A2
def H4 : SState := after b8 A4
def H5 : SState := after b8 A6
def H6 : SState := after b8 A7
def B9 : SState := after b9 midS
def B10 : SState := after b10 B9
def B12 : SState := after b12 B9
def B17 : SState := after b17 B12
def B18 : SState := after b18 B17
def C13a : SState := after b13 B10
def C13b : SState := after b13 B12
def C14a : SState := after b14 C13a
def C14b : SState := after b14 C13b
def C14c : SState := after b14 B17
def C15a : SState := after b15 C14a
def C15b : SState := after b15 C14b
def C15c : SState := after b15 C14c
def C15d : SState := after b15 B18

/-- The result's words every path stores, but the query counts of levels `3` to `5`. -/
def common : List (Nat × Sym) :=
  [(0, .lit 1), (8, .lit 6), (16, .reg .rdx), (24, .load 2 0 8), (32, .lit 4), (40, addS .rdx 3),
    (48, .load 2 8 8), (56, .lit 4), (64, addS .rdx 6), (72, .load 2 16 8), (80, .reg .r12),
    (88, .reg .r9), (104, .reg .r13), (112, .reg .r10), (128, .reg .r11), (136, .reg .rbx),
    (152, .reg .rcx)]

/-- A path's end: the registers restored, the result's words, the writes in the frame's scratch
and the result. -/
def EndOk (S : SState) (v3 v4 v5 : Sym) : Prop :=
  EpiOk 72 slots S = true ∧
    (∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 24) ∨ (w.r = 1 ∧ w.off + w.n ≤ 160)) ∧
    WritesW 1 (common ++ [(96, v3), (120, v4), (144, v5)]) S = true

instance (S : SState) (v3 v4 v5 : Sym) : Decidable (EndOk S v3 v4 v5) := by
  unfold EndOk; infer_instance

/-- At `b9` by a head path: the prologue done, the registers of the count `n`. -/
def HeadOk (S : SState) (n : Nat) : Prop :=
  ProOk 72 0 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 72) ∧
    S.reg .rdi = some (.reg .rdi) ∧ S.reg .rdx = some (.reg .rdx) ∧
    S.reg .rcx = some (.lit n) ∧ S.reg .r14 = some (addS .rsi 18446744073709551600) ∧
    S.reg .r15 = some (addS .rdx 18446744073709551615) ∧
    (3 < n → S.reg .r12 = some (.lit 4) ∧ S.reg .r9 = some (addS .rdx 9)) ∧
    (4 < n → S.reg .r13 = some (.lit 4) ∧ S.reg .r10 = some (addS .rdx 12)) ∧
    (5 < n → S.reg .r11 = some (.lit 4) ∧ S.reg .rbx = some (addS .rdx 15))

instance (S : SState) (n : Nat) : Decidable (HeadOk S n) := by unfold HeadOk; infer_instance

end

set_option Elab.async false

sym_block run_o0 := exec b0 outS
sym_block run_o11 := exec b11 O0
sym_block run_o16 := exec b16 O11
sym_block run_a0 := exec b0 entryA
sym_block run_a1 := exec b1 A0
sym_block run_a2 := exec b2 A1
sym_block run_a3 := exec b3 A1
sym_block run_a4 := exec b4 A3
sym_block run_a5 := exec b5 A3
sym_block run_a6 := exec b6 A5
sym_block run_a7 := exec b7 A5
sym_block run_a8a := exec b8 A2
sym_block run_a8b := exec b8 A4
sym_block run_a8c := exec b8 A6
sym_block run_a8d := exec b8 A7
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 B9
sym_block run_b12 := exec b12 B9
sym_block run_b17 := exec b17 B12
sym_block run_b18 := exec b18 B17
sym_block run_b13a := exec b13 B10
sym_block run_b13b := exec b13 B12
sym_block run_b14a := exec b14 C13a
sym_block run_b14b := exec b14 C13b
sym_block run_b14c := exec b14 B17
sym_block run_b15a := exec b15 C14a
sym_block run_b15b := exec b15 C14b
sym_block run_b15c := exec b15 C14c
sym_block run_b15d := exec b15 B18
sym_block run_b16a := exec b16 C15a
sym_block run_b16b := exec b16 C15b
sym_block run_b16c := exec b16 C15c
sym_block run_b16d := exec b16 C15d

public theorem exit_o0 : exec b0 outS = some (O0, .cond winSym NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_o0.trans (by rw [show O0 = _ from after_eq run_o0]; rfl)
public theorem exit_o11 : exec b11 O0 = some (O11, .jump NativeRustcVmX64.Vm.Ladder.label_16) :=
  run_o11.trans (by rw [show O11 = _ from after_eq run_o11])
public theorem exit_o16 : exec b16 O11 = some (after b16 O11, .ret (.load 0 72 8)) :=
  run_o16.trans (by rw [after_eq run_o16])
public theorem end_o16 : keeps outS (after b16 O11) = true ∧
    (after b16 O11).reg .rsp = some (.ptr 0 80) ∧
    (∀ w ∈ (after b16 O11).mem, (w.r = 0 ∧ w.off + w.n ≤ 72) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) ∧
    WritesW 1 [(0, .lit 0)] (after b16 O11) = true := by
  decide +kernel

public theorem exit_a0 : exec b0 entryA = some (A0, .cond winSym NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_a0.trans (by rw [show A0 = _ from after_eq run_a0]; rfl)
public theorem exit_a1 : exec b1 A0 = some (A1, .cond (geSym 20) NativeRustcVmX64.Vm.Ladder.label_3) :=
  run_a1.trans (by rw [show A1 = _ from after_eq run_a1]; rfl)
public theorem exit_a2 : exec b2 A1 = some (A2, .jump NativeRustcVmX64.Vm.Ladder.label_8) :=
  run_a2.trans (by rw [show A2 = _ from after_eq run_a2])
public theorem exit_a3 : exec b3 A1 = some (A3, .cond (geSym 24) NativeRustcVmX64.Vm.Ladder.label_5) :=
  run_a3.trans (by rw [show A3 = _ from after_eq run_a3]; rfl)
public theorem exit_a4 : exec b4 A3 = some (A4, .jump NativeRustcVmX64.Vm.Ladder.label_8) :=
  run_a4.trans (by rw [show A4 = _ from after_eq run_a4])
public theorem exit_a5 : exec b5 A3 = some (A5, .cond (geSym 28) NativeRustcVmX64.Vm.Ladder.label_7) :=
  run_a5.trans (by rw [show A5 = _ from after_eq run_a5]; rfl)
public theorem exit_a6 : exec b6 A5 = some (A6, .jump NativeRustcVmX64.Vm.Ladder.label_8) :=
  run_a6.trans (by rw [show A6 = _ from after_eq run_a6])
public theorem exit_a7 : exec b7 A5 = some (A7, .fall) :=
  run_a7.trans (by rw [show A7 = _ from after_eq run_a7])
public theorem exit_a8a : exec b8 A2 = some (H3, .cond (cntSym 3) NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_a8a.trans (by rw [show H3 = _ from after_eq run_a8a]; rfl)
public theorem exit_a8b : exec b8 A4 = some (H4, .cond (cntSym 4) NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_a8b.trans (by rw [show H4 = _ from after_eq run_a8b]; rfl)
public theorem exit_a8c : exec b8 A6 = some (H5, .cond (cntSym 5) NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_a8c.trans (by rw [show H5 = _ from after_eq run_a8c]; rfl)
public theorem exit_a8d : exec b8 A7 = some (H6, .cond (cntSym 6) NativeRustcVmX64.Vm.Ladder.label_11) :=
  run_a8d.trans (by rw [show H6 = _ from after_eq run_a8d]; rfl)
public theorem ok_h3 : HeadOk H3 3 := by decide +kernel
public theorem ok_h4 : HeadOk H4 4 := by decide +kernel
public theorem ok_h5 : HeadOk H5 5 := by decide +kernel
public theorem ok_h6 : HeadOk H6 6 := by decide +kernel

public theorem exit_b9 : exec b9 midS = some (B9,
    .cond (SBool.cmp .eq .W64 nm1 (.lit 2)).not NativeRustcVmX64.Vm.Ladder.label_12) :=
  run_b9.trans (by rw [show B9 = _ from after_eq run_b9]; rfl)
public theorem exit_b10 : exec b10 B9 = some (B10, .jump NativeRustcVmX64.Vm.Ladder.label_13) :=
  run_b10.trans (by rw [show B10 = _ from after_eq run_b10])
public theorem exit_b12 : exec b12 B9 = some (B12,
    .cond (SBool.cmp .eq .W32 nm1 (.lit 3)).not NativeRustcVmX64.Vm.Ladder.label_17) :=
  run_b12.trans (by rw [show B12 = _ from after_eq run_b12]; rfl)
public theorem exit_b17 : exec b17 B12 = some (B17,
    .cond (SBool.cmp .eq .W32 nm1 (.lit 4)) NativeRustcVmX64.Vm.Ladder.label_14) :=
  run_b17.trans (by rw [show B17 = _ from after_eq run_b17]; rfl)
public theorem exit_b18 : exec b18 B17 = some (B18, .jump NativeRustcVmX64.Vm.Ladder.label_15) :=
  run_b18.trans (by rw [show B18 = _ from after_eq run_b18])
public theorem exit_b13a : exec b13 B10 = some (C13a, .fall) :=
  run_b13a.trans (by rw [show C13a = _ from after_eq run_b13a])
public theorem exit_b13b : exec b13 B12 = some (C13b, .fall) :=
  run_b13b.trans (by rw [show C13b = _ from after_eq run_b13b])
public theorem exit_b14a : exec b14 C13a = some (C14a, .fall) :=
  run_b14a.trans (by rw [show C14a = _ from after_eq run_b14a])
public theorem exit_b14b : exec b14 C13b = some (C14b, .fall) :=
  run_b14b.trans (by rw [show C14b = _ from after_eq run_b14b])
public theorem exit_b14c : exec b14 B17 = some (C14c, .fall) :=
  run_b14c.trans (by rw [show C14c = _ from after_eq run_b14c])
public theorem exit_b15a : exec b15 C14a = some (C15a, .fall) :=
  run_b15a.trans (by rw [show C15a = _ from after_eq run_b15a])
public theorem exit_b15b : exec b15 C14b = some (C15b, .fall) :=
  run_b15b.trans (by rw [show C15b = _ from after_eq run_b15b])
public theorem exit_b15c : exec b15 C14c = some (C15c, .fall) :=
  run_b15c.trans (by rw [show C15c = _ from after_eq run_b15c])
public theorem exit_b15d : exec b15 B18 = some (C15d, .fall) :=
  run_b15d.trans (by rw [show C15d = _ from after_eq run_b15d])
public theorem exit_b16a : exec b16 C15a = some (after b16 C15a, .ret (.load 0 72 8)) :=
  run_b16a.trans (by rw [after_eq run_b16a])
public theorem exit_b16b : exec b16 C15b = some (after b16 C15b, .ret (.load 0 72 8)) :=
  run_b16b.trans (by rw [after_eq run_b16b])
public theorem exit_b16c : exec b16 C15c = some (after b16 C15c, .ret (.load 0 72 8)) :=
  run_b16c.trans (by rw [after_eq run_b16c])
public theorem exit_b16d : exec b16 C15d = some (after b16 C15d, .ret (.load 0 72 8)) :=
  run_b16d.trans (by rw [after_eq run_b16d])
public theorem end_a : EndOk (after b16 C15a) (.lit 0) (.lit 0) (.lit 0) := by decide +kernel
public theorem end_b : EndOk (after b16 C15b) (.load 2 24 8) (.lit 0) (.lit 0) := by
  decide +kernel
public theorem end_c : EndOk (after b16 C15c) (.load 2 24 8) (.load 2 32 8) (.lit 0) := by
  decide +kernel
public theorem end_d : EndOk (after b16 C15d) (.load 2 24 8) (.load 2 32 8) (.load 2 40 8) := by
  decide +kernel

end NativeRustcVmX64.Layout.Ladder
