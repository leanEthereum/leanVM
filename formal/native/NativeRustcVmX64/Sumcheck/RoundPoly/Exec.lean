module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names
public meta import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `sumcheck_round_poly`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 112-byte frame below the entry's RSP and the return address (`Frame`, `F = 112`:
RSP at offset `8` in the body, a callee's return address at `0`): the claim at `8`, `16`, the
equality factor's limb `0` and the sum's limb `1` at `32`, `24`, `read_scalar`'s `Option<EW>` at
`40`, the pushed registers from `64`. In the body, region 1 is the message (RBX, 80 bytes).

- `entryS`, at the entry in equality mode (`b0`, then `b1`): region 1 the `Option<EW>` `eq`
  (R8); `entryN`, the same in plain mode (`b0`, then `b9`), region 1 only `eq`'s tag (8 bytes);
- `bodyS`, after a call (`b2` to `b8`, `b10` to `b17`);
- `exitS`, at `.L8`/`.L9` (`b18`, `b19`).
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(104, .rbp), (96, .r15), (88, .r14), (80, .r13), (72, .r12), (64, .rbx)]

/-- At the entry in equality mode: the frame, `eq` (R8). -/
def entryS : SState := init [120, 24] [(.rsp, .ptr 0 112), (.r8, .ptr 1 0)]

/-- At the entry in plain mode: the frame, `eq`'s tag (R8). -/
def entryN : SState := init [120, 8] [(.rsp, .ptr 0 112), (.r8, .ptr 1 0)]

/-- After a call: the frame, the message (RBX). -/
def bodyS : SState := init [120, 80] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- At the exit: the frame. -/
def exitS : SState := init [120] [(.rsp, .ptr 0 8)]

/-- `b0`'s exit: `eq`'s tag `0` (plain mode). -/
def c0 : SBool := .cmp .eq .W8 (.load 1 0 1) (.lit 0)

/-- `test %al, %al`, zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- `b10`'s exit: `read_scalar`'s tag not `1`. -/
def c10 : SBool := .not (.cmp .eq .W32 (.load 0 40 4) (.lit 1))

/-- The grind's bits from `bit_length`'s result (RBP zero): `eax - 3`, saturating. -/
def bitsS : Sym :=
  .un .trunc .W32 (.ite (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.un .trunc .W32 (.reg .rbp))
    (.bin .sub .W32 (.reg .rax) (.lit 3)))

/-- The equality mode's entry at its call: `read_scalars(t, msg + 16, count - 1)`. -/
abbrev someS : SState := after b1 (after b0 entryS)

/-- The plain mode's entry at its call: `read_scalar(frame + 40, t)`. -/
abbrev noneS : SState := after b9 (after b0 entryN)

/-- What a body block keeps: RBX the message, R12 to R15 and RBP unless said. -/
def KeepsR (S : SState) (rs : List Reg64) : Bool :=
  S.reg .rbx == some (.ptr 1 0) && rs.all fun r ↦ S.reg r == some (.reg r)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b0n := exec b0 entryN
sym_block run_b9 := exec b9 (after b0 entryN)
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 (after b2 bodyS)
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 (after b6 bodyS)
sym_block run_b8 := exec b8 bodyS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 (after b10 bodyS)
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 (after b12 bodyS)
sym_block run_b14 := exec b14 bodyS
sym_block run_b15 := exec b15 bodyS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 (after b16 bodyS)
sym_block run_b18 := exec b18 exitS
sym_block run_b19 := exec b19 exitS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_4) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem exit_b1 : exec b1 (after b0 entryS) = some (someS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b1.trans (by rw [show someS = after b1 (after b0 entryS) from rfl, after_eq run_b1])
public theorem ok_some : ProOk 112 0 slots someS = true ∧
    someS.reg .rdi = some (.reg .rdi) ∧ someS.reg .rsi = some (.bin .add .W64 (.reg .r9) (.lit 16)) ∧
    someS.reg .rdx = some (.bin .sub .W64 (.reg .rsi) (.lit 1)) ∧
    someS.reg .rbx = some (.reg .r9) ∧ someS.reg .r12 = some (.reg .rdi) ∧
    someS.reg .r13 = some (.bin .sub .W64 (.reg .rsi) (.lit 1)) ∧
    someS.reg .r14 = some (.bin .add .W64 (.reg .r9) (.lit 16)) ∧
    someS.reg .r15 = some (.load 1 16 8) ∧
    WordW 0 8 (.reg .rdx) someS ∧ WordW 0 16 (.reg .rcx) someS ∧
    WordW 0 32 (.load 1 8 8) someS ∧ (∀ w ∈ someS.mem, w.r = 0) := by
  decide +kernel

public theorem exit_b0n : exec b0 entryN = some (after b0 entryN, .cond c0 NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_4) :=
  run_b0n.trans (by rw [after_eq run_b0n]; rfl)
public theorem exit_b9 : exec b9 (after b0 entryN) = some (noneS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b9.trans (by rw [show noneS = after b9 (after b0 entryN) from rfl, after_eq run_b9])
public theorem ok_none : ProOk 112 0 slots noneS = true ∧
    noneS.reg .rdi = some (.ptr 0 40) ∧ noneS.reg .rsi = some (.reg .rdi) ∧
    noneS.reg .rbx = some (.reg .r9) ∧ noneS.reg .r12 = some (.reg .rdi) ∧
    noneS.reg .r13 = some (.reg .rsi) ∧ noneS.reg .r14 = some (.reg .rcx) ∧
    noneS.reg .r15 = some (.reg .rdx) ∧ (∀ w ∈ noneS.mem, w.r = 0 ∧ w.off + w.n ≤ 8 ∨
      w.r = 0 ∧ 64 ≤ w.off) := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS, .cond cAl NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 112 8 slots (after b2 bodyS) = true ∧ (after b2 bodyS).mem = [] ∧
    (after b2 bodyS).reg .rbp = some (.lit 0) ∧
    KeepsR (after b2 bodyS) [.r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b3 : exec b3 (after b2 bodyS) = some (after b3 (after b2 bodyS),
    .call NativeRustcVmX64.Vm.SumE.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 112 0 slots (after b3 (after b2 bodyS)) = true ∧
    (∀ w ∈ (after b3 (after b2 bodyS)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 (after b2 bodyS)).reg .rbp = some (.lit 0) ∧
    (after b3 (after b2 bodyS)).reg .rdi = some (.reg .r14) ∧
    (after b3 (after b2 bodyS)).reg .rsi = some (.reg .r13) ∧
    KeepsR (after b3 (after b2 bodyS)) [.r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b4 : exec b4 bodyS = some (after b4 bodyS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 112 0 slots (after b4 bodyS) = true ∧
    (∀ w ∈ (after b4 bodyS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ w.off = 24 ∧ w.n = 8)) ∧
    WordW 0 24 (.reg .rdx) (after b4 bodyS) ∧
    (after b4 bodyS).reg .rdi = some (.reg .r13) ∧ (after b4 bodyS).reg .r14 = some (.reg .rax) ∧
    KeepsR (after b4 bodyS) [.rbp, .r12, .r13, .r15] = true := by
  decide +kernel
public theorem exit_b5 : exec b5 bodyS = some (after b5 bodyS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 112 0 slots (after b5 bodyS) = true ∧
    (∀ w ∈ (after b5 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b5 bodyS).reg .rdi = some (.reg .r12) ∧ (after b5 bodyS).reg .rsi = some bitsS ∧
    KeepsR (after b5 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b6 : exec b6 bodyS = some (after b6 bodyS, .cond cAl NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : MidOk 112 8 slots (after b6 bodyS) = true ∧ (after b6 bodyS).mem = [] ∧
    KeepsR (after b6 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b7 : exec b7 (after b6 bodyS) = some (after b7 (after b6 bodyS),
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk 112 0 slots (after b7 (after b6 bodyS)) = true ∧
    (∀ w ∈ (after b7 (after b6 bodyS)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b7 (after b6 bodyS)).reg .rdi = some (.load 0 32 8) ∧
    (after b7 (after b6 bodyS)).reg .rsi = some (.reg .r15) ∧
    (after b7 (after b6 bodyS)).reg .rdx = some (.reg .r14) ∧
    (after b7 (after b6 bodyS)).reg .rcx = some (.load 0 24 8) ∧
    KeepsR (after b7 (after b6 bodyS)) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b8 : exec b8 bodyS = some (after b8 bodyS, .jump NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 112 8 slots (after b8 bodyS) = true ∧
    (∀ w ∈ (after b8 bodyS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    WordW 1 0 (.bin .xor .W64 (.reg .rax) (.load 0 8 8)) (after b8 bodyS) ∧
    WordW 1 8 (.bin .xor .W64 (.reg .rdx) (.load 0 16 8)) (after b8 bodyS) ∧
    (after b8 bodyS).reg .rbp = some (.bin .merge .W8 (.reg .rbp) (.lit 1)) ∧
    (after b8 bodyS).reg .rbx = some (.ptr 1 0) := by
  decide +kernel

public theorem exit_b10 : exec b10 bodyS = some (after b10 bodyS, .cond c10 NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_8) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : MidOk 112 8 slots (after b10 bodyS) = true ∧ (after b10 bodyS).mem = [] ∧
    KeepsR (after b10 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b11 : exec b11 (after b10 bodyS) = some (after b11 (after b10 bodyS),
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 112 0 slots (after b11 (after b10 bodyS)) = true ∧
    (∀ w ∈ (after b11 (after b10 bodyS)).mem,
      (w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ w.off = 16 ∧ w.n = 8)) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    WordW 1 0 (.load 0 48 8) (after b11 (after b10 bodyS)) ∧
    WordW 1 8 (.load 0 56 8) (after b11 (after b10 bodyS)) ∧
    WordW 0 16 (.reg .r14) (after b11 (after b10 bodyS)) ∧
    (after b11 (after b10 bodyS)).reg .rdi = some (.reg .r12) ∧
    (after b11 (after b10 bodyS)).reg .rsi = some (.ptr 1 32) ∧
    (after b11 (after b10 bodyS)).reg .rdx =
      some (.bin .add .W64 (.lit 18446744073709551614) (.reg .r13)) ∧
    (after b11 (after b10 bodyS)).reg .r13 =
      some (.bin .add .W64 (.lit 18446744073709551614) (.reg .r13)) ∧
    (after b11 (after b10 bodyS)).reg .r14 = some (.ptr 1 32) ∧
    KeepsR (after b11 (after b10 bodyS)) [.rbp, .r12, .r15] = true := by
  decide +kernel
public theorem exit_b12 : exec b12 bodyS = some (after b12 bodyS, .cond cAl NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b12.trans (by rw [after_eq run_b12]; rfl)
public theorem ok_b12 : MidOk 112 8 slots (after b12 bodyS) = true ∧ (after b12 bodyS).mem = [] ∧
    (after b12 bodyS).reg .rbp = some (.lit 0) ∧
    KeepsR (after b12 bodyS) [.r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b13 : exec b13 (after b12 bodyS) = some (after b13 (after b12 bodyS),
    .call NativeRustcVmX64.Vm.SumE.entryLabel) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 112 0 slots (after b13 (after b12 bodyS)) = true ∧
    (∀ w ∈ (after b13 (after b12 bodyS)).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ w.off = 8 ∧ w.n = 8)) ∧
    WordW 0 8 (.reg .r15) (after b13 (after b12 bodyS)) ∧
    (after b13 (after b12 bodyS)).reg .rbp = some (.lit 0) ∧
    (after b13 (after b12 bodyS)).reg .rdi = some (.reg .r14) ∧
    (after b13 (after b12 bodyS)).reg .rsi = some (.reg .r13) ∧
    KeepsR (after b13 (after b12 bodyS)) [.r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b14 : exec b14 bodyS = some (after b14 bodyS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 112 0 slots (after b14 bodyS) = true ∧
    (∀ w ∈ (after b14 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b14 bodyS).reg .rdi = some (.reg .r13) ∧ (after b14 bodyS).reg .r14 = some (.reg .rdx) ∧
    (after b14 bodyS).reg .r15 = some (.reg .rax) ∧
    KeepsR (after b14 bodyS) [.rbp, .r12, .r13] = true := by
  decide +kernel
public theorem exit_b15 : exec b15 bodyS = some (after b15 bodyS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 112 0 slots (after b15 bodyS) = true ∧
    (∀ w ∈ (after b15 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b15 bodyS).reg .rdi = some (.reg .r12) ∧ (after b15 bodyS).reg .rsi = some bitsS ∧
    KeepsR (after b15 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b16 : exec b16 bodyS = some (after b16 bodyS, .cond cAl NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b16.trans (by rw [after_eq run_b16]; rfl)
public theorem ok_b16 : MidOk 112 8 slots (after b16 bodyS) = true ∧ (after b16 bodyS).mem = [] ∧
    KeepsR (after b16 bodyS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b17 : exec b17 (after b16 bodyS) = some (after b17 (after b16 bodyS),
    .jump NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.label_9) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 112 8 slots (after b17 (after b16 bodyS)) = true ∧
    (∀ w ∈ (after b17 (after b16 bodyS)).mem, w.r = 1 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    WordW 1 16 (.bin .xor .W64 (.reg .r15) (.load 0 8 8)) (after b17 (after b16 bodyS)) ∧
    WordW 1 24 (.bin .xor .W64 (.reg .r14) (.load 0 16 8)) (after b17 (after b16 bodyS)) ∧
    (after b17 (after b16 bodyS)).reg .rbp = some (.bin .merge .W8 (.reg .rbp) (.lit 1)) ∧
    (after b17 (after b16 bodyS)).reg .rbx = some (.ptr 1 0) := by
  decide +kernel

public theorem exit_b18 : exec b18 exitS = some (after b18 exitS, .fall) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 112 8 slots (after b18 exitS) = true ∧ (after b18 exitS).mem = [] ∧
    (after b18 exitS).reg .rbp = some (.lit 0) ∧ (after b18 exitS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem exit_b19 : exec b19 exitS = some (after b19 exitS, .ret (.load 0 112 8)) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : EpiOk 112 slots (after b19 exitS) = true ∧ (after b19 exitS).mem = [] ∧
    (after b19 exitS).reg .rax = some (.un .trunc .W32 (.reg .rbp)) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.RoundPoly
