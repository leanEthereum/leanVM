module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SampleQueries
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.SampleQueries
public meta import NativeRustcVmX64.Whir.Common
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `sample_queries`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 128-byte frame (RBP, R15, R14, R13, R12, RBX pushed at offsets `120` to `80`, the
locals at `16` to `72`, a callee's return address at `0`) and the return address at `128`.
- `entryS` at the entry, region 1 the buffer's count word at RCX: the prologue `b0` (an empty
  count returns, `b19`), `b1` (a depth above `128` goes to `b4`), `b2` (the outer loop's start);
- `midS` (RSP at offset `8`), the frame only: every other block but `b12` and `b16`;
- `perS` (`b12`): region 1 `PER_CHALLENGE` at R12, R13 (the depth) below `129`;
- `pushS` (`b16`): region 1 the buffer's next word (the frame's word `72` plus `8` RBP), region 2
  its count word.
Each block's facts (`ok_b*`) are checked on its literal end state.
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Slots ProOk MidOk EpiOk writesIn)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(120, .rbp), (112, .r15), (104, .r14), (96, .r13), (88, .r12), (80, .rbx)]

/-- `PER_CHALLENGE`'s label. -/
def perL : Label := NativeRustcVmX64.Vm.Symbols.rodata10Label

/-- At the entry: the frame, the buffer's count word at RCX. -/
def entryS : SState := init [136, 8] [(.rsp, .ptr 0 128), (.rcx, .ptr 1 0)]
/-- After the prologue. -/
def S0 : SState := after b0 entryS
/-- After `b1`'s test. -/
def S1 : SState := after b1 S0
/-- RSP at offset `8`: the frame only. -/
def midS : SState := init [136] [(.rsp, .ptr 0 8)]
/-- `b12`: `PER_CHALLENGE` at R12, the depth R13 below `129`. -/
def perS : SState := init [136, 129] [(.rsp, .ptr 0 8), (.r12, .ptr 1 0)] [] [(.reg .r13, 129)]
/-- The pushed word's address in `b16`. -/
def pushA : Sym := .bin .add .W64 (.load 0 72 8) (.bin .mul .W64 (.reg .rbp) (.lit 8))
/-- `b16`: the pushed word, the count word. -/
def pushS : SState :=
  init [136, 8, 8] [(.rsp, .ptr 0 8)] (aliases := [(pushA, 1, 0), (.load 0 72 8, 2, 0)])

/-- Every write in region `0` below `L`. -/
def wr0 (S : SState) (L : Nat) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ L)
/-- No write over the frame's word at `o`. -/
def miss (S : SState) (o : Nat) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + 8 ≤ w.off)
/-- The 8 bytes at `o` of region `r` written with `v`. -/
def wrote (S : SState) (r o : Nat) (v : Sym) : Bool :=
  (List.range 8).all fun t ↦ findWrite r (o + t) S.mem == some (v, t)
/-- Registers kept. -/
def kept (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- `min(RBP, 230)`, 32 bits. -/
def m23S : Sym := .un .trunc .W32 (.ite (.cmp .ult .W64 (.reg .rbp) (.lit 230)) (.reg .rbp) (.lit 230))
/-- `8 min(RBP, 230) - 1840`, the frame's word `48`. -/
def f48S : Sym := .bin .add .W64 (.bin .mul .W64 m23S (.lit 8)) (.lit 18446744073709549776)
/-- `8 max(RCX, 1)`, the frame's word `40`. -/
def f40S : Sym := .bin .shl .W64 (.bin .add .W64 (.reg .rcx)
  (.ite (.cmp .ult .W64 (.reg .rcx) (.lit 1)) (.lit 1) (.lit 0))) (.lit 3)
/-- `min(RAX, PER_CHALLENGE[depth])`, `b12`'s RCX. -/
def nS : Sym :=
  .ite (.cmp .ult .W64 (.load 0 16 8) (.un (.zext .W8) .W32 (.loadx 1 0 (.reg .r13) 1)))
    (.load 0 16 8) (.un (.zext .W8) .W32 (.loadx 1 0 (.reg .r13) 1))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b19z := exec b19 S0
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 S1
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b19 := exec b19 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 perS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 midS
sym_block run_b16 := exec b16 pushS
sym_block run_b17 := exec b17 midS

/-! ## The entry's chains -/

public theorem ok_b0z : EpiOk 128 [] (after b19 S0) = true ∧ writesIn (after b19 S0) = true ∧
    wrote (after b19 S0) 1 0 (.lit 0) = true ∧
    (after b19 S0).mem.all (fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 128)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 8))) = true ∧
    (after b19 S0).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) := by decide +kernel

public theorem ok_b1 : ProOk 128 8 slots S1 = true ∧ wrote S1 0 72 (.ptr 1 0) = true ∧
    wrote S1 1 0 (.lit 0) = true ∧
    S1.mem.all (fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 128)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 8))) = true ∧
    S1.reg .rbx = some (.reg .rdi) ∧ S1.reg .r14 = some (.reg .rdx) ∧
    S1.reg .r13 = some (.reg .rsi) := by decide +kernel

public theorem ok_b2 : ProOk 128 8 slots (after b2 S1) = true ∧
    wrote (after b2 S1) 0 72 (.ptr 1 0) = true ∧ wrote (after b2 S1) 0 24 (.reg .rdi) = true ∧
    wrote (after b2 S1) 1 0 (.lit 0) = true ∧
    (after b2 S1).mem.all (fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 128)) ||
      (w.r == 1 && decide (w.off + w.n ≤ 8))) = true ∧
    (after b2 S1).reg .rbx = some (.reg .rdi) ∧ (after b2 S1).reg .r14 = some (.reg .rdx) ∧
    (after b2 S1).reg .r13 = some (.reg .rsi) ∧ (after b2 S1).reg .r15 = some (.lit 0) ∧
    (after b2 S1).reg .r12 = some (.label perL) ∧ (after b2 S1).reg .rax = some (.reg .rdx) ∧
    (after b2 S1).reg .rbp = some (.lit 0) := by decide +kernel

/-! ## The squeezes' loop -/

public theorem ok_b4 : MidOk 128 0 slots (after b4 midS) = true ∧ wr0 (after b4 midS) 8 = true ∧
    (after b4 midS).reg .rdi = some (.reg .rbx) ∧
    kept (after b4 midS) [.rbx, .r13, .r14] = true := by decide +kernel

public theorem ok_b5 : MidOk 128 8 slots (after b5 midS) = true ∧ (after b5 midS).mem = [] ∧
    (after b5 midS).reg .r14 = some (.bin .sub .W64 (.reg .r14) (.lit 1)) ∧
    kept (after b5 midS) [.rbx, .r13] = true := by decide +kernel

/-! ## The returns -/

public theorem ok_b6 : MidOk 128 8 slots (after b6 midS) = true ∧ (after b6 midS).mem = [] ∧
    (after b6 midS).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) ∧
    kept (after b6 midS) [.r13] = true := by decide +kernel

public theorem ok_b19 : EpiOk 128 slots (after b19 midS) = true ∧ (after b19 midS).mem = [] ∧
    kept (after b19 midS) [.rax] = true := by decide +kernel

/-! ## The outer loop -/

public theorem ok_b8 : MidOk 128 8 slots (after b8 midS) = true ∧ (after b8 midS).mem = [] ∧
    (after b8 midS).reg .rbp = some (.bin .sub .W64 (.reg .rbp) (.lit 1)) ∧
    (after b8 midS).reg .rbx = some (.load 0 24 8) ∧ (after b8 midS).reg .r15 = some (.load 0 32 8) ∧
    (after b8 midS).reg .r12 = some (.label perL) ∧ (after b8 midS).reg .rax = some (.load 0 16 8) ∧
    kept (after b8 midS) [.rcx, .r13, .r14] = true := by decide +kernel

public theorem ok_b9 : MidOk 128 8 slots (after b9 midS) = true ∧ (after b9 midS).mem = [] ∧
    (after b9 midS).reg .r15 = some (.bin .add .W64 (.reg .r15) (.lit 1)) ∧
    (after b9 midS).reg .rax = some (.bin .sub .W64 (.reg .rax) (.reg .rcx)) ∧
    kept (after b9 midS) [.rbx, .r12, .r13, .r14, .rbp] = true := by decide +kernel

public theorem ok_b10 : MidOk 128 8 slots (after b10 midS) = true ∧ (after b10 midS).mem = [] ∧
    kept (after b10 midS) [.rax, .rbx, .r12, .r13, .r14, .r15, .rbp] = true := by decide +kernel

public theorem ok_b11 : MidOk 128 0 slots (after b11 midS) = true ∧ wr0 (after b11 midS) 24 = true ∧
    wrote (after b11 midS) 0 16 (.reg .rax) = true ∧ (after b11 midS).reg .rdi = some (.reg .rbx) ∧
    kept (after b11 midS) [.rbx, .r12, .r13, .r14, .r15, .rbp] = true := by decide +kernel

public theorem ok_b12 : MidOk 128 8 slots (after b12 perS) = true ∧ wr0 (after b12 perS) 72 = true ∧
    miss (after b12 perS) 16 = true ∧ miss (after b12 perS) 24 = true ∧
    wrote (after b12 perS) 0 64 (.reg .rax) = true ∧ wrote (after b12 perS) 0 56 (.reg .rdx) = true ∧
    (after b12 perS).reg .rax = some (.load 0 16 8) ∧ (after b12 perS).reg .rcx = some nS ∧
    (after b12 perS).reg .r12 = some (.ptr 1 0) ∧
    kept (after b12 perS) [.rbx, .r13, .r14, .r15, .rbp] = true := by decide +kernel

/-! ## The inner loop -/

public theorem ok_b13 : MidOk 128 8 slots (after b13 midS) = true ∧ wr0 (after b13 midS) 56 = true ∧
    miss (after b13 midS) 16 = true ∧ miss (after b13 midS) 24 = true ∧
    wrote (after b13 midS) 0 32 (.reg .r15) = true ∧ wrote (after b13 midS) 0 40 f40S = true ∧
    wrote (after b13 midS) 0 48 f48S = true ∧
    (after b13 midS).reg .rbp = some (.bin .add .W64 (.reg .rbp) (.lit 1)) ∧
    (after b13 midS).reg .r15 = some (.lit 0) ∧ (after b13 midS).reg .r12 = some (.lit 0) ∧
    kept (after b13 midS) [.rcx, .r13, .r14] = true := by decide +kernel

public theorem ok_b14 : MidOk 128 8 slots (after b14 midS) = true ∧ (after b14 midS).mem = [] ∧
    kept (after b14 midS) [.rcx, .r12, .r13, .r14, .r15, .rbp] = true := by decide +kernel

public theorem ok_b15 : MidOk 128 0 slots (after b15 midS) = true ∧ wr0 (after b15 midS) 8 = true ∧
    (after b15 midS).reg .rdi = some (.load 0 64 8) ∧ (after b15 midS).reg .rsi = some (.load 0 56 8) ∧
    (after b15 midS).reg .rdx = some (.reg .r15) ∧ (after b15 midS).reg .rbx = some (.reg .rcx) ∧
    (after b15 midS).reg .rcx = some (.reg .r13) ∧
    kept (after b15 midS) [.r12, .r13, .r14, .r15, .rbp] = true := by decide +kernel

public theorem ok_b16 : MidOk 128 8 slots (after b16 pushS) = true ∧
    wrote (after b16 pushS) 1 0 (.reg .rax) = true ∧ wrote (after b16 pushS) 2 0 (.reg .rbp) = true ∧
    (after b16 pushS).mem.all (fun w ↦ (w.r == 1 || w.r == 2) && decide (w.off + w.n ≤ 8)) = true ∧
    (after b16 pushS).reg .rcx = some (.reg .rbx) ∧
    (after b16 pushS).reg .r12 = some (.bin .add .W64 (.lit 18446744073709551608) (.reg .r12)) ∧
    (after b16 pushS).reg .r15 = some (.bin .add .W64 (.reg .r13) (.reg .r15)) ∧
    (after b16 pushS).reg .rbp = some (.bin .add .W64 (.reg .rbp) (.lit 1)) ∧
    kept (after b16 pushS) [.rbx, .r13, .r14] = true := by decide +kernel

public theorem ok_b17 : MidOk 128 8 slots (after b17 midS) = true ∧ (after b17 midS).mem = [] ∧
    kept (after b17 midS) [.rax, .rbx, .rcx, .r12, .r13, .r14, .r15, .rbp] = true := by
  decide +kernel

end NativeRustcVmX64.Whir.SampleQueries
