module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.NextLevel
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmX64.Code.Vm.GlueLevel.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.NextLevel.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public meta import NativeRustcVmX64.Code.Vm.NextLevel
public meta import NativeRustcVmX64.Transcript.Frame
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `next_level`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 8176 bytes below the entry's RSP, the return address and the stack argument `w`
(8192 bytes, `argEnv`). RSP is at offset `72` in the body (a callee's return address at `64`; at
`each_row`'s call, after two pushed argument words, at `56`; at `glue_level`'s, after eight, at
`8`); the six pushed registers at `8128` to `8176`, the return address at `8176`, `w` at `8184`.
The body's word `N(%rsp)` is region 0's offset `72 + N`.

- `entryS` at the entry (`b0`), region 1 the level (RDX);
- `retS` in the body (RSP at `72`), `levelS` with the level (region 1) at RBP, `qS` with the query
  buffer's count (region 1) at RBP;
- `zeroS` the zeroing loop's 80 bytes at `RSP + RCX + 616`;
- `rowsS` with the state `w` (region 1, its address the word at `8184`);
- `s56S` after `each_row` (RSP at `56`), `s8S` after `glue_level` (RSP at `8`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NextLevel NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(8168, .rbp), (8160, .r15), (8152, .r14), (8144, .r13), (8136, .r12), (8128, .rbx)]

/-- At the entry: the frame and the argument word, RSP at offset `8176`; the level at RDX. -/
def entryS : SState := init [8184, 24] [(.rsp, .ptr 0 8176), (.rdx, .ptr 1 0)]

/-- In the body: RSP at offset `72`. -/
def retS : SState := init [8192] [(.rsp, .ptr 0 72)]

/-- The copy reads its function pointer from a read-only loader slot. -/
def copyS : SState :=
  (init [8192, 8] [(.rsp, .ptr 0 72)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")

/-- In the body with the level (region 1) at RBP. -/
def levelS : SState := init [8184, 24] [(.rsp, .ptr 0 72), (.rbp, .ptr 1 0)]

/-- In the body with the query buffer's count (region 1) at RBP. -/
def qS : SState := init [8192, 8] [(.rsp, .ptr 0 72), (.rbp, .ptr 1 0)]

/-- The zeroing loop's body: the 80 bytes (region 0) at `RSP + RCX + 616`. -/
def zeroS : SState :=
  init [80] (aliases := [(.bin .add .W64 (.reg .rsp) (.reg .rcx), (0, -616))])

/-- In the body with the state `w` (region 1), its address the word at `8184`. -/
def rowsS : SState :=
  init [8192, 63200] [(.rsp, .ptr 0 72)] (aliases := [(.load 0 8184 8, (1, 0))])

/-- After `each_row`: RSP at offset `56`. -/
def s56S : SState := init [8192] [(.rsp, .ptr 0 56)]

/-- After `glue_level`: RSP at offset `8`. -/
def s8S : SState := init [8192] [(.rsp, .ptr 0 8)]

/-- Every write in region 0 within one of the ranges `rs`. -/
def Wr (rs : List (Nat × Nat)) (S : SState) : Prop :=
  ∀ w ∈ S.mem, w.r = 0 ∧ ∃ p ∈ rs, p.1 ≤ w.off ∧ w.off + w.n ≤ p.2

instance (rs : List (Nat × Nat)) (S : SState) : Decidable (Wr rs S) := by
  unfold Wr; infer_instance

/-- The registers `rs` kept. -/
def KR (rs : List Reg64) (S : SState) : Prop := ∀ r ∈ rs, S.reg r = some (.reg r)

instance (rs : List Reg64) (S : SState) : Decidable (KR rs S) := by unfold KR; infer_instance

/-- The six callee-saved registers. -/
def six : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `test %al, %al` zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)
/-- `b2`'s exit: a fold above `6`. -/
def cFold : SBool :=
  .and (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 6))) (.not (.cmp .eq .W64 (.load 1 0 8) (.lit 6)))
/-- `b7`'s exit: `μ` above `30`. -/
def cMu : SBool :=
  .and (.not (.cmp .ult .W64 (.load 0 80 8) (.lit 30))) (.not (.cmp .eq .W64 (.load 0 80 8) (.lit 30)))
/-- `b10`'s exit: `read_scalar`'s `None`. -/
def cTag : SBool := .not (.cmp .eq .W32 (.load 0 4440 4) (.lit 1))
/-- `b17`'s exit: more to zero. -/
def cZero : SBool :=
  .not (.cmp .eq .W64 (.bin .add .W64 (.lit 80) (.reg .rcx)) (.lit 3752))
/-- `b21`'s exit: `query_openings`' `None`. -/
def cRows : SBool := .cmp .eq .W64 (.load 0 760 8) (.lit 0)

/-- `b0`'s `height`. -/
def vHeight : Sym := .bin .add .W64 (.reg .r8)
  (.ite (.not (.cmp .ult .W64 (.reg .r9) (.reg .rcx))) (.bin .sub .W64 (.reg .r9) (.reg .rcx))
    (.lit 0))
/-- `b18`'s query count, saturated. -/
def vN : Sym := .ite (.cmp .ult .W64 (.reg .rax) (.lit 231)) (.reg .rax) (.lit 0)
/-- `b18`'s query pointer. -/
def vQ : Sym := .ite (.not (.cmp .ult .W64 (.reg .rax) (.lit 231))) (.lit 8)
  (.bin .add .W64 (.load 0 8184 8) (.lit 61360))
/-- `b22`'s rounds count. -/
def vRc : Sym := .ite (.cmp .ult .W64 (.load 1 61152 8) (.lit 7)) (.load 1 61152 8) (.lit 0)
/-- `b22`'s rounds pointer. -/
def vRp : Sym := .ite (.not (.cmp .ult .W64 (.load 1 61152 8) (.lit 7))) (.lit 8)
  (.bin .add .W64 (.load 0 8184 8) (.lit 61160))
/-- `b22`'s weights pointer. -/
def vWp : Sym := .ite (.not (.cmp .ult .W64 (.load 0 4440 8) (.lit 231))) (.lit 8) (.ptr 0 4448)
/-- `b22`'s weights count. -/
def vWn : Sym := .ite (.not (.cmp .ult .W64 (.load 0 4440 8) (.lit 231))) (.lit 0) (.load 0 4440 8)
/-- `b24`'s out-of-domain point. -/
def vOp : Sym := .ite (.cmp .ult .W64 (.load 0 272 8) (.lit 31)) (.ptr 0 280) (.lit 8)
/-- `b24`'s out-of-domain point's length. -/
def vOn : Sym := .ite (.cmp .ult .W64 (.load 0 272 8) (.lit 31)) (.load 0 272 8) (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS
sym_block run_b2 := exec b2 levelS
sym_block run_b3 := exec b3 retS
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 retS
sym_block run_b7 := exec b7 retS
sym_block run_b8 := exec b8 retS
sym_block run_b9 := exec b9 retS
sym_block run_b10 := exec b10 retS
sym_block run_b11 := exec b11 retS
sym_block run_b13a := exec (b13.take 1) retS
sym_block run_b13b := exec (b13.drop 1) levelS
sym_block run_b15 := exec b15 retS
sym_block run_b16 := exec b16 qS
sym_block run_b17 := exec b17 zeroS
sym_block run_b18 := exec b18 copyS
sym_block run_b19 := exec b19 retS
sym_block run_b20 := exec b20 retS
sym_block run_b21 := exec b21 retS
sym_block run_b22 := exec b22 rowsS
sym_block run_b23 := exec b23 s56S
sym_block run_b24 := exec b24 retS
sym_block run_b25 := exec b25 s8S
sym_block run_b26 := exec b26 retS
sym_block run_b27 := exec b27 retS

end NativeRustcVmX64.Whir.Levels.NL

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NextLevel NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

public theorem b_eq : b6 = b4 ∧ b12 = b4 ∧ b14 = b4 := by decide +kernel

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 8176 64 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 8176) ∧ WordW 0 80 (.reg .r9) (after b0 entryS) ∧
    (after b0 entryS).reg .rbx = some (.reg .rsi) ∧ (after b0 entryS).reg .rbp = some (.ptr 1 0) ∧
    (after b0 entryS).reg .r13 = some (.bin .add .W64 (.reg .r9) (.load 1 8 8)) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdi) ∧ (after b0 entryS).reg .r15 = some (.lit 0) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) ∧ (after b0 entryS).reg .rsi = some vHeight ∧
    (after b0 entryS).reg .rdx = some (.bin .shl .W64 (.lit 2) (.reg .rcx)) := by decide +kernel

public theorem exit_b1 : exec b1 retS = some (after b1 retS, .cond cAl NativeRustcVmX64.Vm.NextLevel.label_14) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : (after b1 retS).mem = [] ∧ (after b1 retS).regs = retS.regs := by
  decide +kernel
public theorem exit_b4 : exec b4 retS = some (after b4 retS, .cond cAl NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : (after b4 retS).mem = [] ∧ (after b4 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b2 : exec b2 levelS = some (after b2 levelS, .cond cFold NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 8176 72 slots (after b2 levelS) = true ∧ Wr [(176, 272)] (after b2 levelS) ∧
    (after b2 levelS).reg .r15 = some (.load 1 0 8) ∧ (after b2 levelS).reg .rbp = some (.ptr 1 0) ∧
    KR [.rbx, .r12, .r13, .r14] (after b2 levelS) := by decide +kernel

public theorem exit_b3 : exec b3 retS = some (after b3 retS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 8176 64 slots (after b3 retS) = true ∧ Wr [(64, 72)] (after b3 retS) ∧
    (after b3 retS).reg .rsi = some (.ptr 0 176) ∧ (after b3 retS).reg .rdi = some (.reg .r14) ∧
    (after b3 retS).reg .rdx = some (.reg .r15) ∧ KR six (after b3 retS) := by decide +kernel

public theorem exit_b5 : exec b5 retS = some (after b5 retS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 8176 64 slots (after b5 retS) = true ∧ Wr [(64, 72)] (after b5 retS) ∧
    (after b5 retS).reg .rdi = some (.reg .r14) ∧ (after b5 retS).reg .rsi = some (.lit 15) ∧
    KR six (after b5 retS) := by decide +kernel

public theorem exit_b7 : exec b7 retS = some (after b7 retS, .cond cMu NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem ok_b7 : MidOk 8176 72 slots (after b7 retS) = true ∧ Wr [(272, 760)] (after b7 retS) ∧
    (after b7 retS).reg .r12 = some (.load 0 80 8) ∧ KR [.rbx, .rbp, .r13, .r14, .r15] (after b7 retS) := by
  decide +kernel

public theorem exit_b8 : exec b8 retS = some (after b8 retS,
    .call NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 8176 64 slots (after b8 retS) = true ∧
    Wr [(64, 72), (272, 280)] (after b8 retS) ∧ WordW 0 272 (.reg .r12) (after b8 retS) ∧
    (after b8 retS).reg .rsi = some (.ptr 0 280) ∧ (after b8 retS).reg .rdi = some (.reg .r14) ∧
    (after b8 retS).reg .rdx = some (.reg .r12) ∧ KR six (after b8 retS) := by decide +kernel

public theorem exit_b9 : exec b9 retS = some (after b9 retS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 8176 64 slots (after b9 retS) = true ∧ Wr [(64, 72)] (after b9 retS) ∧
    (after b9 retS).reg .rdi = some (.ptr 0 4440) ∧ (after b9 retS).reg .rsi = some (.reg .r14) ∧
    KR six (after b9 retS) := by decide +kernel

public theorem exit_b10 : exec b10 retS = some (after b10 retS, .cond cTag NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : (after b10 retS).mem = [] ∧ (after b10 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b11 : exec b11 retS = some (after b11 retS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 8176 64 slots (after b11 retS) = true ∧
    Wr [(64, 72), (128, 144)] (after b11 retS) ∧ WordW 0 128 (.load 0 4456 8) (after b11 retS) ∧
    WordW 0 136 (.load 0 4448 8) (after b11 retS) ∧ (after b11 retS).reg .rdi = some (.reg .r14) ∧
    (after b11 retS).reg .rsi = some (.lit 17) ∧ KR six (after b11 retS) := by decide +kernel

public theorem exit_b13a : exec (b13.take 1) retS = some (after (b13.take 1) retS, .fall) :=
  run_b13a.trans (by rw [after_eq run_b13a])
public theorem ok_b13a : (after (b13.take 1) retS).mem = [] ∧
    (after (b13.take 1) retS).reg .rax = some (.load 0 8184 8) ∧
    MidOk 8176 72 slots (after (b13.take 1) retS) = true ∧
    KR [.rbx, .rbp, .r12, .r13, .r14, .r15] (after (b13.take 1) retS) := by decide +kernel
public theorem exit_b13b : exec (b13.drop 1) levelS = some (after (b13.drop 1) levelS,
    .call NativeRustcVmX64.Vm.SampleQueries.entryLabel) :=
  run_b13b.trans (by rw [after_eq run_b13b])
public theorem ok_b13b : MidOk 8176 64 slots (after (b13.drop 1) levelS) = true ∧
    Wr [(64, 72)] (after (b13.drop 1) levelS) ∧
    (after (b13.drop 1) levelS).reg .rdi = some (.reg .r14) ∧
    (after (b13.drop 1) levelS).reg .rsi = some (.reg .r13) ∧
    (after (b13.drop 1) levelS).reg .rdx = some (.load 1 16 8) ∧
    (after (b13.drop 1) levelS).reg .rcx = some (.bin .add .W64 (.reg .rax) (.lit 61352)) ∧
    (after (b13.drop 1) levelS).reg .rbp = some (.bin .add .W64 (.reg .rax) (.lit 61352)) ∧
    KR [.rbx, .r12, .r13, .r14, .r15] (after (b13.drop 1) levelS) := by decide +kernel

public theorem exit_b15 : exec b15 retS = some (after b15 retS,
    .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 8176 64 slots (after b15 retS) = true ∧ Wr [(64, 72)] (after b15 retS) ∧
    (after b15 retS).reg .rdi = some (.reg .r14) ∧ KR six (after b15 retS) := by decide +kernel

public theorem exit_b16 : exec b16 qS = some (after b16 qS, .fall) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : MidOk 8176 72 slots (after b16 qS) = true ∧ Wr [(88, 104)] (after b16 qS) ∧
    WordW 0 88 (.reg .rdx) (after b16 qS) ∧ WordW 0 96 (.reg .rax) (after b16 qS) ∧
    (after b16 qS).reg .rax = some (.load 1 0 8) ∧ (after b16 qS).reg .rcx = some (.lit 72) ∧
    (after b16 qS).reg .rbp = some (.ptr 1 0) ∧ KR [.rbx, .r12, .r13, .r14, .r15] (after b16 qS) := by
  decide +kernel

public theorem exit_b17 : exec b17 zeroS = some (after b17 zeroS, .cond cZero NativeRustcVmX64.Vm.NextLevel.label_9) :=
  run_b17.trans (by rw [after_eq run_b17]; rfl)
public theorem ok_b17 : (∀ w ∈ (after b17 zeroS).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (after b17 zeroS).reg .rcx = some (.bin .add .W64 (.lit 80) (.reg .rcx)) ∧
    KR (allRegs.filter (· != .rcx)) (after b17 zeroS) := by decide +kernel

public theorem exit_b18 : exec b18 copyS = some (after b18 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 8176 64 slots (after b18 copyS) = true ∧ Wr [(64, 72)] (after b18 copyS) ∧
    (after b18 copyS).reg .rdi = some (.ptr 0 4448) ∧ (after b18 copyS).reg .rsi = some (.ptr 0 760) ∧
    (after b18 copyS).reg .rdx = some (.lit 3680) ∧ (after b18 copyS).reg .rbp = some vN ∧
    (after b18 copyS).reg .r13 = some vQ ∧ KR [.rbx, .r12, .r14, .r15] (after b18 copyS) := by
  decide +kernel

public theorem exit_b19 : exec b19 retS = some (after b19 retS,
    .call NativeRustcVmX64.Vm.Powers.entryLabel) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 8176 64 slots (after b19 retS) = true ∧
    Wr [(64, 72), (4440, 4448)] (after b19 retS) ∧ WordW 0 4440 (.reg .rbp) (after b19 retS) ∧
    (after b19 retS).reg .rdi = some (.load 0 96 8) ∧ (after b19 retS).reg .rsi = some (.load 0 88 8) ∧
    (after b19 retS).reg .rdx = some (.ptr 0 4448) ∧ (after b19 retS).reg .rcx = some (.reg .rbp) ∧
    KR six (after b19 retS) := by decide +kernel

public theorem exit_b20 : exec b20 retS = some (after b20 retS,
    .call NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : MidOk 8176 64 slots (after b20 retS) = true ∧
    Wr [(64, 72), (120, 128)] (after b20 retS) ∧ WordW 0 120 (.reg .r13) (after b20 retS) ∧
    (after b20 retS).reg .rdi = some (.ptr 0 760) ∧ (after b20 retS).reg .rsi = some (.reg .r14) ∧
    (after b20 retS).reg .rdx = some (.reg .rbx) ∧ (after b20 retS).reg .rcx = some (.reg .r13) ∧
    (after b20 retS).reg .r8 = some (.reg .rbp) ∧ KR six (after b20 retS) := by decide +kernel

public theorem exit_b21 : exec b21 retS = some (after b21 retS, .cond cRows NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b21.trans (by rw [after_eq run_b21]; rfl)
public theorem ok_b21 : (after b21 retS).mem = [] ∧ (after b21 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b22 : exec b22 rowsS = some (after b22 rowsS,
    .call NativeRustcVmX64.Vm.EachRowOfNextLevel.entryLabel) :=
  run_b22.trans (by rw [after_eq run_b22])
public theorem ok_b22 : MidOk 8176 48 slots (after b22 rowsS) = true ∧
    Wr [(48, 72), (104, 120), (144, 176), (760, 808)] (after b22 rowsS) ∧
    WordW 0 56 vRc (after b22 rowsS) ∧ WordW 0 64 (.ptr 0 760) (after b22 rowsS) ∧
    WordW 0 760 (.ptr 0 80) (after b22 rowsS) ∧ WordW 0 768 (.ptr 0 176) (after b22 rowsS) ∧
    WordW 0 776 (.reg .r15) (after b22 rowsS) ∧ WordW 0 784 (.ptr 0 104) (after b22 rowsS) ∧
    WordW 0 792 vWp (after b22 rowsS) ∧ WordW 0 800 vWn (after b22 rowsS) ∧
    WordW 0 104 (.lit 0) (after b22 rowsS) ∧ WordW 0 112 (.lit 0) (after b22 rowsS) ∧
    WordW 0 144 (.load 0 760 8) (after b22 rowsS) ∧ WordW 0 152 (.load 0 768 8) (after b22 rowsS) ∧
    WordW 0 160 (.load 0 776 8) (after b22 rowsS) ∧ WordW 0 168 (.load 0 784 8) (after b22 rowsS) ∧
    (after b22 rowsS).reg .rdi = some (.reg .rbx) ∧ (after b22 rowsS).reg .rsi = some (.load 0 120 8) ∧
    (after b22 rowsS).reg .rdx = some (.reg .rbp) ∧ (after b22 rowsS).reg .rcx = some (.ptr 0 144) ∧
    (after b22 rowsS).reg .r8 = some (.reg .r12) ∧ (after b22 rowsS).reg .r9 = some vRp ∧
    (after b22 rowsS).reg .rbx = some (.load 0 120 8) ∧ (after b22 rowsS).reg .r13 = some vWp ∧
    (after b22 rowsS).reg .r14 = some vWn ∧ KR [.rbp, .r12, .r15] (after b22 rowsS) := by
  decide +kernel

public theorem exit_b23 : exec b23 s56S = some (after b23 s56S, .cond cAl NativeRustcVmX64.Vm.NextLevel.label_13) :=
  run_b23.trans (by rw [after_eq run_b23]; rfl)
public theorem ok_b23 : (after b23 s56S).mem = [] ∧ (after b23 s56S).regs = retS.regs := by
  decide +kernel

public theorem exit_b24 : exec b24 retS = some (after b24 retS,
    .call NativeRustcVmX64.Vm.GlueLevel.entryLabel) :=
  run_b24.trans (by rw [after_eq run_b24])
public theorem ok_b24 : MidOk 8176 0 slots (after b24 retS) = true ∧ Wr [(0, 72)] (after b24 retS) ∧
    WordW 0 8 (.load 0 136 8) (after b24 retS) ∧ WordW 0 16 (.load 0 128 8) (after b24 retS) ∧
    WordW 0 24 (.reg .rbx) (after b24 retS) ∧ WordW 0 32 (.reg .rbp) (after b24 retS) ∧
    WordW 0 40 (.reg .r13) (after b24 retS) ∧ WordW 0 48 (.reg .r14) (after b24 retS) ∧
    WordW 0 56 (.load 0 104 8) (after b24 retS) ∧ WordW 0 64 (.load 0 112 8) (after b24 retS) ∧
    (after b24 retS).reg .rdi = some (.load 0 8184 8) ∧ (after b24 retS).reg .rsi = some (.load 0 96 8) ∧
    (after b24 retS).reg .rdx = some (.load 0 88 8) ∧ (after b24 retS).reg .rcx = some (.load 0 80 8) ∧
    (after b24 retS).reg .r8 = some vOp ∧ (after b24 retS).reg .r9 = some vOn ∧
    KR six (after b24 retS) := by decide +kernel

public theorem exit_b25 : exec b25 s8S = some (after b25 s8S, .jump NativeRustcVmX64.Vm.NextLevel.label_14) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : MidOk 8176 72 slots (after b25 s8S) = true ∧ (after b25 s8S).mem = [] ∧
    (after b25 s8S).reg .r15 = some (.un .trunc .W32 (.reg .rax)) := by decide +kernel

public theorem exit_b26 : exec b26 retS = some (after b26 retS, .fall) :=
  run_b26.trans (by rw [after_eq run_b26])
public theorem ok_b26 : MidOk 8176 72 slots (after b26 retS) = true ∧ (after b26 retS).mem = [] ∧
    (after b26 retS).reg .r15 = some (.lit 0) := by decide +kernel

public theorem exit_b27 : exec b27 retS = some (after b27 retS, .ret (.load 0 8176 8)) :=
  run_b27.trans (by rw [after_eq run_b27])
public theorem ok_b27 : EpiOk 8176 slots (after b27 retS) = true ∧ (after b27 retS).mem = [] ∧
    (after b27 retS).reg .rax = some (.un .trunc .W32 (.reg .r15)) := by decide +kernel

end NativeRustcVmX64.Whir.Levels.NL
