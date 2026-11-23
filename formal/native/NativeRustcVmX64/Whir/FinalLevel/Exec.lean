module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.FinalLevel
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public meta import NativeRustcVmX64.Code.Vm.FinalLevel
public meta import NativeRustcVmX64.Transcript.Frame
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `final_level`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 2672 bytes below the entry's RSP, the return address and the stack argument `w`
(2688 bytes, `argEnv`). RSP is at offset `40` in the body (a callee's return address at `32`; at
`each_row`'s call, after four words, at `0`; at `sumcheck_plain`'s, after two, at `16`); the six
pushed registers at `2624` to `2672`, the return address at `2672`, `w` at `2680`. The body's word
`N(%rsp)` is region 0's offset `40 + N`: `μ` at `40`, `laneFolds` (later the point's length) at
`48`, the basis (later the point's address) at `56`, an `Option<EW>` at `64`, the claim at `88`,
`96`, the glued loop's end at `104`, the rows' copy at `112`, the openings (later the sumcheck's
`Option<EW>`, then the rotated point) at `144`, the point at `632`, the tail at `1120`, the folded
scalars at `1600`.

- `entryS` at the entry (`b0`, `frameEnv`), region 1 the level (RDX);
- `zeroS` the first zeroing loop's body: region 0 the 1568 bytes at `RSP + RAX`;
- `retS` in the body, `levelS` with the level (region 1) at RBP (`frameEnv`: the level need not
  be apart from `w`'s word), `wS` with `w` (region 1) at RBP,
  `rowsS` with `w` (region 1) at the word `2680`, `bxS` with `w` at RBX, `gS` with a glued claim
  (region 1, 24 bytes) at R13;
- `s8S` after `each_row` (RSP at `8`), `s24S` after `sumcheck_plain` (RSP at `24`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FinalLevel NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots :=
  [(2664, .rbp), (2656, .r15), (2648, .r14), (2640, .r13), (2632, .r12), (2624, .rbx)]

/-- At the entry: the frame and the return address, RSP at offset `2672`; the level at RDX. -/
def entryS : SState := init [2680, 24] [(.rsp, .ptr 0 2672), (.rdx, .ptr 1 0)]

/-- The first zeroing loop's body: region 0 the 1568 bytes at `RSP + RAX`. -/
def zeroS : SState := init [1568] (aliases := [(.bin .add .W64 (.reg .rsp) (.reg .rax), (0, 0))])

/-- In the body: RSP at offset `40`. -/
def retS : SState := init [2688] [(.rsp, .ptr 0 40)]

/-- In the body with the level (region 1) at RBP. -/
def levelS : SState := init [2680, 24] [(.rsp, .ptr 0 40), (.rbp, .ptr 1 0)]

/-- In the body with `w` (region 1) at RBP. -/
def wS : SState := init [2688, 63200] [(.rsp, .ptr 0 40), (.rbp, .ptr 1 0)]

/-- In the body with `w` (region 1), its address the word at `2680`. -/
def rowsS : SState :=
  init [2688, 63200] [(.rsp, .ptr 0 40)] (aliases := [(.load 0 2680 8, (1, 0))])

/-- In the body with `w` (region 1) at RBX. -/
def bxS : SState := init [2688, 63200] [(.rsp, .ptr 0 40), (.rbx, .ptr 1 0)]

/-- In the body with a glued claim's first 24 bytes (region 1) at R13. -/
def gS : SState := init [2688, 24] [(.rsp, .ptr 0 40), (.r13, .ptr 1 0)]

/-- After `each_row`: RSP at offset `8`. -/
def s8S : SState := init [2688] [(.rsp, .ptr 0 8)]

/-- After `sumcheck_plain`: RSP at offset `24`. -/
def s24S : SState := init [2688] [(.rsp, .ptr 0 24)]

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
/-- `b1`'s exit: more to zero. -/
def cZero : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 64) (.reg .rax)) (.lit 1080))
/-- `b2`'s exit: `μ` above `63`. -/
def cMu : SBool :=
  .and (.not (.cmp .ult .W64 (.reg .rcx) (.lit 63))) (.not (.cmp .eq .W64 (.reg .rcx) (.lit 63)))
/-- `2 ^ μ`, as `b3` computes it. -/
def s14 : Sym := .bin .shl .W64 (.lit 1) (.reg .rcx)
/-- `2 ^ μ` plus the level's fold, as `b3` computes it. -/
def s13 : Sym := .bin .add .W64 s14 (.load 1 0 8)
/-- `b3`'s exit: the folded count overflows or exceeds `64`. -/
def cSize : SBool :=
  .not (.cmp .eq .W8 (.bin .or .W8
    (.bin .merge .W8 (.reg .rcx) (.ite (.not (.cmp .ult .W64 s13 (.lit 65))) (.lit 1) (.lit 0)))
    (.bin .merge .W8 (.reg .rax) (.ite (.cmp .ult .W64 s13 s14) (.lit 1) (.lit 0)))) (.lit 0))
/-- `b11`'s exit: `query_openings`' `None`. -/
def cRows : SBool := .cmp .eq .W64 (.load 0 144 8) (.lit 0)
/-- `b13`'s exit: `each_row`'s `false`. -/
def cCl : SBool :=
  .cmp .eq .W8 (.bin .and .W8 (.un .trunc .W32 (.reg .rax)) (.un .trunc .W32 (.reg .rax))) (.lit 0)
/-- `b14`'s exit: `μ` above `30`. -/
def cMu30 : SBool :=
  .and (.not (.cmp .ult .W64 (.load 0 40 8) (.lit 30))) (.not (.cmp .eq .W64 (.load 0 40 8) (.lit 30)))
/-- `b16`'s exit: the sumcheck's `None`. -/
def cTag144 : SBool := .not (.cmp .eq .W32 (.load 0 144 4) (.lit 1))
/-- `b26`'s exit: the basis' `None`. -/
def cTag64 : SBool := .not (.cmp .eq .W32 (.load 0 64 4) (.lit 1))
/-- `b27`'s glued claims' bytes. -/
def vGs : Sym := .ite (.cmp .ult .W64 (.load 1 504 8) (.lit 11))
  (.bin .mul .W64 (.load 1 504 8) (.lit 6064)) (.lit 0)
/-- `b27`'s exit: no glued claim. -/
def cNoG : SBool := .cmp .eq .W64 (.bin .and .W64 vGs vGs) (.lit 0)
/-- `b32`'s exit: more glued claims. -/
def cMore : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 6064) (.reg .r13)) (.load 0 104 8))

/-- `b10`'s query count, saturated. -/
def vN : Sym := .ite (.cmp .ult .W64 (.load 1 61352 8) (.lit 231)) (.load 1 61352 8) (.lit 0)
/-- `b10`'s query pointer. -/
def vQ : Sym := .ite (.not (.cmp .ult .W64 (.load 1 61352 8) (.lit 231))) (.lit 8) (.ptr 1 61360)
/-- `b12`'s rounds count. -/
def vRc : Sym := .ite (.not (.cmp .ult .W64 (.load 1 61152 8) (.lit 7))) (.lit 0) (.load 1 61152 8)
/-- `b12`'s rounds pointer. -/
def vRp : Sym := .ite (.cmp .ult .W64 (.load 1 61152 8) (.lit 7))
  (.bin .add .W64 (.lit 61160) (.load 0 2680 8)) (.lit 8)
/-- `b17`'s `α`s' count. -/
def vAn : Sym := .ite (.cmp .ult .W64 (.load 1 16 8) (.lit 31)) (.load 1 16 8) (.lit 0)
/-- `b17`'s `α`s' pointer. -/
def vAp : Sym := .ite (.cmp .ult .W64 (.load 1 16 8) (.lit 31)) (.ptr 1 24) (.lit 8)
/-- `b21`'s point length. -/
def vLen : Sym := .ite (.not (.cmp .ult .W64 (.load 0 632 8) (.lit 31))) (.lit 0) (.load 0 632 8)
/-- `b21`'s point pointer. -/
def vPt : Sym := .ite (.not (.cmp .ult .W64 (.load 0 632 8) (.lit 31))) (.lit 8) (.ptr 0 640)
/-- `b21`'s count of the point past `laneFolds`. -/
def vRd : Sym := .ite (.cmp .ult .W64 vLen (.load 0 48 8)) (.lit 0) (.bin .sub .W64 vLen (.load 0 48 8))
/-- `b21`'s pointer to the point past `laneFolds`. -/
def vRs : Sym := .ite (.cmp .ult .W64 vLen (.load 0 48 8)) (.lit 8)
  (.bin .add .W64 vPt (.bin .shl .W64 (.load 0 48 8) (.lit 4)))
/-- `b23`'s count of the point before `laneFolds`. -/
def vMin : Sym := .ite (.cmp .ult .W64 (.reg .r13) (.load 0 48 8)) (.reg .r13) (.load 0 48 8)
/-- `b25`'s rotated point's count. -/
def vBn : Sym := .ite (.cmp .ult .W64 (.load 0 144 8) (.lit 31)) (.load 0 144 8) (.lit 0)
/-- `b25`'s rotated point's pointer. -/
def vBp : Sym := .ite (.not (.cmp .ult .W64 (.load 0 144 8) (.lit 31))) (.lit 8) (.ptr 0 152)
/-- `b27`'s glued claims' pointer. -/
def vG13 : Sym := .ite (.cmp .ult .W64 (.load 1 504 8) (.lit 11))
  (.bin .add .W64 (.lit 512) (.load 0 2680 8)) (.reg .r13)
/-- `b29`'s point's count from the claim's fold start. -/
def vGc : Sym := .ite (.cmp .ult .W64 (.load 0 48 8) (.load 1 16 8)) (.lit 0)
  (.bin .sub .W64 (.load 0 48 8) (.load 1 16 8))
/-- `b29`'s point's pointer from the claim's fold start. -/
def vGd : Sym := .ite (.cmp .ult .W64 (.load 0 48 8) (.load 1 16 8)) (.lit 8)
  (.bin .add .W64 (.load 0 56 8) (.bin .shl .W64 (.load 1 16 8) (.lit 4)))
/-- `b35`'s verdict byte. -/
def vEnd : Sym := .ite (.cmp .eq .W64 (.bin .or .W64 (.bin .xor .W64 (.reg .rdx) (.load 0 96 8))
  (.bin .xor .W64 (.reg .rax) (.load 0 88 8))) (.lit 0)) (.lit 1) (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 zeroS
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 levelS
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 retS
sym_block run_b6 := exec b6 retS
sym_block run_b8a := exec (b8.take 2) levelS
sym_block run_b8b := exec (b8.drop 2) retS
sym_block run_b10 := exec b10 wS
sym_block run_b11 := exec b11 retS
sym_block run_b12 := exec b12 rowsS
sym_block run_b13 := exec b13 s8S
sym_block run_b14 := exec b14 retS
sym_block run_b15 := exec b15 rowsS
sym_block run_b16 := exec b16 s24S
sym_block run_b17 := exec b17 bxS
sym_block run_b19 := exec b19 retS
sym_block run_b21 := exec b21 retS
sym_block run_b23 := exec b23 retS
sym_block run_b25 := exec b25 retS
sym_block run_b26 := exec b26 retS
sym_block run_b27 := exec b27 rowsS
sym_block run_b28 := exec b28 retS
sym_block run_b29 := exec b29 gS
sym_block run_b31 := exec b31 retS
sym_block run_b32 := exec b32 retS
sym_block run_b33 := exec b33 retS
sym_block run_b34 := exec b34 retS
sym_block run_b35 := exec b35 retS
sym_block run_b36 := exec b36 retS
sym_block run_b37 := exec b37 retS

end NativeRustcVmX64.Whir.Levels.FL

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FinalLevel NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

public theorem b_eq : b7 = b5 ∧ b9 = b5 ∧ b18 = b5 ∧ b20 = b5 ∧ b22 = b5 ∧ b24 = b5 ∧ b30 = b26 := by
  decide +kernel

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .fall) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 2672 40 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 2672) ∧
    (after b0 entryS).reg .rax = some (.lit 56) ∧ (after b0 entryS).reg .rbx = some (.load 1 8 8) ∧
    (after b0 entryS).reg .rbp = some (.ptr 1 0) ∧
    KR [.rcx, .rsi, .rdi, .r8, .r9, .r12, .r13, .r14, .r15] (after b0 entryS) := by decide +kernel

public theorem exit_b1 : exec b1 zeroS = some (after b1 zeroS, .cond cZero NativeRustcVmX64.Vm.FinalLevel.label_1) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : (∀ w ∈ (after b1 zeroS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 1568) ∧
    (after b1 zeroS).reg .rax = some (.bin .add .W64 (.lit 64) (.reg .rax)) ∧
    KR (allRegs.filter (· != .rax)) (after b1 zeroS) := by decide +kernel

public theorem exit_b2 : exec b2 retS = some (after b2 retS, .cond cMu NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : (after b2 retS).mem = [] ∧ (after b2 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b3 : exec b3 levelS = some (after b3 levelS, .cond cSize NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem ok_b3 : MidOk 2672 40 slots (after b3 levelS) = true ∧ Wr [(40, 48)] (after b3 levelS) ∧
    WordW 0 40 (.reg .rcx) (after b3 levelS) ∧ (after b3 levelS).reg .r14 = some s14 ∧
    (after b3 levelS).reg .r13 = some s13 ∧ (after b3 levelS).reg .rbp = some (.ptr 1 0) ∧
    KR [.rbx, .r12, .r15, .rsi, .rdi, .r8, .r9] (after b3 levelS) := by decide +kernel

public theorem exit_b4 : exec b4 retS = some (after b4 retS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 2672 32 slots (after b4 retS) = true ∧
    Wr [(32, 40), (48, 64)] (after b4 retS) ∧ WordW 0 48 (.reg .r8) (after b4 retS) ∧
    WordW 0 56 (.reg .r9) (after b4 retS) ∧ (after b4 retS).reg .rsi = some (.ptr 0 1600) ∧
    (after b4 retS).reg .rdx = some (.reg .r13) ∧ (after b4 retS).reg .r12 = some (.reg .rdi) ∧
    (after b4 retS).reg .r15 = some (.reg .rsi) ∧
    KR [.rdi, .rbx, .rbp, .r13, .r14] (after b4 retS) := by decide +kernel

public theorem exit_b5 : exec b5 retS = some (after b5 retS, .cond cAl NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b5.trans (by rw [after_eq run_b5]; rfl)
public theorem ok_b5 : (after b5 retS).mem = [] ∧ (after b5 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b6 : exec b6 retS = some (after b6 retS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 2672 32 slots (after b6 retS) = true ∧ Wr [(32, 40)] (after b6 retS) ∧
    (after b6 retS).reg .rdi = some (.reg .r12) ∧ (after b6 retS).reg .rsi = some (.lit 17) ∧
    KR six (after b6 retS) := by decide +kernel

public theorem exit_b8a : exec (b8.take 2) levelS = some (after (b8.take 2) levelS, .fall) :=
  run_b8a.trans (by rw [after_eq run_b8a])
public theorem ok_b8a : MidOk 2672 40 slots (after (b8.take 2) levelS) = true ∧
    (after (b8.take 2) levelS).mem = [] ∧
    (after (b8.take 2) levelS).reg .rbx = some (.bin .add .W64 (.load 0 40 8) (.reg .rbx)) ∧
    (after (b8.take 2) levelS).reg .rdx = some (.load 1 16 8) ∧
    KR [.r12, .r13, .r14, .r15] (after (b8.take 2) levelS) := by decide +kernel
public theorem exit_b8b : exec (b8.drop 2) retS = some (after (b8.drop 2) retS,
    .call NativeRustcVmX64.Vm.SampleQueries.entryLabel) :=
  run_b8b.trans (by rw [after_eq run_b8b])
public theorem ok_b8b : MidOk 2672 32 slots (after (b8.drop 2) retS) = true ∧
    Wr [(32, 40)] (after (b8.drop 2) retS) ∧
    (after (b8.drop 2) retS).reg .rdi = some (.reg .r12) ∧
    (after (b8.drop 2) retS).reg .rsi = some (.reg .rbx) ∧
    (after (b8.drop 2) retS).reg .rcx = some (.bin .add .W64 (.load 0 2680 8) (.lit 61352)) ∧
    (after (b8.drop 2) retS).reg .rbp = some (.load 0 2680 8) ∧
    KR [.rdx, .rbx, .r12, .r13, .r14, .r15] (after (b8.drop 2) retS) := by decide +kernel

public theorem exit_b10 : exec b10 wS = some (after b10 wS,
    .call NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 2672 32 slots (after b10 wS) = true ∧ Wr [(32, 40)] (after b10 wS) ∧
    (after b10 wS).reg .rdi = some (.ptr 0 144) ∧ (after b10 wS).reg .rsi = some (.reg .r12) ∧
    (after b10 wS).reg .rdx = some (.reg .r15) ∧ (after b10 wS).reg .rcx = some vQ ∧
    (after b10 wS).reg .r8 = some vN ∧ (after b10 wS).reg .rbx = some vN ∧
    (after b10 wS).reg .rbp = some vQ ∧ KR [.r12, .r13, .r14, .r15] (after b10 wS) := by
  decide +kernel

public theorem exit_b11 : exec b11 retS = some (after b11 retS, .cond cRows NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b11.trans (by rw [after_eq run_b11]; rfl)
public theorem ok_b11 : (after b11 retS).mem = [] ∧ (after b11 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b12 : exec b12 rowsS = some (after b12 rowsS,
    .call NativeRustcVmX64.Vm.EachRowOfFinalLevel.entryLabel) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 2672 0 slots (after b12 rowsS) = true ∧
    Wr [(0, 32), (112, 144)] (after b12 rowsS) ∧ WordW 0 8 vRc (after b12 rowsS) ∧
    WordW 0 16 (.ptr 0 1600) (after b12 rowsS) ∧ WordW 0 24 (.reg .r13) (after b12 rowsS) ∧
    WordW 0 112 (.load 0 144 8) (after b12 rowsS) ∧ WordW 0 120 (.load 0 152 8) (after b12 rowsS) ∧
    WordW 0 128 (.load 0 160 8) (after b12 rowsS) ∧ WordW 0 136 (.load 0 168 8) (after b12 rowsS) ∧
    (after b12 rowsS).reg .rdi = some (.reg .r15) ∧ (after b12 rowsS).reg .rsi = some (.reg .rbp) ∧
    (after b12 rowsS).reg .rdx = some (.reg .rbx) ∧ (after b12 rowsS).reg .rcx = some (.ptr 0 112) ∧
    (after b12 rowsS).reg .r8 = some (.load 0 40 8) ∧ (after b12 rowsS).reg .r9 = some vRp ∧
    KR six (after b12 rowsS) := by decide +kernel

public theorem exit_b13 : exec b13 s8S = some (after b13 s8S, .cond cCl NativeRustcVmX64.Vm.FinalLevel.label_6) :=
  run_b13.trans (by rw [after_eq run_b13]; rfl)
public theorem ok_b13 : MidOk 2672 40 slots (after b13 s8S) = true ∧ (after b13 s8S).mem = [] ∧
    (after b13 s8S).reg .rax = some (.lit 0) ∧ KR six (after b13 s8S) := by decide +kernel

public theorem exit_b14 : exec b14 retS = some (after b14 retS, .cond cMu30 NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b14.trans (by rw [after_eq run_b14]; rfl)
public theorem ok_b14 : MidOk 2672 40 slots (after b14 retS) = true ∧
    Wr [(1120, 1600)] (after b14 retS) ∧ (after b14 retS).reg .rax = some (.load 0 40 8) ∧
    KR six (after b14 retS) := by decide +kernel

public theorem exit_b15 : exec b15 rowsS = some (after b15 rowsS,
    .call NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 2672 16 slots (after b15 rowsS) = true ∧
    Wr [(16, 32)] (after b15 rowsS) ∧ WordW 0 24 (.reg .rax) (after b15 rowsS) ∧
    (after b15 rowsS).reg .rdi = some (.ptr 0 144) ∧ (after b15 rowsS).reg .rsi = some (.reg .r12) ∧
    (after b15 rowsS).reg .rdx = some (.load 1 0 8) ∧ (after b15 rowsS).reg .rcx = some (.load 1 8 8) ∧
    (after b15 rowsS).reg .r8 = some (.lit 3) ∧ (after b15 rowsS).reg .r9 = some (.ptr 0 1120) ∧
    (after b15 rowsS).reg .rbx = some (.load 0 2680 8) ∧
    KR [.rbp, .r12, .r13, .r14, .r15] (after b15 rowsS) := by decide +kernel

public theorem exit_b16 : exec b16 s24S = some (after b16 s24S, .cond cTag144 NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b16.trans (by rw [after_eq run_b16]; rfl)
public theorem ok_b16 : MidOk 2672 40 slots (after b16 s24S) = true ∧ (after b16 s24S).mem = [] ∧
    KR (allRegs.filter (· != .rsp)) (after b16 s24S) := by decide +kernel

public theorem exit_b17 : exec b17 bxS = some (after b17 bxS,
    .call NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 2672 32 slots (after b17 bxS) = true ∧
    Wr [(32, 40), (632, 1120)] (after b17 bxS) ∧ WordW 0 632 (.lit 0) (after b17 bxS) ∧
    (after b17 bxS).reg .rdi = some (.ptr 0 632) ∧ (after b17 bxS).reg .rsi = some vAp ∧
    (after b17 bxS).reg .rdx = some vAn ∧ (after b17 bxS).reg .r12 = some (.load 0 152 8) ∧
    (after b17 bxS).reg .r15 = some (.load 0 160 8) ∧ (after b17 bxS).reg .rbx = some (.ptr 1 0) ∧
    KR [.rbp, .r13, .r14] (after b17 bxS) := by decide +kernel

public theorem exit_b19 : exec b19 retS = some (after b19 retS,
    .call NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 2672 32 slots (after b19 retS) = true ∧ Wr [(32, 40)] (after b19 retS) ∧
    (after b19 retS).reg .rdi = some (.ptr 0 632) ∧ (after b19 retS).reg .rsi = some (.ptr 0 1120) ∧
    (after b19 retS).reg .rdx = some (.load 0 40 8) ∧ KR six (after b19 retS) := by decide +kernel

public theorem exit_b21 : exec b21 retS = some (after b21 retS,
    .call NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : MidOk 2672 32 slots (after b21 retS) = true ∧
    Wr [(32, 40), (144, 632)] (after b21 retS) ∧ WordW 0 144 (.lit 0) (after b21 retS) ∧
    (after b21 retS).reg .rdi = some (.ptr 0 144) ∧ (after b21 retS).reg .rsi = some vRs ∧
    (after b21 retS).reg .rdx = some vRd ∧ (after b21 retS).reg .rbx = some vPt ∧
    (after b21 retS).reg .r13 = some vLen ∧ KR [.rbp, .r12, .r14, .r15] (after b21 retS) := by
  decide +kernel

public theorem exit_b23 : exec b23 retS = some (after b23 retS,
    .call NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  run_b23.trans (by rw [after_eq run_b23])
public theorem ok_b23 : MidOk 2672 32 slots (after b23 retS) = true ∧ Wr [(32, 40)] (after b23 retS) ∧
    (after b23 retS).reg .rdi = some (.ptr 0 144) ∧ (after b23 retS).reg .rsi = some (.reg .rbx) ∧
    (after b23 retS).reg .rdx = some vMin ∧ KR six (after b23 retS) := by decide +kernel

public theorem exit_b25 : exec b25 retS = some (after b25 retS,
    .call NativeRustcVmX64.Vm.BasisWEval.entryLabel) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : MidOk 2672 32 slots (after b25 retS) = true ∧
    Wr [(32, 40), (48, 56)] (after b25 retS) ∧ WordW 0 48 (.reg .r13) (after b25 retS) ∧
    (after b25 retS).reg .rdi = some (.ptr 0 64) ∧ (after b25 retS).reg .rsi = some (.load 0 56 8) ∧
    (after b25 retS).reg .rdx = some vBp ∧ (after b25 retS).reg .rcx = some vBn ∧
    (after b25 retS).reg .r13 = some (.lit 8) ∧
    KR [.rbx, .rbp, .r12, .r14, .r15] (after b25 retS) := by decide +kernel

public theorem exit_b26 : exec b26 retS = some (after b26 retS, .cond cTag64 NativeRustcVmX64.Vm.FinalLevel.label_5) :=
  run_b26.trans (by rw [after_eq run_b26]; rfl)
public theorem ok_b26 : (after b26 retS).mem = [] ∧ (after b26 retS).regs = retS.regs := by
  decide +kernel

public theorem exit_b27 : exec b27 rowsS = some (after b27 rowsS, .cond cNoG NativeRustcVmX64.Vm.FinalLevel.label_23) :=
  run_b27.trans (by rw [after_eq run_b27]; rfl)
public theorem ok_b27 : MidOk 2672 40 slots (after b27 rowsS) = true ∧
    Wr [(56, 64), (88, 104)] (after b27 rowsS) ∧ WordW 0 56 (.reg .rbx) (after b27 rowsS) ∧
    WordW 0 88 (.reg .r12) (after b27 rowsS) ∧ WordW 0 96 (.reg .r15) (after b27 rowsS) ∧
    (after b27 rowsS).reg .r15 = some (.load 0 72 8) ∧ (after b27 rowsS).reg .rbp = some (.load 0 80 8) ∧
    (after b27 rowsS).reg .r13 = some vG13 ∧ (after b27 rowsS).reg .rsi = some vGs ∧
    KR [.rbx, .r12, .r14] (after b27 rowsS) := by decide +kernel

public theorem exit_b28 : exec b28 retS = some (after b28 retS, .fall) :=
  run_b28.trans (by rw [after_eq run_b28])
public theorem ok_b28 : MidOk 2672 40 slots (after b28 retS) = true ∧ Wr [(104, 112)] (after b28 retS) ∧
    WordW 0 104 (.bin .add .W64 (.reg .r13) (.reg .rsi)) (after b28 retS) ∧
    KR six (after b28 retS) := by decide +kernel

public theorem exit_b29 : exec b29 gS = some (after b29 gS,
    .call NativeRustcVmX64.Vm.GluedEval.entryLabel) :=
  run_b29.trans (by rw [after_eq run_b29])
public theorem ok_b29 : MidOk 2672 32 slots (after b29 gS) = true ∧ Wr [(32, 40)] (after b29 gS) ∧
    (after b29 gS).reg .rdi = some (.ptr 0 64) ∧ (after b29 gS).reg .rsi = some (.ptr 1 0) ∧
    (after b29 gS).reg .rdx = some vGd ∧ (after b29 gS).reg .rcx = some vGc ∧
    (after b29 gS).reg .rbx = some (.load 1 0 8) ∧ (after b29 gS).reg .r12 = some (.load 1 8 8) ∧
    (after b29 gS).reg .r13 = some (.ptr 1 0) ∧ KR [.rbp, .r14, .r15] (after b29 gS) := by
  decide +kernel

public theorem exit_b31 : exec b31 retS = some (after b31 retS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b31 : MidOk 2672 32 slots (after b31 retS) = true ∧ Wr [(32, 40)] (after b31 retS) ∧
    (after b31 retS).reg .rdi = some (.reg .rbx) ∧ (after b31 retS).reg .rsi = some (.reg .r12) ∧
    (after b31 retS).reg .rdx = some (.load 0 72 8) ∧ (after b31 retS).reg .rcx = some (.load 0 80 8) ∧
    KR six (after b31 retS) := by decide +kernel

public theorem exit_b32 : exec b32 retS = some (after b32 retS, .cond cMore NativeRustcVmX64.Vm.FinalLevel.label_21) :=
  run_b32.trans (by rw [after_eq run_b32]; rfl)
public theorem ok_b32 : MidOk 2672 40 slots (after b32 retS) = true ∧ (after b32 retS).mem = [] ∧
    (after b32 retS).reg .r15 = some (.bin .xor .W64 (.reg .r15) (.reg .rax)) ∧
    (after b32 retS).reg .rbp = some (.bin .xor .W64 (.reg .rbp) (.reg .rdx)) ∧
    (after b32 retS).reg .r13 = some (.bin .add .W64 (.lit 6064) (.reg .r13)) ∧
    KR [.rbx, .r12, .r14] (after b32 retS) := by decide +kernel

public theorem exit_b33 : exec b33 retS = some (after b33 retS,
    .call NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) :=
  run_b33.trans (by rw [after_eq run_b33])
public theorem ok_b33 : MidOk 2672 32 slots (after b33 retS) = true ∧ Wr [(32, 40)] (after b33 retS) ∧
    (after b33 retS).reg .rdi = some (.reg .r14) ∧ (after b33 retS).reg .rsi = some (.ptr 0 1600) ∧
    (after b33 retS).reg .rdx = some (.reg .r14) ∧ (after b33 retS).reg .rcx = some (.ptr 0 1120) ∧
    (after b33 retS).reg .r8 = some (.load 0 40 8) ∧ KR six (after b33 retS) := by decide +kernel

public theorem exit_b34 : exec b34 retS = some (after b34 retS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b34.trans (by rw [after_eq run_b34])
public theorem ok_b34 : MidOk 2672 32 slots (after b34 retS) = true ∧ Wr [(32, 40)] (after b34 retS) ∧
    (after b34 retS).reg .rdi = some (.reg .r15) ∧ (after b34 retS).reg .rsi = some (.reg .rbp) ∧
    (after b34 retS).reg .rdx = some (.reg .rax) ∧ (after b34 retS).reg .rcx = some (.reg .rdx) ∧
    KR six (after b34 retS) := by decide +kernel

public theorem exit_b35 : exec b35 retS = some (after b35 retS, .jump NativeRustcVmX64.Vm.FinalLevel.label_6) :=
  run_b35.trans (by rw [after_eq run_b35])
public theorem ok_b35 : MidOk 2672 40 slots (after b35 retS) = true ∧ (after b35 retS).mem = [] ∧
    (after b35 retS).reg .rax = some (.bin .merge .W8 (.bin .xor .W64 (.reg .rax) (.load 0 88 8)) vEnd) ∧
    KR six (after b35 retS) := by decide +kernel

public theorem exit_b36 : exec b36 retS = some (after b36 retS, .fall) :=
  run_b36.trans (by rw [after_eq run_b36])
public theorem ok_b36 : MidOk 2672 40 slots (after b36 retS) = true ∧ (after b36 retS).mem = [] ∧
    (after b36 retS).reg .rax = some (.lit 0) ∧ KR six (after b36 retS) := by decide +kernel

public theorem exit_b37 : exec b37 retS = some (after b37 retS, .ret (.load 0 2672 8)) :=
  run_b37.trans (by rw [after_eq run_b37])
public theorem ok_b37 : EpiOk 2672 slots (after b37 retS) = true ∧ (after b37 retS).mem = [] ∧
    (after b37 retS).reg .rax = some (.reg .rax) := by decide +kernel

end NativeRustcVmX64.Whir.Levels.FL
