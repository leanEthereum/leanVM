module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.GkrStep
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public meta import NativeRustcVmX64.Code.Vm.GkrStep
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `gkr_step`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 1408-byte frame below the entry's RSP and the return address (`Frame`,
`F = 1408`): the pushed registers from `1360`, RSP at offset `40` in the body, a callee's return
address at `32` (the sumcheck's at `0`, its three stack arguments at `8` to `32`). In the frame:
`last` at `44` (4 bytes), the coordinates `y` at `48`, the sumcheck's claim at `80` (limb `1`) and
`88` (limb `0`), the point's address at `96`, the combiner's limb `0` at `104`, the sumcheck's
`Option<EW>` at `112`, then the children at `112`, `176`, `240`, the products at `304`, the
sumcheck's challenges from `352`.

- `entryS` at the entry (`b0`); `headS` in the body; `sS` in the body with region 1 the
  `GkrStateW` (R14); `s8S` after the sumcheck's call (RSP at `8`).
- The loops run without the frame as a region: `zS` (`b6`, region 0 the 48 bytes it zeroes),
  `cS` (`b37`, region 0 the two point slots it writes, region 1 the two challenges it reads),
  `tS` (`b39`, region 0 the point's address in the frame, region 1 the challenge it reads,
  region 2 the slot it writes), their addresses as aliases.
-/

namespace NativeRustcVmX64.Bus.GkrStep

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(1400, .rbp), (1392, .r15), (1384, .r14), (1376, .r13), (1368, .r12), (1360, .rbx)]

def entryS : SState := init [1416] [(.rsp, .ptr 0 1408)]
def headS : SState := init [1416] [(.rsp, .ptr 0 40)]
def sS : SState := init [1416, 1064] [(.rsp, .ptr 0 40), (.r14, .ptr 1 0)]
def s8S : SState := init [1416] [(.rsp, .ptr 0 8)]

def zS : SState :=
  init [48] [] [] [] [(.bin .add .W64 (.reg .rsp) (.reg .rcx), 0, -272)]
def cS : SState :=
  init [32, 32] [] [] []
    [(.bin .add .W64 (.reg .r14) (.reg .rdx), 0, 0),
     (.bin .add .W64 (.reg .rsp) (.reg .rdx), 1, -256)]
/-- `b39`'s slot address: the point's address loaded, `16 step`, `16 i`. -/
def dstS : Sym :=
  .bin .add .W64 (.bin .add .W64 (.reg .rbx) (.load 0 0 8)) (.bin .shl .W64 (.reg .rax) (.lit 4))
def tS : SState :=
  init [8, 16, 16] [] [] []
    [(.reg .rsp, 0, -56),
     (.bin .add .W64 (.reg .rsp) (.bin .shl .W64 (.reg .rax) (.lit 4)), 1, -312), (dstS, 2, 0)]

/-- The writes of region 0 within the intervals. -/
def W0 (S : SState) (ivs : List (Nat × Nat)) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && ivs.any fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2)

/-- The writes of region 0 within the intervals or of region 1 within `[lo, hi)`. -/
def W01 (S : SState) (ivs : List (Nat × Nat)) (lo hi : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && ivs.any fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))
    || (w.r == 1 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi))

/-- The registers a block keeps. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- The callee-saved registers. -/
abbrev cs6 : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `test %al, %al`: zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- The first grind's bits. -/
def bits1S : Sym :=
  .un .trunc .W32 (.ite (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.lit 0)
    (.bin .sub .W32 (.reg .rax) (.lit 3)))
/-- The second grind's bits. -/
def bits2S : Sym :=
  .ite (.not (.cmp .ult .W32 (.reg .rax) (.lit 3))) (.bin .sub .W32 (.reg .rax) (.lit 3)) (.lit 0)
/-- `|point|`, as `b7` reads it. -/
def lenS : Sym := .ite (.cmp .ult .W64 (.load 1 48 8) (.lit 64)) (.load 1 48 8) (.lit 0)
/-- `1 << step`. -/
def powS : Sym := .bin .shl .W64 (.lit 1) (.un .trunc .W32 (.reg .rbx))
/-- `b28`'s exit: `step + |x| > 63`. -/
def c28 : SBool :=
  .and (.not (.cmp .ult .W64 (.bin .add .W64 (.reg .rbx) (.reg .r13)) (.lit 63)))
    (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .rbx) (.reg .r13)) (.lit 63)))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 headS
sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 headS
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 zS
sym_block run_b7 := exec b7 sS
sym_block run_b8 := exec b8 s8S
sym_block run_b9 := exec b9 headS
sym_block run_b10 := exec b10 headS
sym_block run_b11 := exec b11 headS
sym_block run_b13 := exec b13 headS
sym_block run_b15 := exec b15 headS
sym_block run_b16 := exec b16 headS
sym_block run_b17 := exec b17 headS
sym_block run_b18 := exec b18 headS
sym_block run_b19 := exec b19 headS
sym_block run_b20 := exec b20 headS
sym_block run_b21 := exec b21 headS
sym_block run_b22 := exec b22 headS
sym_block run_b24 := exec b24 headS
sym_block run_b25 := exec b25 headS
sym_block run_b26 := exec b26 sS
sym_block run_b27 := exec b27 sS
sym_block run_b28 := exec b28 sS
sym_block run_b29 := exec b29 sS
sym_block run_b30 := exec b30 sS
sym_block run_b31 := exec b31 headS
sym_block run_b32 := exec b32 headS
sym_block run_b33 := exec b33 headS
sym_block run_b34 := exec b34 headS
sym_block run_b35 := exec b35 headS
sym_block run_b36 := exec b36 headS
sym_block run_b37 := exec b37 cS
sym_block run_b38 := exec b38 headS
sym_block run_b39 := exec b39 tS
sym_block run_b40 := exec b40 headS

/-! ## The prologue to the sumcheck -/

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 1408 32 slots (after b0 entryS) = true ∧
    W0 (after b0 entryS) [(32, 40), (1360, 1408)] = true ∧
    (after b0 entryS).reg .rdi = some (.lit 1) ∧ (after b0 entryS).reg .r14 = some (.reg .rcx) ∧
    (after b0 entryS).reg .r12 = some (.un .trunc .W32 (.reg .rdx)) ∧
    (after b0 entryS).reg .rbx = some (.reg .rsi) ∧ (after b0 entryS).reg .r15 = some (.reg .rdi) := by
  decide +kernel

public theorem exit_b1 : exec b1 headS = some (after b1 headS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk 1408 32 slots (after b1 headS) = true ∧
    W0 (after b1 headS) [(32, 40)] = true ∧
    (after b1 headS).reg .rsi = some bits1S ∧ (after b1 headS).reg .rdi = some (.reg .r15) ∧
    (after b1 headS).reg .rbp = some (.lit 0) ∧
    Keeps (after b1 headS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 headS = some (after b2 headS, .cond cAl NativeRustcVmX64.Vm.GkrStep.label_18) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 1408 40 slots (after b2 headS) = true ∧ (after b2 headS).mem = [] ∧
    Keeps (after b2 headS) cs6 = true := by
  decide +kernel

public theorem exit_b3 : exec b3 headS = some (after b3 headS,
    .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 1408 32 slots (after b3 headS) = true ∧
    W0 (after b3 headS) [(32, 40), (44, 48)] = true ∧
    (∀ t < 4, findWrite 0 (44 + t) (after b3 headS).mem = some (.un .trunc .W32 (.reg .r12), t)) ∧
    (after b3 headS).reg .rdi = some (.reg .r15) ∧ Keeps (after b3 headS) cs6 = true := by
  decide +kernel

public theorem exit_b4 : exec b4 headS = some (after b4 headS,
    .call NativeRustcVmX64.Vm.PolyEval.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 1408 32 slots (after b4 headS) = true ∧
    W0 (after b4 headS) [(32, 40), (104, 112)] = true ∧ WordW 0 104 (.reg .rax) (after b4 headS) ∧
    (after b4 headS).reg .rbp = some (.reg .rdx) ∧ (after b4 headS).reg .rsi = some (.lit 3) ∧
    (after b4 headS).reg .rdi = some (.reg .r14) ∧ (after b4 headS).reg .rdx = some (.reg .rax) ∧
    (after b4 headS).reg .rcx = some (.reg .rdx) ∧
    Keeps (after b4 headS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 headS = some (after b5 headS, .fall) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 1408 40 slots (after b5 headS) = true ∧ (after b5 headS).mem = [] ∧
    (after b5 headS).reg .r10 = some (.reg .rdx) ∧ (after b5 headS).reg .rcx = some (.lit 40) ∧
    Keeps (after b5 headS) (.rax :: cs6) = true := by
  decide +kernel

public theorem exit_b6 : exec b6 zS = some (after b6 zS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 48) (.reg .rcx)) (.lit 1048)).not
      NativeRustcVmX64.Vm.GkrStep.label_2) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : (∀ w ∈ (after b6 zS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b6 zS).reg .rcx = some (.bin .add .W64 (.lit 48) (.reg .rcx)) ∧
    Keeps (after b6 zS) (.rsp :: .rax :: .r10 :: cs6) = true := by
  decide +kernel

public theorem exit_b7 : exec b7 sS = some (after b7 sS,
    .call NativeRustcVmX64.Vm.SumcheckOfGkrStep.entryLabel) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk 1408 0 slots (after b7 sS) = true ∧
    W0 (after b7 sS) [(0, 40), (96, 104)] = true ∧
    WordW 0 8 lenS (after b7 sS) ∧ WordW 0 16 (.ptr 0 352) (after b7 sS) ∧
    WordW 0 24 lenS (after b7 sS) ∧ WordW 0 96 (.ptr 1 56) (after b7 sS) ∧
    (after b7 sS).reg .rdi = some (.ptr 0 112) ∧ (after b7 sS).reg .rsi = some (.reg .r15) ∧
    (after b7 sS).reg .rdx = some (.reg .rax) ∧ (after b7 sS).reg .rcx = some (.reg .r10) ∧
    (after b7 sS).reg .r8 = some (.bin .bts .W64 (.lit 1) (.reg .rbx)) ∧
    (after b7 sS).reg .r9 = some (.ite (.cmp .ult .W64 (.load 1 48 8) (.lit 64)) (.ptr 1 56) (.lit 8)) ∧
    (after b7 sS).reg .r12 = some powS ∧ (after b7 sS).reg .r13 = some lenS ∧
    (after b7 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b7 sS) [.rbx, .rbp, .r15] = true := by
  decide +kernel

public theorem exit_b8 : exec b8 s8S = some (after b8 s8S,
    .cond (SBool.cmp .eq .W32 (.load 0 112 4) (.lit 1)).not NativeRustcVmX64.Vm.GkrStep.label_17) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 1408 40 slots (after b8 s8S) = true ∧ (after b8 s8S).mem = [] ∧
    Keeps (after b8 s8S) cs6 = true := by
  decide +kernel

/-! ## The children -/

public theorem exit_b9 : exec b9 headS = some (after b9 headS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 1408 32 slots (after b9 headS) = true ∧
    W0 (after b9 headS) [(32, 40), (80, 96), (112, 304)] = true ∧
    WordW 0 88 (.load 0 120 8) (after b9 headS) ∧ WordW 0 80 (.load 0 128 8) (after b9 headS) ∧
    (after b9 headS).reg .rsi = some (.ptr 0 112) ∧ (after b9 headS).reg .rdi = some (.reg .r15) ∧
    (after b9 headS).reg .rdx = some (.reg .r12) ∧ Keeps (after b9 headS) cs6 = true := by
  decide +kernel

public theorem exit_b10 : exec b10 headS = some (after b10 headS, .cond cAl NativeRustcVmX64.Vm.GkrStep.label_17) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : MidOk 1408 40 slots (after b10 headS) = true ∧
    (after b10 headS).mem = [] ∧ Keeps (after b10 headS) cs6 = true := by
  decide +kernel

/-- `b12`, `b14`, `b23` are `b10`. -/
public theorem b12_eq : b12 = b10 := by decide
public theorem b14_eq : b14 = b10 := by decide
public theorem b23_eq : b23 = b10 := by decide

public theorem exit_b11 : exec b11 headS = some (after b11 headS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 1408 32 slots (after b11 headS) = true ∧
    W0 (after b11 headS) [(32, 40)] = true ∧
    (after b11 headS).reg .rsi = some (.ptr 0 176) ∧ (after b11 headS).reg .rdi = some (.reg .r15) ∧
    (after b11 headS).reg .rdx = some (.reg .r12) ∧ Keeps (after b11 headS) cs6 = true := by
  decide +kernel

public theorem exit_b13 : exec b13 headS = some (after b13 headS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 1408 32 slots (after b13 headS) = true ∧
    W0 (after b13 headS) [(32, 40)] = true ∧
    (after b13 headS).reg .rsi = some (.ptr 0 240) ∧ (after b13 headS).reg .rdi = some (.reg .r15) ∧
    (after b13 headS).reg .rdx = some (.reg .r12) ∧ Keeps (after b13 headS) cs6 = true := by
  decide +kernel

/-! ## The products and the check -/

public theorem exit_b15 : exec b15 headS = some (after b15 headS,
    .call NativeRustcVmX64.Vm.ProdE.entryLabel) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 1408 32 slots (after b15 headS) = true ∧
    W0 (after b15 headS) [(32, 40)] = true ∧
    (after b15 headS).reg .rdi = some (.ptr 0 112) ∧ (after b15 headS).reg .rsi = some (.reg .r12) ∧
    Keeps (after b15 headS) cs6 = true := by
  decide +kernel

public theorem exit_b16 : exec b16 headS = some (after b16 headS,
    .call NativeRustcVmX64.Vm.ProdE.entryLabel) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : MidOk 1408 32 slots (after b16 headS) = true ∧
    W0 (after b16 headS) [(32, 40), (304, 320)] = true ∧
    WordW 0 304 (.reg .rax) (after b16 headS) ∧ WordW 0 312 (.reg .rdx) (after b16 headS) ∧
    (after b16 headS).reg .rdi = some (.ptr 0 176) ∧ (after b16 headS).reg .rsi = some (.reg .r12) ∧
    Keeps (after b16 headS) cs6 = true := by
  decide +kernel

public theorem exit_b17 : exec b17 headS = some (after b17 headS,
    .call NativeRustcVmX64.Vm.ProdE.entryLabel) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : MidOk 1408 32 slots (after b17 headS) = true ∧
    W0 (after b17 headS) [(32, 40), (320, 336)] = true ∧
    WordW 0 320 (.reg .rax) (after b17 headS) ∧ WordW 0 328 (.reg .rdx) (after b17 headS) ∧
    (after b17 headS).reg .rdi = some (.ptr 0 240) ∧ (after b17 headS).reg .rsi = some (.reg .r12) ∧
    Keeps (after b17 headS) cs6 = true := by
  decide +kernel

public theorem exit_b18 : exec b18 headS = some (after b18 headS,
    .call NativeRustcVmX64.Vm.PolyEval.entryLabel) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : MidOk 1408 32 slots (after b18 headS) = true ∧
    W0 (after b18 headS) [(32, 40), (336, 352)] = true ∧
    WordW 0 336 (.reg .rax) (after b18 headS) ∧ WordW 0 344 (.reg .rdx) (after b18 headS) ∧
    (after b18 headS).reg .rdi = some (.ptr 0 304) ∧ (after b18 headS).reg .rsi = some (.lit 3) ∧
    (after b18 headS).reg .rdx = some (.load 0 104 8) ∧
    (after b18 headS).reg .rcx = some (.reg .rbp) ∧ Keeps (after b18 headS) cs6 = true := by
  decide +kernel

public theorem exit_b19 : exec b19 headS = some (after b19 headS,
    .cond (SBool.cmp .eq .W64 (.load 0 88 8) (.reg .rax)).not NativeRustcVmX64.Vm.GkrStep.label_17) :=
  run_b19.trans (by rw [after_eq run_b19])
public theorem ok_b19 : MidOk 1408 40 slots (after b19 headS) = true ∧
    (after b19 headS).mem = [] ∧ Keeps (after b19 headS) (.rdx :: cs6) = true := by
  decide +kernel

public theorem exit_b20 : exec b20 headS = some (after b20 headS,
    .cond (SBool.cmp .eq .W64 (.load 0 80 8) (.reg .rdx)).not NativeRustcVmX64.Vm.GkrStep.label_17) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : MidOk 1408 40 slots (after b20 headS) = true ∧
    (after b20 headS).mem = [] ∧ Keeps (after b20 headS) cs6 = true := by
  decide +kernel

/-! ## The second grind, the coordinates, the new values -/

public theorem exit_b21 : exec b21 headS = some (after b21 headS,
    .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : MidOk 1408 32 slots (after b21 headS) = true ∧
    W0 (after b21 headS) [(32, 40)] = true ∧
    (after b21 headS).reg .rdi =
      some (.bin .sub .W64 (.bin .shl .W64 (.reg .rbx) (.load 0 44 4)) (.lit 1)) ∧
    Keeps (after b21 headS) cs6 = true := by
  decide +kernel

public theorem exit_b22 : exec b22 headS = some (after b22 headS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b22.trans (by rw [after_eq run_b22])
public theorem ok_b22 : MidOk 1408 32 slots (after b22 headS) = true ∧
    W0 (after b22 headS) [(32, 40)] = true ∧
    (after b22 headS).reg .rsi = some bits2S ∧ (after b22 headS).reg .rdi = some (.reg .r15) ∧
    Keeps (after b22 headS) cs6 = true := by
  decide +kernel

public theorem exit_b24 : exec b24 headS = some (after b24 headS,
    .call NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) :=
  run_b24.trans (by rw [after_eq run_b24])
public theorem ok_b24 : MidOk 1408 32 slots (after b24 headS) = true ∧
    W0 (after b24 headS) [(32, 40), (48, 80)] = true ∧
    (after b24 headS).reg .rdi = some (.reg .r15) ∧ (after b24 headS).reg .rsi = some (.ptr 0 48) ∧
    (after b24 headS).reg .rdx = some (.reg .rbx) ∧ (after b24 headS).reg .rbp = some (.ptr 0 48) ∧
    Keeps (after b24 headS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b25 : exec b25 headS = some (after b25 headS,
    .call NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : MidOk 1408 32 slots (after b25 headS) = true ∧
    W0 (after b25 headS) [(32, 40)] = true ∧
    (after b25 headS).reg .rdi = some (.reg .r12) ∧ (after b25 headS).reg .rsi = some (.ptr 0 112) ∧
    (after b25 headS).reg .rdx = some (.reg .r12) ∧ (after b25 headS).reg .rcx = some (.reg .rbp) ∧
    (after b25 headS).reg .r8 = some (.reg .rbx) ∧ Keeps (after b25 headS) cs6 = true := by
  decide +kernel

public theorem exit_b26 : exec b26 sS = some (after b26 sS,
    .call NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) :=
  run_b26.trans (by rw [after_eq run_b26])
public theorem ok_b26 : MidOk 1408 32 slots (after b26 sS) = true ∧
    W01 (after b26 sS) [(32, 40)] 0 16 = true ∧
    WordW 1 0 (.reg .rax) (after b26 sS) ∧ WordW 1 8 (.reg .rdx) (after b26 sS) ∧
    (after b26 sS).reg .rdi = some (.reg .r12) ∧ (after b26 sS).reg .rsi = some (.ptr 0 176) ∧
    (after b26 sS).reg .rdx = some (.reg .r12) ∧ (after b26 sS).reg .rcx = some (.reg .rbp) ∧
    (after b26 sS).reg .r8 = some (.reg .rbx) ∧ (after b26 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b26 sS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b27 : exec b27 sS = some (after b27 sS,
    .call NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) :=
  run_b27.trans (by rw [after_eq run_b27])
public theorem ok_b27 : MidOk 1408 32 slots (after b27 sS) = true ∧
    W01 (after b27 sS) [(32, 40)] 16 32 = true ∧
    WordW 1 16 (.reg .rax) (after b27 sS) ∧ WordW 1 24 (.reg .rdx) (after b27 sS) ∧
    (after b27 sS).reg .rdi = some (.reg .r12) ∧ (after b27 sS).reg .rsi = some (.ptr 0 240) ∧
    (after b27 sS).reg .rdx = some (.reg .r12) ∧ (after b27 sS).reg .rcx = some (.reg .rbp) ∧
    (after b27 sS).reg .r8 = some (.reg .rbx) ∧ (after b27 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b27 sS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b28 : exec b28 sS = some (after b28 sS, .cond c28 NativeRustcVmX64.Vm.GkrStep.label_17) :=
  run_b28.trans (by rw [after_eq run_b28]; rfl)
public theorem ok_b28 : MidOk 1408 40 slots (after b28 sS) = true ∧
    W01 (after b28 sS) [] 32 48 = true ∧
    WordW 1 32 (.reg .rax) (after b28 sS) ∧ WordW 1 40 (.reg .rdx) (after b28 sS) ∧
    (after b28 sS).reg .rax = some (.bin .add .W64 (.reg .rbx) (.reg .r13)) ∧
    (after b28 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b28 sS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

/-! ## The point -/

public theorem exit_b29 : exec b29 sS = some (after b29 sS,
    .cond (.cmp .eq .W64 (.reg .rbx) (.lit 1)) NativeRustcVmX64.Vm.GkrStep.label_13) :=
  run_b29.trans (by rw [after_eq run_b29])
public theorem ok_b29 : MidOk 1408 40 slots (after b29 sS) = true ∧
    W01 (after b29 sS) [] 48 72 = true ∧
    WordW 1 48 (.reg .rax) (after b29 sS) ∧ WordW 1 56 (.load 0 48 8) (after b29 sS) ∧
    WordW 1 64 (.load 0 56 8) (after b29 sS) ∧ (after b29 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b29 sS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b30 : exec b30 sS = some (after b30 sS, .fall) :=
  run_b30.trans (by rw [after_eq run_b30])
public theorem ok_b30 : MidOk 1408 40 slots (after b30 sS) = true ∧
    W01 (after b30 sS) [] 72 88 = true ∧
    WordW 1 72 (.load 0 64 8) (after b30 sS) ∧ WordW 1 80 (.load 0 72 8) (after b30 sS) ∧
    (after b30 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b30 sS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b31 : exec b31 headS = some (after b31 headS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0)) NativeRustcVmX64.Vm.GkrStep.label_23) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b31 : MidOk 1408 40 slots (after b31 headS) = true ∧
    (after b31 headS).mem = [] ∧ Keeps (after b31 headS) cs6 = true := by
  decide +kernel

public theorem exit_b32 : exec b32 headS = some (after b32 headS,
    .cond (SBool.cmp .eq .W64 (.reg .r13) (.lit 1)).not NativeRustcVmX64.Vm.GkrStep.label_19) :=
  run_b32.trans (by rw [after_eq run_b32])
public theorem ok_b32 : MidOk 1408 40 slots (after b32 headS) = true ∧
    (after b32 headS).mem = [] ∧
    (after b32 headS).reg .rbx = some (.bin .shl .W64 (.reg .rbx) (.lit 4)) ∧
    Keeps (after b32 headS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b33 : exec b33 headS = some (after b33 headS, .jump NativeRustcVmX64.Vm.GkrStep.label_22) :=
  run_b33.trans (by rw [after_eq run_b33])
public theorem ok_b33 : MidOk 1408 40 slots (after b33 headS) = true ∧
    (after b33 headS).mem = [] ∧ (after b33 headS).reg .rax = some (.lit 0) ∧
    Keeps (after b33 headS) cs6 = true := by
  decide +kernel

public theorem exit_b34 : exec b34 headS = some (after b34 headS, .fall) :=
  run_b34.trans (by rw [after_eq run_b34])
public theorem ok_b34 : MidOk 1408 40 slots (after b34 headS) = true ∧
    (after b34 headS).mem = [] ∧ (after b34 headS).reg .rbp = some (.lit 0) := by
  decide +kernel

public theorem exit_b35 : exec b35 headS = some (after b35 headS, .ret (.load 0 1408 8)) :=
  run_b35.trans (by rw [after_eq run_b35])
public theorem ok_b35 : EpiOk 1408 slots (after b35 headS) = true ∧ (after b35 headS).mem = [] ∧
    (after b35 headS).reg .rax = some (.un .trunc .W32 (.reg .rbp)) := by
  decide +kernel

public theorem exit_b36 : exec b36 headS = some (after b36 headS, .fall) :=
  run_b36.trans (by rw [after_eq run_b36])
public theorem ok_b36 : MidOk 1408 40 slots (after b36 headS) = true ∧
    (after b36 headS).mem = [] ∧
    (after b36 headS).reg .rcx = some (.bin .and .W32 (.un .trunc .W32 (.reg .r13)) (.lit 62)) ∧
    (after b36 headS).reg .r14 = some (.bin .add .W64 (.reg .rbx) (.reg .r14)) ∧
    (after b36 headS).reg .rdx = some (.lit 56) ∧ (after b36 headS).reg .rax = some (.lit 0) ∧
    Keeps (after b36 headS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b37 : exec b37 cS = some (after b37 cS,
    .cond (SBool.cmp .eq .W64 (.reg .rcx) (.bin .add .W64 (.lit 2) (.reg .rax))).not
      NativeRustcVmX64.Vm.GkrStep.label_20) :=
  run_b37.trans (by rw [after_eq run_b37])
public theorem ok_b37 : (∀ w ∈ (after b37 cS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    WordW 0 0 (.load 1 0 8) (after b37 cS) ∧ WordW 0 8 (.load 1 8 8) (after b37 cS) ∧
    WordW 0 16 (.load 1 16 8) (after b37 cS) ∧ WordW 0 24 (.load 1 24 8) (after b37 cS) ∧
    (after b37 cS).reg .rax = some (.bin .add .W64 (.lit 2) (.reg .rax)) ∧
    (after b37 cS).reg .rdx = some (.bin .add .W64 (.lit 32) (.reg .rdx)) ∧
    Keeps (after b37 cS) (.rsp :: .rcx :: cs6) = true := by
  decide +kernel

public theorem exit_b38 : exec b38 headS = some (after b38 headS,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.GkrStep.label_23) :=
  run_b38.trans (by rw [after_eq run_b38])
public theorem ok_b38 : MidOk 1408 40 slots (after b38 headS) = true ∧
    (after b38 headS).mem = [] ∧ Keeps (after b38 headS) (.rax :: cs6) = true := by
  decide +kernel

public theorem exit_b39 : exec b39 tS = some (after b39 tS, .fall) :=
  run_b39.trans (by rw [after_eq run_b39])
public theorem ok_b39 : (∀ w ∈ (after b39 tS).mem, w.r = 2 ∧ w.off + w.n ≤ 16) ∧
    WordW 2 0 (.load 1 0 8) (after b39 tS) ∧ WordW 2 8 (.load 1 8 8) (after b39 tS) ∧
    Keeps (after b39 tS) (.rsp :: cs6) = true := by
  decide +kernel

public theorem exit_b40 : exec b40 headS = some (after b40 headS, .jump NativeRustcVmX64.Vm.GkrStep.label_18) :=
  run_b40.trans (by rw [after_eq run_b40])
public theorem ok_b40 : MidOk 1408 40 slots (after b40 headS) = true ∧
    (after b40 headS).mem = [] ∧
    (after b40 headS).reg .rbp = some (.bin .merge .W8 (.reg .rbp) (.lit 1)) := by
  decide +kernel

end NativeRustcVmX64.Bus.GkrStep
