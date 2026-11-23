module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Init
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval
public meta import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval
public meta import NativeRustcVmX64.Arrays.MultilinearEvalBy.Init

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure): its blocks, run by the symbolic executor
(x86-64)

The frame is `MleFrame`'s. From
- `Field.frameS 1216`: the prologue (`b0`);
- `MleFrame.zS`: a turn of the loop zeroing the pending entries (`b1`);
- `Field.midS 1216`: the flags zeroed and the tests `n = 0`, `|point| = 0` (`b2`, `b3`, `b18`),
  the arguments stored (`b4`), the outer loop's test (`b5`), the inner loop's set-up (`b9`), the
  calls (`s11b`, `b12`), the sum and the inner loop's test (`b13`), the epilogue (`b21`);
- `eS`: `mle[i]` (`b6`), region 1 the element;
- `ldS`: `mle[0]` at `|point| = 0` (`b19`);
- `MleFrame.flagS .r14`: `full[k]`'s test (`b10`);
- `MleFrame.pairS .r14 .r12`: a pairing's loads (`s11a`);
- `MleFrame.pushS .r14 .r12`: a pending entry's store (`b16`);
- `MleFrame.regsS`: the jumps and the zero result (`b14`, `b17`, `b20`).
-/

namespace NativeRustcVmX64.Arrays.MleOfMultilinearEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval
  NativeRustcVmX64.Field NativeRustcVmX64.Arrays.MleFrame

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 1216
/-- `mle[i]`: its address `mle + (i << 4)`, `mle` the frame's word at `24`, `i` in RDX. -/
def eS : SState :=
  elemS 1216 (.bin .add .W64 (.load 0 24 8) (.bin .shl .W64 (.reg .rdx) (.lit 4))) 0
/-- `mle[0]` at RSI. -/
def ldS : SState := init [16] [(.rsi, .ptr 0 0)]

/-- The pairing's loads. -/
def s11a : List Directive := b11.take 9
/-- The pairing's first call. -/
def s11b : List Directive := b11.drop 9

/-- The loop's registers: `full[k]` at R14, `16 k` in R12, the value in R15, RBP, `point[k]` in
RBX, R13. -/
def R1 : Regs := ⟨.r14, .r12, .r15, .rbp, .rbx, .r13⟩

theorem R1_saved : R1.Saved := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 zS
sym_block run_b2 := exec b2 (midS 1216)
sym_block run_b3 := exec b3 (after b2 (midS 1216))
sym_block run_b4 := exec b4 (after b3 (after b2 (midS 1216)))
sym_block run_b18 := exec b18 (after b3 (after b2 (midS 1216)))
sym_block run_b19 := exec b19 ldS
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 (midS 1216)
sym_block run_b5 := exec b5 (midS 1216)
sym_block run_b6 := exec b6 eS
sym_block run_b9 := exec b9 (midS 1216)
sym_block run_b10 := exec b10 (flagS .r14)
sym_block run_s11a := exec s11a (pairS .r14 .r12)
sym_block run_s11b := exec s11b (midS 1216)
sym_block run_b12 := exec b12 (midS 1216)
sym_block run_b13 := exec b13 (midS 1216)
sym_block run_b14 := exec b14 regsS
sym_block run_b16 := exec b16 (pushS .r14 .r12)
sym_block run_b17 := exec b17 regsS

/-! ## What the blocks do -/

public theorem b0_ok : EntryOk (after b0 entryS) ∧ (after b0 entryS).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem b1_ok : ZeroOk (after b1 zS) := by decide +kernel

public theorem init_ok : InitOk (after b2 (midS 1216)) ∧
    InitOk (after b3 (after b2 (midS 1216))) ∧
    InitOk (after b18 (after b3 (after b2 (midS 1216)))) ∧
    InitOk (after b4 (after b3 (after b2 (midS 1216)))) := by
  decide +kernel

public theorem b4_args : MleArgsOk (after b4 (after b3 (after b2 (midS 1216)))) := by decide +kernel

public theorem b18_rsi : (after b18 (after b3 (after b2 (midS 1216)))).reg .rsi = some (.reg .rsi) := by
  decide +kernel

public theorem b19_ok : keepsAll ldS (after b19 ldS) [] = true ∧
    (after b19 ldS).reg .r15 = some (.load 0 0 8) ∧ (after b19 ldS).reg .rbp = some (.load 0 8 8) := by
  decide +kernel

public theorem b20_ok : ZeroValOk R1 (after b20 regsS) := by decide +kernel

public theorem b21_ok : EndOk R1 (after b21 (midS 1216)) := by decide +kernel

public theorem b5_ok : keepsAll (midS 1216) (after b5 (midS 1216)) [] = true ∧
    (after b5 (midS 1216)).reg .rdx = some (.load 0 16 8) := by
  decide +kernel

public theorem b6_ok : keepsAll eS (after b6 eS) [.rdx] = true ∧
    (after b6 eS).reg .r15 = some (.load 1 0 8) ∧ (after b6 eS).reg .rbp = some (.load 1 8 8) := by
  decide +kernel

public theorem b9_ok : EnterOk R1 .rdx (.reg .r15) (.reg .rbp) (after b9 (midS 1216)) := by
  decide +kernel

public theorem b10_ok : TestOk R1 (after b10 (flagS .r14)) := by decide +kernel

public theorem s11a_ok : PairOk R1 (after s11a (pairS .r14 .r12)) := by decide +kernel

public theorem s11b_ok : Call1Ok R1 (after s11b (midS 1216)) := by decide +kernel

public theorem b12_ok : Call2Ok R1 (after b12 (midS 1216)) := by decide +kernel

public theorem b13_ok : SumOk R1 (after b13 (midS 1216)) := by decide +kernel

public theorem jumps_ok : JumpOk R1 (after b14 regsS) ∧ JumpOk R1 (after b17 regsS) := by
  decide +kernel

public theorem b16_ok : PushOk R1 (after b16 (pushS .r14 .r12)) := by decide +kernel

end NativeRustcVmX64.Arrays.MleOfMultilinearEval
