module

public import NativeRustcVmX64.Arrays.MultilinearEvalBy.Init
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue
public meta import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue
public meta import NativeRustcVmX64.Arrays.MultilinearEvalBy.Init

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure): its blocks, run by the symbolic
executor (x86-64)

The frame is `MleFrame`'s. From
- `Field.frameS 1216`: the prologue and the test `|point| > 63` (`b0`, then `b1`);
- `MleFrame.zS`: a turn of the loop zeroing the pending entries (`b2`);
- `Field.midS 1216`: the flags zeroed and the tests `n = 0`, `|point| = 0` (`b3`, `b4`, `b17`),
  the arguments stored (`b5`), the outer loop's test (`b6`), the inner loop's set-up (`b9`), the
  calls (`s11b`, `b12`), the sum and the inner loop's test (`b13`), the epilogue (`b20`);
- `eS`: `words[i]` (`b7`), region 1 the word;
- `ldS`: `words[0]` at `|point| = 0` (`b18`);
- `MleFrame.flagS .rbx`: `full[k]`'s test (`b10`);
- `MleFrame.pairS .rbx .r15`: a pairing's loads (`s11a`);
- `MleFrame.pushS .rbx .r15`: a pending entry's store (`b15`);
- `MleFrame.regsS`: the jumps and the zero result (`b14`, `b16`, `b19`).
-/

namespace NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue
  NativeRustcVmX64.Field NativeRustcVmX64.Arrays.MleFrame

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 1216
/-- `words[i]`: its address `words + 8 i`, `words` the frame's word at `24`, `i` in RCX. -/
def eS : SState :=
  init [1216 + 8, 8] [(.rsp, .ptr 0 8)]
    (aliases := [(.bin .add .W64 (.load 0 24 8) (.bin .mul .W64 (.reg .rcx) (.lit 8)), 1, 0)])
/-- `words[0]` at RSI. -/
def ldS : SState := init [8] [(.rsi, .ptr 0 0)]

/-- The pairing's loads. -/
def s11a : List Directive := b11.take 9
/-- The pairing's first call. -/
def s11b : List Directive := b11.drop 9

/-- The loop's registers: `full[k]` at RBX, `16 k` in R15, the value in R13, RBP, `point[k]` in
R14, R12. -/
def R2 : Regs := ⟨.rbx, .r15, .r13, .rbp, .r14, .r12⟩

theorem R2_saved : R2.Saved := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b19 := exec b19 regsS
sym_block run_b2 := exec b2 zS
sym_block run_b3 := exec b3 (midS 1216)
sym_block run_b4 := exec b4 (after b3 (midS 1216))
sym_block run_b17 := exec b17 (after b4 (after b3 (midS 1216)))
sym_block run_b18 := exec b18 ldS
sym_block run_b5 := exec b5 (after b4 (after b3 (midS 1216)))
sym_block run_b20 := exec b20 (midS 1216)
sym_block run_b6 := exec b6 (midS 1216)
sym_block run_b7 := exec b7 eS
sym_block run_b9 := exec b9 (midS 1216)
sym_block run_b10 := exec b10 (flagS .rbx)
sym_block run_s11a := exec s11a (pairS .rbx .r15)
sym_block run_s11b := exec s11b (midS 1216)
sym_block run_b12 := exec b12 (midS 1216)
sym_block run_b13 := exec b13 (midS 1216)
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 (pushS .rbx .r15)
sym_block run_b16 := exec b16 regsS

/-! ## What the blocks do -/

public theorem b0_ok : EntryOk (after b0 entryS) := by decide +kernel

public theorem b1_ok : EntryOk (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem b2_ok : ZeroOk (after b2 zS) := by decide +kernel

public theorem init_ok : InitOk (after b3 (midS 1216)) ∧
    InitOk (after b4 (after b3 (midS 1216))) ∧
    InitOk (after b17 (after b4 (after b3 (midS 1216)))) ∧
    InitOk (after b5 (after b4 (after b3 (midS 1216)))) := by
  decide +kernel

public theorem b5_args : MleArgsOk (after b5 (after b4 (after b3 (midS 1216)))) := by decide +kernel

public theorem b17_rsi : (after b17 (after b4 (after b3 (midS 1216)))).reg .rsi = some (.reg .rsi) := by
  decide +kernel

public theorem b18_ok : keepsAll ldS (after b18 ldS) [] = true ∧
    (after b18 ldS).reg .r13 = some (.load 0 0 8) ∧ (after b18 ldS).reg .rbp = some (.lit 0) := by
  decide +kernel

public theorem b19_ok : ZeroValOk R2 (after b19 regsS) := by decide +kernel

public theorem b20_ok : EndOk R2 (after b20 (midS 1216)) := by decide +kernel

public theorem b6_ok : keepsAll (midS 1216) (after b6 (midS 1216)) [] = true ∧
    (after b6 (midS 1216)).reg .rcx = some (.load 0 16 8) := by
  decide +kernel

public theorem b7_ok : keepsAll eS (after b7 eS) [.rcx] = true ∧
    (after b7 eS).reg .r13 = some (.load 1 0 8) := by
  decide +kernel

public theorem b9_ok : EnterOk R2 .rcx (.reg .r13) (.lit 0) (after b9 (midS 1216)) := by
  decide +kernel

public theorem b10_ok : TestOk R2 (after b10 (flagS .rbx)) := by decide +kernel

public theorem s11a_ok : PairOk R2 (after s11a (pairS .rbx .r15)) := by decide +kernel

public theorem s11b_ok : Call1Ok R2 (after s11b (midS 1216)) := by decide +kernel

public theorem b12_ok : Call2Ok R2 (after b12 (midS 1216)) := by decide +kernel

public theorem b13_ok : SumOk R2 (after b13 (midS 1216)) := by decide +kernel

public theorem jumps_ok : JumpOk R2 (after b14 regsS) ∧ JumpOk R2 (after b16 regsS) := by
  decide +kernel

public theorem b15_ok : PushOk R2 (after b15 (pushS .rbx .r15)) := by decide +kernel

end NativeRustcVmX64.Arrays.MleOfComputedBytecodeValue
