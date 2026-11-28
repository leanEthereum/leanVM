module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue
public meta import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure): its blocks, run by the symbolic executor

The frame as in `multilinear_eval`'s instance (`MleFrame`). The entry is the word `words[i]` in
X22 (X23 = 0).

- `entryS`, the prologue and the test `|point| > 63` (`b0`), zeroing the entries and flags and the
  test `n = 0` (`b1`), the test `|point| = 0` (`b2`, then `b15`) and the arguments' stores (`b3`):
  region 0 the frame;
- `frameS`, SP the frame's base: the loop test (`b4`), the inner loop's set-up (`b7`), the
  epilogue (`b18`);
- `elemS`, `words[i]` (`b5`): region 0 the frame, region 1 the word (X29 its index);
- `wordS`, `words[0]` at `|point| = 0` (`b16`);
- `flagS`, `full[k]`'s test (`b8`): region 0 the flag;
- `pairS`, a pairing's loads (`b9`): region 0 `point[k]`, 1 `pending[k]`, 2 `full[k]`;
- `pushS`, a pending entry's store (`b13`): region 0 `pending[k]`, 1 `full[k]`, 2 the frame's
  first `48` bytes (SP);
- `regsS`, registers only (`b10`, `b11`, `b12`, `b14`, `b17`).
-/

namespace NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(1232, true)] (.ptr 0 1232)
/-- SP the frame's base. -/
def frameS : SState := init [(1232, true)] (.ptr 0 0)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- `words[i]`: the frame, the word (its address `words + (i << 3)`, `words` the frame's word at
`8`, `i` in X29). -/
def elemS : SState :=
  init [(1232, true), (8, false)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.load 0 8 8) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X29)), 1, 0)]
/-- `words[0]`, X1 its address. -/
def wordS : SState := init [(8, false)] .sp [(.X1, .ptr 0 0)]
/-- `full[k]`, X20 its address. -/
def flagS : SState := init [(1, false)] .sp [(.X20, .ptr 0 0)]
/-- `point[k]`, `pending[k]`, `full[k]`; X21 the first's address plus `8`. -/
def pairS : SState :=
  init [(16, false), (16, false), (1, false)] .sp [(.X21, .ptr 0 8), (.X28, .ptr 1 0), (.X20, .ptr 2 0)]
/-- `pending[k]`, `full[k]`, the frame's first `48` bytes (SP). -/
def pushS : SState := init [(16, false), (1, false), (48, true)] (.ptr 2 0) [(.X28, .ptr 0 0), (.X20, .ptr 1 0)]

/-- The prologue's slots. -/
def slots0 : List (Nat × XReg) :=
  [(1136, .X29), (1144, .X30), (1152, .X28), (1160, .X27), (1168, .X26), (1176, .X25),
    (1184, .X24), (1192, .X23), (1200, .X22), (1208, .X21), (1216, .X20), (1224, .X19)]

/-- The prologue's slots and the arguments' (`b3`). -/
def slots : List (Nat × XReg) := slots0 ++ [(8, .X1), (16, .X0), (32, .X2), (40, .X4)]

/-- The frame after the prologue: the slots, writes only in the frame, SP its base. -/
def FrameOk (sl : List (Nat × XReg)) (S : SState) : Bool :=
  sl.all (fun p ↦ decide (p.1 + 8 ≤ 1232) &&
      (List.range 8).all fun i ↦ findWrite 0 (p.1 + i) S.mem == some (.reg p.2, i)) &&
    S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 1232)) && S.sp == .ptr 0 0

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b1 (after b0 entryS))
sym_block run_b3 := exec b3 (after b2 (after b1 (after b0 entryS)))
sym_block run_b15 := exec b15 (after b2 (after b1 (after b0 entryS)))
sym_block run_b4 := exec b4 frameS
sym_block run_b5 := exec b5 elemS
sym_block run_b7 := exec b7 frameS
sym_block run_b8 := exec b8 flagS
sym_block run_b9 := exec b9 pairS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 pushS
sym_block run_b14 := exec b14 regsS
sym_block run_b16 := exec b16 wordS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 frameS

public theorem b0_frame : FrameOk slots0 (after b0 entryS) = true := by decide +kernel
public theorem b1_frame : FrameOk slots0 (after b1 (after b0 entryS)) = true := by decide +kernel
public theorem b2_frame : FrameOk slots0 (after b2 (after b1 (after b0 entryS))) = true := by
  decide +kernel
public theorem b15_frame :
    FrameOk slots0 (after b15 (after b2 (after b1 (after b0 entryS)))) = true := by
  decide +kernel
public theorem b3_frame : FrameOk slots (after b3 (after b2 (after b1 (after b0 entryS)))) = true := by
  decide +kernel

/-- The zeroed flags; `b3` stored `point + 8` at `24`. -/
public theorem b3_words :
    ((List.range 64).all fun k ↦
      findWrite 0 (1072 + k) (after b3 (after b2 (after b1 (after b0 entryS)))).mem ==
        some (.lit 0, k % 8)) ∧
    ((List.range 8).all fun i ↦
      findWrite 0 (24 + i) (after b3 (after b2 (after b1 (after b0 entryS)))).mem ==
        some (.bin .add .W64 (.reg .X3) (.lit 8), i)) := by
  decide +kernel

public theorem b18_restores : restores slots0 1232 (after b18 frameS) = true ∧
    restores slots 1232 (after b18 frameS) = true := by decide +kernel

public theorem kept_nil : (calleeRegs.filter fun r ↦ !inSlots slots r) = [] ∧
    (calleeRegs.filter fun r ↦ !inSlots slots0 r) = [] := by decide

public theorem keeps : keepsAll frameS (after b4 frameS) [] = true ∧
    keepsAll elemS (after b5 elemS) [] = true ∧ keepsAll frameS (after b7 frameS) [] = true ∧
    keepsAll flagS (after b8 flagS) [] = true ∧
    keepsAll pairS { after b9 pairS with mem := [] } [] = true ∧
    keepsAll regsS (after b10 regsS) [] = true ∧ keepsAll regsS (after b11 regsS) [] = true ∧
    keepsAll regsS (after b12 regsS) [] = true ∧
    keepsAll pushS { after b13 pushS with mem := [] } [] = true ∧
    keepsAll regsS (after b14 regsS) [] = true ∧ keepsAll regsS (after b17 regsS) [] = true ∧
    keepsAll wordS (after b16 wordS) [] = true := by
  decide +kernel


end NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue
