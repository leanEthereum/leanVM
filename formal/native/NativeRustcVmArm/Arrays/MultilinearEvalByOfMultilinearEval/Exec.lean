module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval
public meta import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure): its blocks, run by the symbolic executor

The frame (`1232` bytes below the entry's SP, `fb` its base): `n`'s and the slices' words at
`fb + 8` (`mle`), `16` (`n`), `24` (`point + 8`), `32` (`|mle|`), `40` (`|point|`); the pending
entries at `fb + 48 + 16 k`, the `full` flags at `fb + 1072 + k` (`k < 64`); the saved registers
from `fb + 1136`.

- `entryS`, the prologue (`b0`, zeroing the entries and flags), the tests `n = 0` (`b0`),
  `|point| = 0` (`b1`, then `b14`) and the stores of the arguments (`b2`): region 0 the frame;
- `frameS`, SP the frame's base: the loop test (`b3`), the inner loop's set-up (`b6`), the
  epilogue (`b17`);
- `elemS`, `mle[i]` (`b4`): region 0 the frame, region 1 the element (X29 its index);
- `ldS .X1 0`, `mle[0]` at `|point| = 0` (`b15`);
- `flagS`, `full[k]`'s test (`b7`): region 0 the flag;
- `pairS`, a pairing's loads (`b8`): region 0 `point[k]`, 1 `pending[k]`, 2 `full[k]`;
- `pushS`, a pending entry's store (`b12`): region 0 `pending[k]`, 1 `full[k]`, 2 the frame's
  first `48` bytes (SP);
- `regsS`, registers only (`b9`, `b10`, `b11`, `b13`, `b16`).
-/

namespace NativeRustcVmArm.Arrays.MleOfMultilinearEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(1232, true)] (.ptr 0 1232)
/-- SP the frame's base. -/
def frameS : SState := init [(1232, true)] (.ptr 0 0)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- `mle[i]`: the frame, the element (its address `mle + (i << 4)`, `mle` the frame's word at
`8`, `i` in X29). -/
def elemS : SState :=
  init [(1232, true), (16, false)] (.ptr 0 0) [] [] []
    [(.bin .add .W64 (.load 0 8 8) (.un (.shift .LSL 4) .W64 (.reg .X29)), 1, 0)]
/-- `full[k]`, X20 its address. -/
def flagS : SState := init [(1, false)] .sp [(.X20, .ptr 0 0)]
/-- `point[k]`, `pending[k]`, `full[k]`; X19 the first's address plus `8`. -/
def pairS : SState :=
  init [(16, false), (16, false), (1, false)] .sp [(.X19, .ptr 0 8), (.X21, .ptr 1 0), (.X20, .ptr 2 0)]
/-- `pending[k]`, `full[k]`, the frame's first `48` bytes (SP). -/
def pushS : SState := init [(16, false), (1, false), (48, true)] (.ptr 2 0) [(.X21, .ptr 0 0), (.X20, .ptr 1 0)]

/-- The prologue's slots. -/
def slots0 : List (Nat × XReg) :=
  [(1136, .X29), (1144, .X30), (1152, .X28), (1160, .X27), (1168, .X26), (1176, .X25),
    (1184, .X24), (1192, .X23), (1200, .X22), (1208, .X21), (1216, .X20), (1224, .X19)]

/-- The prologue's slots and the arguments' (`b2`). -/
def slots : List (Nat × XReg) := slots0 ++ [(8, .X1), (16, .X0), (32, .X2), (40, .X4)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b1 (after b0 entryS))
sym_block run_b14 := exec b14 (after b1 (after b0 entryS))
sym_block run_b3 := exec b3 frameS
sym_block run_b4 := exec b4 elemS
sym_block run_b6 := exec b6 frameS
sym_block run_b7 := exec b7 flagS
sym_block run_b8 := exec b8 pairS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 pushS
sym_block run_b13 := exec b13 regsS
sym_block run_b15 := exec b15 (ldS .X1 0)
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 frameS

/-- The frame after the prologue: the slots, writes only in the frame, SP its base. -/
@[expose] public def FrameOk (sl : List (Nat × XReg)) (S : SState) : Bool :=
  sl.all (fun p ↦ decide (p.1 + 8 ≤ 1232) &&
      (List.range 8).all fun i ↦ findWrite 0 (p.1 + i) S.mem == some (.reg p.2, i)) &&
    S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 1232)) && S.sp == .ptr 0 0

public theorem b0_frame : FrameOk slots0 (after b0 entryS) = true := by decide +kernel
public theorem b1_frame : FrameOk slots0 (after b1 (after b0 entryS)) = true := by decide +kernel
public theorem b14_frame : FrameOk slots0 (after b14 (after b1 (after b0 entryS))) = true := by
  decide +kernel
public theorem b2_frame : FrameOk slots (after b2 (after b1 (after b0 entryS))) = true := by
  decide +kernel

/-- The prologue zeroed the flags; `b2` stored `point + 8` at `24`. -/
public theorem b2_words :
    ((List.range 64).all fun k ↦
      findWrite 0 (1072 + k) (after b2 (after b1 (after b0 entryS))).mem == some (.lit 0, k % 8)) ∧
    ((List.range 8).all fun i ↦ findWrite 0 (24 + i) (after b2 (after b1 (after b0 entryS))).mem ==
      some (.bin .add .W64 (.reg .X3) (.lit 8), i)) := by
  decide +kernel

public theorem b17_restores : restores slots0 1232 (after b17 frameS) = true ∧
    restores slots 1232 (after b17 frameS) = true := by decide +kernel

public theorem kept_nil : (calleeRegs.filter fun r ↦ !inSlots slots r) = [] ∧
    (calleeRegs.filter fun r ↦ !inSlots slots0 r) = [] := by decide

public theorem keeps : keepsAll frameS (after b3 frameS) [] = true ∧
    keepsAll elemS (after b4 elemS) [] = true ∧ keepsAll frameS (after b6 frameS) [] = true ∧
    keepsAll flagS (after b7 flagS) [] = true ∧
    keepsAll pairS { after b8 pairS with mem := [] } [] = true ∧
    keepsAll regsS (after b9 regsS) [] = true ∧ keepsAll regsS (after b10 regsS) [] = true ∧
    keepsAll regsS (after b11 regsS) [] = true ∧
    keepsAll pushS { after b12 pushS with mem := [] } [] = true ∧
    keepsAll regsS (after b13 regsS) [] = true ∧ keepsAll regsS (after b16 regsS) [] = true ∧
    keepsAll (ldS .X1 0) (after b15 (ldS .X1 0)) [] = true := by
  decide +kernel

end NativeRustcVmArm.Arrays.MleOfMultilinearEval
