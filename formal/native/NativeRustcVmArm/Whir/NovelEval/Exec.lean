module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.NovelEval
public meta import NativeRustcVmArm.Code.Vm.NovelEval
public meta import NativeRustcVmArm.Whir.Common

/-!
# `novel_eval`'s blocks, run by the symbolic executor

The frame is 1120 bytes below the entry's SP: the basis (128 words) from SP, the saved registers
from SP + 1024.
- `entryS` (region 0 the frame below SP): `b0`, the prologue and `memset`;
- `regsS` (no region): `b1`, `b3`, `b4`, `b8`, `b9`, `b10`, `b13` to `b16`;
- `frameS` (region 0 the frame from SP): `b2` (`basis[0] = 1`);
- `ldS`: `b5` loads the value X22 points to; `bS`: `b6` loads the basis word X26 points to;
- `stS`: `b7` stores at `X26 + 8·X24` (an alias);
- `sumS` (region 0 the coefficient X26 − 8 points to, region 1 the basis word X27 points to):
  `b11`;
- `outS` (region 0 the frame from SP, region 1 the `Option<EW>` X19 points to): `b17`, `b18`.
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NovelEval

@[expose] public section

/-- The address `b7` stores at. -/
def stAddr : Sym :=
  .bin .add .W64 (.reg .X26) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X24))

def entryS : SState := init [(1120, true)] (.ptr 0 1120)
def regsS : SState := init [] .sp
def frameS : SState := init [(1120, true)] (.ptr 0 0)
def ldS : SState := init [(8, false)] .sp [(.X22, .ptr 0 0)]
def bS : SState := init [(8, false)] .sp [(.X26, .ptr 0 0)]
def stS : SState := init [(8, false)] .sp [] [] [] [(stAddr, 0, 0)]
def sumS : SState := init [(16, false), (8, false)] .sp [(.X26, .ptr 0 8), (.X27, .ptr 1 0)]
def outS : SState := init [(1120, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(1024, .X29), (1040, .X30), (1048, .X27), (1056, .X26), (1064, .X25), (1072, .X24),
    (1080, .X23), (1088, .X22), (1096, .X21), (1104, .X20), (1112, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 frameS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 ldS
sym_block run_b6 := exec b6 bS
sym_block run_b7 := exec b7 stS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 sumS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 outS
sym_block run_b18 := exec b18 (after b17 outS)
sym_block run_b18' := exec b18 outS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 1120 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1120) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

/-- The blocks without writes keep the free registers. -/
public theorem regs_keeps : ∀ ds ∈ [b1, b3, b4, b8, b9, b10, b12, b13, b14, b15, b16],
    keepsRegs regsS (after ds regsS) (freeRegs slots) = true ∧ (after ds regsS).mem = [] := by
  decide +kernel

public theorem b2_keeps : keepsRegs frameS (after b2 frameS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b2 frameS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b5_keeps : keepsRegs ldS (after b5 ldS) (freeRegs slots) = true ∧
    (after b5 ldS).mem = [] := by decide +kernel
public theorem b6_keeps : keepsRegs bS (after b6 bS) (freeRegs slots) = true ∧
    (after b6 bS).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs stS (after b7 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b7 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b11_keeps : keepsRegs sumS (after b11 sumS) (freeRegs slots) = true ∧
    (after b11 sumS).mem = [] := by decide +kernel
public theorem b18_restores : restores slots 1120 (after b18 (after b17 outS)) = true ∧
    ∀ w ∈ (after b18 (after b17 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by decide +kernel
public theorem b18'_restores : restores slots 1120 (after b18 outS) = true ∧
    ∀ w ∈ (after b18 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by decide +kernel

end NativeRustcVmArm.Whir.NovelEval
