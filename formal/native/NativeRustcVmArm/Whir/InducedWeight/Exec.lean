module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.InducedWeight
public meta import NativeRustcVmArm.Code.Vm.InducedWeight
public meta import NativeRustcVmArm.Whir.Common

/-!
# `induced_weight`'s blocks, run by the symbolic executor

The frame is 1200 bytes below the entry's SP: from SP the spills (`out` at 16, the turns' bound
at 56, the table's slice at 40, 48, the queries at 64, the weights and the point's count at 72,
80, the point's and `what`'s pointers at 24, 32), the table's copy (`len` at 88, items from 96),
the `Option` buffer of `subspace_table` / the `Buf` of `subspace_at_table` at 592, the saved
registers from 1104.
- `entryS` (region 0 the frame below SP): `b0`;
- `frS` (region 0 the frame from SP): the spills' blocks;
- `qaS` (region 0 the frame, region 1 weight `j`), `qbS` (region 1 query `j`): `b6`'s halves;
- `pS` (region 0 the point's element X23 − 8 points to, region 1 `what`'s word X24 points to):
  `b9`;
- `regsS`: `b10` to `b14`;
- `outS` (region 0 the frame, region 1 the `Option<EW>` at the spilled `out`): `b15`, `b16`;
  `noneS` the same with X20 the output: `b16` from `b1`.
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight

@[expose] public section

/-- Weight `j`'s address. -/
def wAddr : Sym := .bin .add .W64 (.load 0 72 8) (.un (.shift .LSL 4) .W64 (.reg .X22))
/-- Query `j`'s address. -/
def qAddr : Sym :=
  .bin .add .W64 (.load 0 64 8) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X22))

def entryS : SState := init [(1200, true)] (.ptr 0 1200)
def frS : SState := init [(1200, true)] (.ptr 0 0)
def regsS : SState := init [] .sp
/-- `b6`'s loads of weight `j` (the weights and the queries may overlap: two environments). -/
def b6a : List Directive := b6.take 6
/-- `b6`'s load of query `j` and the call. -/
def b6b : List Directive := b6.drop 6
def qaS : SState := init [(1200, true), (16, false)] (.ptr 0 0) [] [] [] [(wAddr, 1, 0)]
def qbS : SState := init [(1200, true), (8, false)] (.ptr 0 0) [] [] [] [(qAddr, 1, 0)]
def pS : SState := init [(16, false), (8, false)] .sp [(.X23, .ptr 0 8), (.X24, .ptr 1 0)]
def outS : SState := init [(1200, true), (24, false)] (.ptr 0 0) [] [] [] [(.load 0 16 8, 1, 0)]
def noneS : SState := init [(1200, true), (24, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(1104, .X29), (1112, .X30), (1120, .X28), (1128, .X27), (1136, .X26), (1144, .X25),
    (1152, .X24), (1160, .X23), (1168, .X22), (1176, .X21), (1184, .X20), (1192, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6a := exec b6a qaS
sym_block run_b6b := exec b6b qbS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 pS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 outS
sym_block run_b16 := exec b16 (after b15 outS)
sym_block run_b16' := exec b16 noneS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 1200 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1200) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b10_keeps : keepsRegs regsS (after b10 regsS) (freeRegs slots) = true ∧
    (after b10 regsS).mem = [] := by decide +kernel
public theorem b11_keeps : keepsRegs regsS (after b11 regsS) (freeRegs slots) = true ∧
    (after b11 regsS).mem = [] := by decide +kernel
public theorem b12_keeps : keepsRegs regsS (after b12 regsS) (freeRegs slots) = true ∧
    (after b12 regsS).mem = [] := by decide +kernel
public theorem b13_keeps : keepsRegs regsS (after b13 regsS) (freeRegs slots) = true ∧
    (after b13 regsS).mem = [] := by decide +kernel
public theorem b14_keeps : keepsRegs regsS (after b14 regsS) (freeRegs slots) = true ∧
    (after b14 regsS).mem = [] := by decide +kernel
public theorem b1_keeps : keepsRegs frS (after b1 frS) (freeRegs slots) = true ∧
    (after b1 frS).mem = [] := by decide +kernel
public theorem b5_keeps : keepsRegs frS (after b5 frS) (freeRegs slots) = true ∧
    (after b5 frS).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs frS (after b7 frS) (freeRegs slots) = true ∧
    (after b7 frS).mem = [] := by decide +kernel
public theorem b8_keeps : keepsRegs frS (after b8 frS) (freeRegs slots) = true ∧
    (after b8 frS).mem = [] := by decide +kernel
public theorem b2_keeps : keepsRegs frS (after b2 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b2 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 96 := by decide +kernel
public theorem b3_keeps : keepsRegs frS (after b3 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b3 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 96 := by decide +kernel
public theorem b4_keeps : keepsRegs frS (after b4 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b4 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 96 := by decide +kernel
public theorem b6a_keeps : keepsRegs qaS (after b6a qaS) (freeRegs slots) = true ∧
    (after b6a qaS).mem = [] := by decide +kernel
public theorem b6b_keeps : keepsRegs qbS (after b6b qbS) (freeRegs slots) = true ∧
    (after b6b qbS).mem = [] := by decide +kernel
public theorem b6_split : b6a ++ b6b = b6 := List.take_append_drop _ _
public theorem b6a_length : b6a.length = 6 := rfl
public theorem b9_keeps : keepsRegs pS (after b9 pS) (freeRegs slots) = true ∧
    (after b9 pS).mem = [] := by decide +kernel
public theorem b16_restores : restores slots 1200 (after b16 (after b15 outS)) = true ∧
    ∀ w ∈ (after b16 (after b15 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by decide +kernel
public theorem b16'_restores : restores slots 1200 (after b16 noneS) = true ∧
    ∀ w ∈ (after b16 noneS).mem, w.r = 1 ∧ w.off + w.n ≤ 24 := by decide +kernel

end NativeRustcVmArm.Whir.InducedWeight
