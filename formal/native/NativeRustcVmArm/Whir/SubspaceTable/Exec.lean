module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.SubspaceTable
public meta import NativeRustcVmArm.Code.Vm.SubspaceTable
public meta import NativeRustcVmArm.Whir.Common

/-!
# `subspace_table`'s blocks, run by the symbolic executor

The frame is 864 bytes below the entry's SP: from SP the spilled `out` at 8, the layer (31 words)
at 16, the table's `Buf` (`len` at 264, the pairs from 272), the saved registers from 768.
- `entryS` (region 0 the frame below SP): `b0`;
- `regsS` (no region): the counters and branches;
- `frS` (region 0 the frame from SP): the spill, the table's start, the copy, the epilogue;
- `wordS` (region 0 the word X19 points to): the output's tag (`b5`, `b22`), the inner loop's load
  and store (`b15`, `b17`);
- `vecS` (region 0 four layer words, X11 − 16): the unrolled initialization `b7`; `tailS` (region
  0 the layer word X9 points to): `b10`;
- `rootS` (region 0 the layer word at X28 + 8·X26): `b18`;
- `pushS` (region 0 the pair at X27 + 16·X25): `b20`;
- `noneS` (region 0 the frame, region 1 the output, the spilled `out`): `b23`, then `b24`.
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable

@[expose] public section

/-- The new root's address in `b18`. -/
def rAddr : Sym :=
  .bin .add .W64 (.reg .X28) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X26))
/-- The pushed pair's address in `b20`. -/
def pAddr : Sym := .bin .add .W64 (.reg .X27) (.un (.shift .LSL 4) .W64 (.reg .X25))

def entryS : SState := init [(864, true)] (.ptr 0 864)
def regsS : SState := init [] .sp
def frS : SState := init [(864, true)] (.ptr 0 0)
def wordS : SState := init [(8, false)] .sp [(.X19, .ptr 0 0)]
def vecS : SState := init [(32, false)] .sp [(.X11, .ptr 0 16)]
def tailS : SState := init [(8, false)] .sp [(.X9, .ptr 0 0)]
def rootS : SState := init [(8, false)] .sp [] [] [] [(rAddr, 0, 0)]
def pushS : SState := init [(16, false)] .sp [] [] [] [(pAddr, 0, 0)]
def noneS : SState := init [(864, true), (8, false)] (.ptr 0 0) [] [] [] [(.load 0 8 8, 1, 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(768, .X29), (776, .X30), (784, .X28), (792, .X27), (800, .X26), (808, .X25),
    (816, .X24), (824, .X23), (832, .X22), (840, .X21), (848, .X20), (856, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 wordS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 vecS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 tailS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 wordS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 wordS
sym_block run_b18 := exec b18 rootS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 pushS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 wordS
sym_block run_b23 := exec b23 noneS
sym_block run_b24 := exec b24 frS
sym_block run_b24' := exec b24 (after b23 noneS)

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 864 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 864) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b1_keeps : keepsRegs regsS (after b1 regsS) (freeRegs slots) = true ∧
    (after b1 regsS).mem = [] := by decide +kernel
public theorem b2_keeps : keepsRegs frS (after b2 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b2 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b3_keeps : keepsRegs regsS (after b3 regsS) (freeRegs slots) = true ∧
    (after b3 regsS).mem = [] := by decide +kernel
public theorem b4_keeps : keepsRegs regsS (after b4 regsS) (freeRegs slots) = true ∧
    (after b4 regsS).mem = [] := by decide +kernel
public theorem b5_keeps : keepsRegs wordS (after b5 wordS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b5 wordS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b6_keeps : keepsRegs regsS (after b6 regsS) (freeRegs slots) = true ∧
    (after b6 regsS).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs vecS (after b7 vecS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b7 vecS).mem, w.r = 0 ∧ w.off + w.n ≤ 32 := by decide +kernel
public theorem b8_keeps : keepsRegs regsS (after b8 regsS) (freeRegs slots) = true ∧
    (after b8 regsS).mem = [] := by decide +kernel
public theorem b9_keeps : keepsRegs regsS (after b9 regsS) (freeRegs slots) = true ∧
    (after b9 regsS).mem = [] := by decide +kernel
public theorem b10_keeps : keepsRegs tailS (after b10 tailS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b10 tailS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b11_keeps : keepsRegs frS (after b11 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b11 frS).mem, w.r = 0 ∧ 264 ≤ w.off ∧ w.off + w.n ≤ 768 := by decide +kernel
public theorem b12_keeps : keepsRegs frS (after b12 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b12 frS).mem, w.r = 0 ∧ 272 ≤ w.off ∧ w.off + w.n ≤ 288 := by decide +kernel
public theorem b13_keeps : keepsRegs regsS (after b13 regsS) (freeRegs slots) = true ∧
    (after b13 regsS).mem = [] := by decide +kernel
public theorem b14_keeps : keepsRegs regsS (after b14 regsS) (freeRegs slots) = true ∧
    (after b14 regsS).mem = [] := by decide +kernel
public theorem b15_keeps : keepsRegs wordS (after b15 wordS) (freeRegs slots) = true ∧
    (after b15 wordS).mem = [] := by decide +kernel
public theorem b16_keeps : keepsRegs regsS (after b16 regsS) (freeRegs slots) = true ∧
    (after b16 regsS).mem = [] := by decide +kernel
public theorem b17_keeps : keepsRegs wordS (after b17 wordS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b17 wordS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b18_keeps : keepsRegs rootS (after b18 rootS) (freeRegs slots) = true ∧
    (after b18 rootS).mem = [] := by decide +kernel
public theorem b19_keeps : keepsRegs regsS (after b19 regsS) (freeRegs slots) = true ∧
    (after b19 regsS).mem = [] := by decide +kernel
public theorem b20_keeps : keepsRegs pushS (after b20 pushS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b20 pushS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b21_keeps : keepsRegs frS (after b21 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b21 frS).mem, w.r = 0 ∧ 264 ≤ w.off ∧ w.off + w.n ≤ 272 := by decide +kernel
public theorem b22_keeps : keepsRegs wordS (after b22 wordS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b22 wordS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b24_restores : restores slots 864 (after b24 frS) = true ∧
    (after b24 frS).mem = [] := by decide +kernel
public theorem b24'_restores : restores slots 864 (after b24 (after b23 noneS)) = true ∧
    ∀ w ∈ (after b24 (after b23 noneS)).mem, w.r = 1 ∧ w.off + w.n ≤ 8 := by decide +kernel

end NativeRustcVmArm.Whir.SubspaceTable
