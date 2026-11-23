module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.EqKernel
public meta import NativeRustcVmArm.Code.Vm.EqKernel
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `eq_kernel`'s blocks, run by the symbolic executor

- `regsS`, registers only: the size test (`b0`) and `None` (`b1`) when `out` is short, the round's
  tests (`b5`, `b6`), `b .LEqKernel_4` (`b10`);
- `entryS`, at the entry when `out` holds the kernel: region 0 the 112-byte frame below SP, 1
  `out[0]`, X2 its address: the size test (`b0`), the prologue, `out[0] = 1` and the `|point| = 0`
  test (`b2`), the size and `point`'s end stored at `[sp]`, `[sp, #8]` (`b3`);
- `frameS`, SP the frame's base: `b4` (loads `[sp, #8]`), `b12` (loads `[sp]`), `b13` (the
  epilogue);
- `ldS .X22 0`, a round's set-up (`b7`): region 0 `point[i]`;
- `loS`, a pair's product (`b8`): region 0 `out[j]`, X28 its address plus `8`;
- `pairS`, a pair's stores (`b9`): region 0 `out[j]`, 1 `out[n + j]`; X28, X21 their addresses
  plus `8`.
-/

namespace NativeRustcVmArm.Arrays.EqKernel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqKernel

@[expose] public section

/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the entry: the frame, `out[0]`, X2 its address. -/
def entryS : SState := init [(112, true), (16, false)] (.ptr 0 112) [(.X2, .ptr 1 0)]
/-- SP the frame's base. -/
def frameS : SState := init [(112, true)] (.ptr 0 0)
/-- `out[j]`, X28 its address plus `8`. -/
def loS : SState := init [(16, false)] .sp [(.X28, .ptr 0 8)]
/-- `out[j]` and `out[n + j]`, X28 and X21 their addresses plus `8`. -/
def pairS : SState := init [(16, false), (16, false)] .sp [(.X28, .ptr 0 8), (.X21, .ptr 1 8)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(16, .X29), (24, .X30), (32, .X28), (40, .X27), (48, .X26), (56, .X25), (64, .X24),
    (72, .X23), (80, .X22), (88, .X21), (96, .X20), (104, .X19)]

/-- The registers no block but the prologue and the epilogue may change: none. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

/-- The size `2^|point|`. -/
def sizeSym : Sym := .bin .lslv .W64 (.lit 1) (.reg .X1)
/-- `point`'s end. -/
def endSym : Sym := .bin .add .W64 (.reg .X0) (.un (.shift .LSL 4) .W64 (.reg .X1))

/-- After the prologue. -/
abbrev S2 : SState := after b2 (after b0 entryS)

/-- After the prologue: SP the frame's base, X0 `1`, the slots filled, `out[0] = 1`, writes only
in the frame and `out[0]`. -/
abbrev EntryOk (S : SState) : Prop :=
  S.sp = .ptr 0 0 ∧ S.reg .X0 = some (.lit 1) ∧
    (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i)) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → S.reg r = some (.reg r)) ∧
    (∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ 112) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    (∀ i < 8, findWrite 1 (0 + i) S.mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 1 (8 + i) S.mem = some (.lit 0, i))

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 (after b0 regsS)
sym_block run_b0e := exec b0 entryS
sym_block run_b2 := exec b2 (after b0 entryS)
sym_block run_b3 := exec b3 S2
sym_block run_b4 := exec b4 frameS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 (ldS .X22 0)
sym_block run_b8 := exec b8 loS
sym_block run_b9 := exec b9 pairS
sym_block run_b10 := exec b10 regsS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 frameS

public theorem b1_keeps : keeps regsS (after b1 (after b0 regsS)) = true ∧
    (after b1 (after b0 regsS)).mem = [] ∧ (after b1 (after b0 regsS)).reg .X0 = some (.lit 0) := by
  decide +kernel
public theorem S2_ok : EntryOk (after b2 (after b0 entryS)) ∧
    (after b2 (after b0 entryS)).reg .X8 = some sizeSym := by
  decide +kernel
public theorem S3_ok : EntryOk (after b3 S2) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b3 S2).mem = some (sizeSym, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b3 S2).mem = some (endSym, i)) ∧
    (after b3 S2).reg .X20 = some (.reg .X3) ∧ (after b3 S2).reg .X22 = some (.reg .X0) ∧
    (after b3 S2).reg .X27 = some (.ptr 1 8) ∧ (after b3 S2).reg .X29 = some (.lit 1) := by
  decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) keptRegs = true := by decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) keptRegs = true := by decide +kernel
public theorem b10_keeps : keepsAll regsS (after b10 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll frameS (after b4 frameS) keptRegs = true := by decide +kernel
public theorem b12_keeps : keepsAll frameS (after b12 frameS) keptRegs = true := by decide +kernel
public theorem b7_keeps : keepsAll (ldS .X22 0) (after b7 (ldS .X22 0)) keptRegs = true ∧
    ([XReg.X19, .X20, .X22, .X27, .X29].all fun q ↦ ((ldS .X22 0).reg q).isSome &&
      (after b7 (ldS .X22 0)).reg q == (ldS .X22 0).reg q) = true := by
  decide +kernel
public theorem b8_keeps : keepsAll loS (after b8 loS) keptRegs = true := by decide +kernel
public theorem b9_facts : (after b9 pairS).sp = .sp ∧
    (∀ w ∈ (after b9 pairS).mem, (w.r = 0 ∧ w.off + w.n ≤ 16) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b9 pairS).mem =
      some (.bin .eor .W64 (.reg .X25) (.reg .X0), i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b9 pairS).mem =
      some (.bin .eor .W64 (.reg .X26) (.reg .X1), i)) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b9 pairS).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b9 pairS).mem = some (.reg .X1, i)) := by
  decide +kernel
public theorem b13_restores : restores slots 112 (after b13 frameS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.EqKernel
