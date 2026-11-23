module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.PlacementsOf
public meta import NativeRustcVmArm.Code.Vm.PlacementsOf
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `placements_of`'s blocks, run by the symbolic executor

The frame: 5136 bytes below the entry's SP, `block_cols` (`0`), `block_sizes` (`1264`),
`block_offsets` (`2528`), `offsets` (`3792`), the saved registers (`5056`).

- `entryS`: region 0 the frame. `b0` saves X19-X26, X29, X30, opens the frame, calls `memset`.
- `regsS`: blocks without memory (`b1`, `b2`, `b3`, `b6`, `b8`-`b14`, `b17`-`b19`, `b23`-`b25`,
  `b28`, `b29`).
- `byteS r i`: region 0 the byte at `r + i` (`ldrb [r, i]`): `b4`, `b5`, `b26`.
- `l7S`: `b7`: region 0 `kappas[c]`, region 1 `block_cols[n]`, region 2 `block_sizes[n]`.
- `l15S`, `l16S`: the second loop's loads (`block_cols[i]`, X9 post-indexed) and its load and store
  (`block_offsets[i]`, `offsets[x10]`).
- `l17S`: `b17`: region 0 the frame (SP), `offsets[4]`.
- `b22` runs in two parts (`Exec2`).
- `l20S`: `b20`: region 0 `offsets[c]`.
- `stS`: `b21`, `b27`: the placement's 24 bytes (region 0, X10 at byte 16).
- `exitS`: `b30`: region 0 the frame.
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf NativeRustcVmArm.Arrays

@[expose] public section

/-- `[p, i, lsl #3]`'s address. -/
def idx (p i : XReg) : Sym :=
  mkBin .add .W64 (.reg p) (mkUn (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg i))
/-- `[p, i]`'s address (bytes). -/
def idxB (p i : XReg) : Sym :=
  mkBin .add .W64 (.reg p) (mkUn (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg i))

/-- The frame, its size. -/
def frameN : Nat := 5136

def entryS : SState := init [(frameN, true)] (.ptr 0 frameN)
def regsS : SState := init [] .sp
def byteS (p i : XReg) : SState := init [(1, false)] .sp [] [] [] [(idxB p i, 0, 0)]
def l7S : SState := init [(8, false), (8, false), (8, false)] .sp [] [] []
  [(idx .X19 .X8, 0, 0), (idx .X25 .X22, 1, 0), (idx .X26 .X22, 2, 0)]
def l15S : SState := init [(8, false)] .sp [(.X9, .ptr 0 0)]
def l16S : SState :=
  init [(8, false), (8, false)] .sp [(.X8, .ptr 0 0)] [] [] [(idx .X25 .X10, 1, 0)]
def l17S : SState := init [(frameN, true)] (.ptr 0 0)
def l20S : SState := init [(8, false)] .sp [] [] [] [(idx .X25 .X9, 0, 0)]
def stS : SState := init [(24, false)] .sp [(.X10, .ptr 0 16)]
def exitS : SState := init [(frameN, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(5056, .X29), (5064, .X30), (5072, .X26), (5080, .X25), (5088, .X24), (5096, .X23),
    (5104, .X22), (5112, .X21), (5120, .X20), (5128, .X19)]

/-- The callee-saved registers no slot holds. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 (byteS .X23 .X8)
sym_block run_b5 := exec b5 (byteS .X24 .X8)
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 l7S
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 l15S
sym_block run_b16 := exec b16 l16S
sym_block run_b17 := exec b17 l17S
sym_block run_b18 := exec b18 regsS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 l20S
sym_block run_b21 := exec b21 stS
sym_block run_b23 := exec b23 regsS
sym_block run_b24 := exec b24 regsS
sym_block run_b25 := exec b25 regsS
sym_block run_b26 := exec b26 (byteS .X24 .X9)
sym_block run_b27 := exec b27 stS
sym_block run_b28 := exec b28 regsS
sym_block run_b29 := exec b29 regsS
sym_block run_b30 := exec b30 exitS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ frameN ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ frameN) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

/-- The blocks without memory keep the registers no slot holds and write nothing. -/
public theorem regs_keep : ∀ b ∈ [b1, b2, b3, b6, b8, b9, b10, b11, b12, b13, b14, b18, b19, b23,
    b24, b25, b28, b29], keepsAll regsS (after b regsS) keptRegs = true := by
  decide +kernel

public theorem b4_keep : keepsAll (byteS .X23 .X8) (after b4 (byteS .X23 .X8)) keptRegs = true := by
  decide +kernel
public theorem b5_keep : keepsAll (byteS .X24 .X8) (after b5 (byteS .X24 .X8)) keptRegs = true := by
  decide +kernel
public theorem b26_keep :
    keepsAll (byteS .X24 .X9) (after b26 (byteS .X24 .X9)) keptRegs = true := by
  decide +kernel
public theorem b15_keep : keepsAll l15S (after b15 l15S) keptRegs = true := by decide +kernel
public theorem b17_keep : keepsAll l17S (after b17 l17S) keptRegs = true := by decide +kernel
public theorem b20_keep : keepsAll l20S (after b20 l20S) keptRegs = true := by decide +kernel

public theorem b7_facts : keepsAll l7S { after b7 l7S with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b7 l7S).mem, (w.r = 1 ∨ w.r = 2) ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b7 l7S).mem = some (.reg .X8, i)) ∧
    (∀ i < 8, findWrite 2 (0 + i) (after b7 l7S).mem = some (.load 0 0 8, i)) := by
  decide +kernel

public theorem b16_facts : keepsAll l16S { after b16 l16S with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b16 l16S).mem, w.r = 1 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b16 l16S).mem = some (.load 0 0 8, i)) := by
  decide +kernel

public theorem b21_facts : keepsAll stS { after b21 stS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b21 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b21 stS).mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b21 stS).mem = some (.reg .X11, i)) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b21 stS).mem = some (.reg .X12, i)) := by
  decide +kernel

public theorem b27_facts : keepsAll stS { after b27 stS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b27 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b27 stS).mem = some (.lit 0, i)) := by
  decide +kernel

public theorem b30_restores : restores slots frameN (after b30 exitS) = true ∧
    (after b30 exitS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Layout.PlacementsOf
