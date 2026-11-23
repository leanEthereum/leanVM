module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.FoldRow
public meta import NativeRustcVmArm.Code.Vm.FoldRow
public meta import NativeRustcVmArm.Whir.Common

/-!
# `fold_row`'s blocks, run by the symbolic executor

rustc unrolled the rounds into six copies (round `r` at blocks `9r - 8` to `9r`, round 6 at
`b46` to `b54`, `b55` the end). The frame is 128 bytes below the entry's SP: `x` at SP, `n` at
SP + 8, the rounds' count at SP + 16, `values` at SP + 24, the saved registers from SP + 32.
- `entryS` (region 0 the frame below SP): `b0`;
- `regsS` (no region): the counters and branches;
- `frS` (region 0 the frame from SP): the spills;
- `hd1S` (region 0 the first round, X3): `b1`; `hdS r` (region 0 the frame, region 1 the first
  `r` rounds, X22): the other rounds' heads;
- `ldS` (region 0 the lanes `2i`, `2i + 1`, X23 − 16): the loads; `stS` (region 0 lane `i`,
  X20 − 8): the store; `ldS6`, `stS6` round 6's (X28, X27);
- `exitS` (region 0 the frame, region 1 lane `0`, the spilled `values`): `b55`.
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRow

@[expose] public section

def entryS : SState := init [(128, true)] (.ptr 0 128)
def regsS : SState := init [] .sp
def frS : SState := init [(128, true)] (.ptr 0 0)
def hd1S : SState := init [(32, false)] .sp [(.X3, .ptr 0 0)]
def hdS (r : Nat) : SState := init [(128, true), (32 * r, false)] (.ptr 0 0) [(.X22, .ptr 1 0)]
def ldS : SState := init [(32, false)] .sp [(.X23, .ptr 0 16)]
def stS : SState := init [(16, false)] .sp [(.X20, .ptr 0 8)]
def ldS6 : SState := init [(32, false)] .sp [(.X28, .ptr 0 16)]
def stS6 : SState := init [(16, false)] .sp [(.X27, .ptr 0 8)]
def exitS : SState := init [(128, true), (16, false)] (.ptr 0 0) [] [] [] [(.load 0 24 8, 1, 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(32, .X29), (40, .X30), (48, .X28), (56, .X27), (64, .X26), (72, .X25), (80, .X24),
    (88, .X23), (96, .X22), (104, .X21), (112, .X20), (120, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 hd1S
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 ldS
sym_block run_b8 := exec b8 stS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 (hdS 2)
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 ldS
sym_block run_b17 := exec b17 stS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 (hdS 3)
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 regsS
sym_block run_b24 := exec b24 regsS
sym_block run_b25 := exec b25 ldS
sym_block run_b26 := exec b26 stS
sym_block run_b27 := exec b27 frS
sym_block run_b28 := exec b28 (hdS 4)
sym_block run_b29 := exec b29 regsS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 regsS
sym_block run_b33 := exec b33 regsS
sym_block run_b34 := exec b34 ldS
sym_block run_b35 := exec b35 stS
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 (hdS 5)
sym_block run_b38 := exec b38 regsS
sym_block run_b39 := exec b39 frS
sym_block run_b40 := exec b40 frS
sym_block run_b41 := exec b41 regsS
sym_block run_b42 := exec b42 regsS
sym_block run_b43 := exec b43 ldS
sym_block run_b44 := exec b44 stS
sym_block run_b45 := exec b45 frS
sym_block run_b46 := exec b46 (hdS 6)
sym_block run_b47 := exec b47 regsS
sym_block run_b48 := exec b48 frS
sym_block run_b49 := exec b49 frS
sym_block run_b50 := exec b50 regsS
sym_block run_b51 := exec b51 regsS
sym_block run_b52 := exec b52 ldS6
sym_block run_b53 := exec b53 stS6
sym_block run_b54 := exec b54 regsS
sym_block run_b55 := exec b55 exitS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 128 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 128) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel
public theorem b5_keeps : keepsRegs regsS (after b5 regsS) (freeRegs slots) = true ∧
    (after b5 regsS).mem = [] := by decide +kernel
public theorem b6_keeps : keepsRegs regsS (after b6 regsS) (freeRegs slots) = true ∧
    (after b6 regsS).mem = [] := by decide +kernel
public theorem b11_keeps : keepsRegs regsS (after b11 regsS) (freeRegs slots) = true ∧
    (after b11 regsS).mem = [] := by decide +kernel
public theorem b14_keeps : keepsRegs regsS (after b14 regsS) (freeRegs slots) = true ∧
    (after b14 regsS).mem = [] := by decide +kernel
public theorem b15_keeps : keepsRegs regsS (after b15 regsS) (freeRegs slots) = true ∧
    (after b15 regsS).mem = [] := by decide +kernel
public theorem b20_keeps : keepsRegs regsS (after b20 regsS) (freeRegs slots) = true ∧
    (after b20 regsS).mem = [] := by decide +kernel
public theorem b23_keeps : keepsRegs regsS (after b23 regsS) (freeRegs slots) = true ∧
    (after b23 regsS).mem = [] := by decide +kernel
public theorem b24_keeps : keepsRegs regsS (after b24 regsS) (freeRegs slots) = true ∧
    (after b24 regsS).mem = [] := by decide +kernel
public theorem b29_keeps : keepsRegs regsS (after b29 regsS) (freeRegs slots) = true ∧
    (after b29 regsS).mem = [] := by decide +kernel
public theorem b32_keeps : keepsRegs regsS (after b32 regsS) (freeRegs slots) = true ∧
    (after b32 regsS).mem = [] := by decide +kernel
public theorem b33_keeps : keepsRegs regsS (after b33 regsS) (freeRegs slots) = true ∧
    (after b33 regsS).mem = [] := by decide +kernel
public theorem b38_keeps : keepsRegs regsS (after b38 regsS) (freeRegs slots) = true ∧
    (after b38 regsS).mem = [] := by decide +kernel
public theorem b41_keeps : keepsRegs regsS (after b41 regsS) (freeRegs slots) = true ∧
    (after b41 regsS).mem = [] := by decide +kernel
public theorem b42_keeps : keepsRegs regsS (after b42 regsS) (freeRegs slots) = true ∧
    (after b42 regsS).mem = [] := by decide +kernel
public theorem b47_keeps : keepsRegs regsS (after b47 regsS) (freeRegs slots) = true ∧
    (after b47 regsS).mem = [] := by decide +kernel
public theorem b50_keeps : keepsRegs regsS (after b50 regsS) (freeRegs slots) = true ∧
    (after b50 regsS).mem = [] := by decide +kernel
public theorem b51_keeps : keepsRegs regsS (after b51 regsS) (freeRegs slots) = true ∧
    (after b51 regsS).mem = [] := by decide +kernel
public theorem b54_keeps : keepsRegs regsS (after b54 regsS) (freeRegs slots) = true ∧
    (after b54 regsS).mem = [] := by decide +kernel
public theorem b4_keeps : keepsRegs frS (after b4 frS) (freeRegs slots) = true ∧
    (after b4 frS).mem = [] := by decide +kernel
public theorem b9_keeps : keepsRegs frS (after b9 frS) (freeRegs slots) = true ∧
    (after b9 frS).mem = [] := by decide +kernel
public theorem b12_keeps : keepsRegs frS (after b12 frS) (freeRegs slots) = true ∧
    (after b12 frS).mem = [] := by decide +kernel
public theorem b13_keeps : keepsRegs frS (after b13 frS) (freeRegs slots) = true ∧
    (after b13 frS).mem = [] := by decide +kernel
public theorem b18_keeps : keepsRegs frS (after b18 frS) (freeRegs slots) = true ∧
    (after b18 frS).mem = [] := by decide +kernel
public theorem b21_keeps : keepsRegs frS (after b21 frS) (freeRegs slots) = true ∧
    (after b21 frS).mem = [] := by decide +kernel
public theorem b22_keeps : keepsRegs frS (after b22 frS) (freeRegs slots) = true ∧
    (after b22 frS).mem = [] := by decide +kernel
public theorem b27_keeps : keepsRegs frS (after b27 frS) (freeRegs slots) = true ∧
    (after b27 frS).mem = [] := by decide +kernel
public theorem b30_keeps : keepsRegs frS (after b30 frS) (freeRegs slots) = true ∧
    (after b30 frS).mem = [] := by decide +kernel
public theorem b31_keeps : keepsRegs frS (after b31 frS) (freeRegs slots) = true ∧
    (after b31 frS).mem = [] := by decide +kernel
public theorem b36_keeps : keepsRegs frS (after b36 frS) (freeRegs slots) = true ∧
    (after b36 frS).mem = [] := by decide +kernel
public theorem b39_keeps : keepsRegs frS (after b39 frS) (freeRegs slots) = true ∧
    (after b39 frS).mem = [] := by decide +kernel
public theorem b40_keeps : keepsRegs frS (after b40 frS) (freeRegs slots) = true ∧
    (after b40 frS).mem = [] := by decide +kernel
public theorem b45_keeps : keepsRegs frS (after b45 frS) (freeRegs slots) = true ∧
    (after b45 frS).mem = [] := by decide +kernel
public theorem b48_keeps : keepsRegs frS (after b48 frS) (freeRegs slots) = true ∧
    (after b48 frS).mem = [] := by decide +kernel
public theorem b49_keeps : keepsRegs frS (after b49 frS) (freeRegs slots) = true ∧
    (after b49 frS).mem = [] := by decide +kernel
public theorem b1_keeps : keepsRegs hd1S (after b1 hd1S) (freeRegs slots) = true ∧
    (after b1 hd1S).mem = [] := by decide +kernel
public theorem b10_keeps : keepsRegs (hdS 2) (after b10 (hdS 2)) (freeRegs slots) = true ∧
    (after b10 (hdS 2)).mem = [] := by decide +kernel
public theorem b19_keeps : keepsRegs (hdS 3) (after b19 (hdS 3)) (freeRegs slots) = true ∧
    (after b19 (hdS 3)).mem = [] := by decide +kernel
public theorem b28_keeps : keepsRegs (hdS 4) (after b28 (hdS 4)) (freeRegs slots) = true ∧
    (after b28 (hdS 4)).mem = [] := by decide +kernel
public theorem b37_keeps : keepsRegs (hdS 5) (after b37 (hdS 5)) (freeRegs slots) = true ∧
    (after b37 (hdS 5)).mem = [] := by decide +kernel
public theorem b46_keeps : keepsRegs (hdS 6) (after b46 (hdS 6)) (freeRegs slots) = true ∧
    (after b46 (hdS 6)).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs ldS (after b7 ldS) (freeRegs slots) = true ∧
    (after b7 ldS).mem = [] := by decide +kernel
public theorem b16_keeps : keepsRegs ldS (after b16 ldS) (freeRegs slots) = true ∧
    (after b16 ldS).mem = [] := by decide +kernel
public theorem b25_keeps : keepsRegs ldS (after b25 ldS) (freeRegs slots) = true ∧
    (after b25 ldS).mem = [] := by decide +kernel
public theorem b34_keeps : keepsRegs ldS (after b34 ldS) (freeRegs slots) = true ∧
    (after b34 ldS).mem = [] := by decide +kernel
public theorem b43_keeps : keepsRegs ldS (after b43 ldS) (freeRegs slots) = true ∧
    (after b43 ldS).mem = [] := by decide +kernel
public theorem b52_keeps : keepsRegs ldS6 (after b52 ldS6) (freeRegs slots) = true ∧
    (after b52 ldS6).mem = [] := by decide +kernel
public theorem b2_keeps : keepsRegs frS (after b2 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b2 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b3_keeps : keepsRegs frS (after b3 frS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b3 frS).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b8_keeps : keepsRegs stS (after b8 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b8 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b17_keeps : keepsRegs stS (after b17 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b17 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b26_keeps : keepsRegs stS (after b26 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b26 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b35_keeps : keepsRegs stS (after b35 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b35 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b44_keeps : keepsRegs stS (after b44 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b44 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b53_keeps : keepsRegs stS6 (after b53 stS6) (freeRegs slots) = true ∧
    ∀ w ∈ (after b53 stS6).mem, w.r = 0 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b55_restores : restores slots 128 (after b55 exitS) = true ∧
    (after b55 exitS).mem = [] := by decide +kernel

end NativeRustcVmArm.Whir.FoldRow
