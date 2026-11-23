module

public import NativeRustcVmArm.Top.Frame
public import NativeRustcVmArm.Code.Vm.Seed
public meta import NativeRustcVmArm.Code.Vm.Seed

/-!
# `seed`'s blocks, run by the symbolic executor

`seed` (`sub sp, sp, #240`; the IV at the frame's byte 8, the state from there): the states its
proof starts blocks from and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`: the prologue, ending in `bl keccak256_words`): region 0 the
  240-byte frame below SP;
- `noneS`, after a call that is followed by register moves only (`b1`, ending in `bl memset`;
  `b3`, ending in `bl memcpy`): no region;
- `pubS`, after `memset` (`b2`: the public input copied to the frame's bytes 40 to 71, ending in
  `bl keccak_f`): region 0 the frame (SP), region 1 the public input (X19);
- `exitS`, after `memcpy` (`b4`, the epilogue): region 0 the frame (SP).
-/

namespace NativeRustcVmArm.Top.Seed

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Seed

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(240, true)] (.ptr 0 240)

/-- No region. -/
def noneS : SState := init []

/-- After `memset`: the frame (region 0) and the public input (region 1, X19). -/
def pubS : SState := init [(240, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- After `memcpy`: the frame (region 0). -/
def exitS : SState := init [(240, true)] (.ptr 0 0)

/-- The prologue's slots in the frame. -/
def slots : List (Nat × XReg) := [(208, .X30), (216, .X21), (224, .X20), (232, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 noneS
sym_block run_b2 := exec b2 pubS
sym_block run_b3 := exec b3 noneS
sym_block run_b4 := exec b4 exitS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 208 ≤ w.off ∧ w.off + w.n ≤ 240 := by
  decide +kernel

public theorem b2_words : ∀ q < 4, ∀ i < 8, findWrite 0 ((40 + 8 * q) + i) (after b2 pubS).mem =
    some (.load 1 (8 * q) 8, i) := by
  decide +kernel

public theorem b0_regs : ∀ r ∈ [XReg.X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
    (after b0 entryS).reg r = some (.reg r) := by
  decide +kernel

public theorem b1_keeps : keepsRegs noneS (after b1 noneS) calleeRegs = true ∧
    (after b1 noneS).mem = [] := by
  decide +kernel

public theorem b2_keeps : keepsRegs pubS (after b2 pubS) calleeRegs = true := by
  decide +kernel

public theorem b3_keeps : keepsRegs noneS (after b3 noneS) calleeRegs = true ∧
    (after b3 noneS).mem = [] := by
  decide +kernel

public theorem b4_restores : restores slots 240 (after b4 exitS) = true := by
  decide +kernel

public theorem b2_mem1 : ∀ w ∈ (after b2 pubS).mem, w.r = 0 ∧ 40 ≤ w.off ∧ w.off + w.n ≤ 72 := by
  decide +kernel

public theorem b4_mem : (after b4 exitS).mem = [] := by decide +kernel

end NativeRustcVmArm.Top.Seed
