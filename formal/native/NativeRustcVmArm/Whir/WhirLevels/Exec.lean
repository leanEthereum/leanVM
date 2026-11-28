module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.WhirLevels
public meta import NativeRustcVmArm.Code.Vm.WhirLevels
public meta import NativeRustcVmArm.Whir.Common

/-!
# `whir_levels`'s blocks, run by the symbolic executor

rustc unrolled the loop over the (at most `6`) levels. Region 0 is the 96-byte frame at the
prologue (`entryS`, `b0`) and the epilogues (`epiS`: `b4`, the tail call of `final_level`, and
`b38`, returning `None`); the level `k` reads (`lvS n`, region 0 the first `n` bytes of the levels at
X23, or X4 at `b1`); the `α`s' count at byte `16` of the state (`wS`, X19: `b3`, `b9`, `b16`, `b23`,
`b29`, `b35`); the other blocks only move registers (`regsS`). `b37`, a seventh level, is never
reached (a ladder has at most `6`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.WhirLevels

@[expose] public section

/-- At the entry: the frame below SP. -/
def entryS : SState := init [(96, true)] (.ptr 0 96)
/-- The epilogues: the frame at SP. -/
def epiS : SState := init [(96, true)] (.ptr 0 0)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- The `α`s' count at X19 + 16. -/
def wS : SState := init [(24, false)] .sp [(.X19, .ptr 0 0)]
/-- The first `n` bytes of the levels at X23. -/
def lvS (n : Nat) : SState := init [(n, false)] .sp [(.X23, .ptr 0 0)]
/-- Level 0's fold at X4. -/
def lv0S : SState := init [(8, false)] .sp [(.X4, .ptr 0 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 lv0S
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 wS
sym_block run_b4 := exec b4 epiS
sym_block run_b5 := exec b5 (lvS 40)
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 (lvS 32)
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 wS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 (lvS 64)
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 (lvS 56)
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 wS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 (lvS 88)
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 (lvS 80)
sym_block run_b22 := exec b22 regsS
sym_block run_b23 := exec b23 wS
sym_block run_b24 := exec b24 (lvS 112)
sym_block run_b25 := exec b25 regsS
sym_block run_b26 := exec b26 regsS
sym_block run_b27 := exec b27 (lvS 104)
sym_block run_b28 := exec b28 regsS
sym_block run_b29 := exec b29 wS
sym_block run_b30 := exec b30 (lvS 136)
sym_block run_b31 := exec b31 regsS
sym_block run_b32 := exec b32 regsS
sym_block run_b33 := exec b33 (lvS 128)
sym_block run_b34 := exec b34 regsS
sym_block run_b35 := exec b35 wS
sym_block run_b36 := exec b36 regsS
sym_block run_b38 := exec b38 epiS

end NativeRustcVmArm.Whir.WhirLevels
