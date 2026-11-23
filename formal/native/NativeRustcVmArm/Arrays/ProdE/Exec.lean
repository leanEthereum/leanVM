module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.ProdE
public meta import NativeRustcVmArm.Code.Vm.ProdE
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `prod_e`'s blocks, run by the symbolic executor

rustc specialised `prod_e` to its only caller's lengths, `2` to `4`: straight-line code, a call
of `EW::mul` per element, the last one a tail call at length `4`.

- `entryS`, the prologue (`b0a`, `b0`'s first instructions): region 0 the 32-byte frame;
- `ldS .X0 0` (`b0b`: `values[0]`, `1·values[0]`), `ldS .X19 (-16)` (`b1`), `ldS .X19 (-32)`
  (`b3`), `ldS .X19 (-48)` (`b6a`): region 0 the element;
- `regsS`, the length tests (`b2`, `b4`);
- `exitS`, the epilogue (`b5`) and the tail call's (`b6b`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.ProdE

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ProdE

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(32, true)] (.ptr 0 32)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(32, true)] (.ptr 0 0)

/-- The prologue. -/
def b0a : List Directive := b0.take 3
/-- `values[0]` and the first call. -/
def b0b : List Directive := b0.drop 3
/-- `values[3]`. -/
def b6a : List Directive := b6.take 2
/-- The epilogue and the tail call. -/
def b6b : List Directive := b6.drop 2

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(0, .X30), (16, .X20), (24, .X19)]

/-- The registers the code keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (ldS .X0 0)
sym_block run_b1 := exec b1 (ldS .X19 (-16))
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 (ldS .X19 (-32))
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 exitS
sym_block run_b6a := exec b6a (ldS .X19 (-48))
sym_block run_b6b := exec b6b exitS

public theorem b0a_frame : (∀ p ∈ slots, p.1 + 8 ≤ 32 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → (after b0a entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b0b_facts : keepsAll (ldS .X0 0) (after b0b (ldS .X0 0)) keptRegs = true ∧
    (([] : List XReg).all fun q ↦ ((ldS .X0 0).reg q).isSome &&
      (after b0b (ldS .X0 0)).reg q == (ldS .X0 0).reg q) = true := by
  decide +kernel
public theorem b1_facts : keepsAll (ldS .X19 (-16)) (after b1 (ldS .X19 (-16))) keptRegs = true ∧
    ([XReg.X0, .X1, .X19, .X20].all fun q ↦ ((ldS .X19 (-16)).reg q).isSome &&
      (after b1 (ldS .X19 (-16))).reg q == (ldS .X19 (-16)).reg q) = true := by
  decide +kernel
public theorem b3_facts : keepsAll (ldS .X19 (-32)) (after b3 (ldS .X19 (-32))) keptRegs = true ∧
    ([XReg.X0, .X1, .X19, .X20].all fun q ↦ ((ldS .X19 (-32)).reg q).isSome &&
      (after b3 (ldS .X19 (-32))).reg q == (ldS .X19 (-32)).reg q) = true := by
  decide +kernel
public theorem b6a_facts : keepsAll (ldS .X19 (-48)) (after b6a (ldS .X19 (-48))) keptRegs = true ∧
    ([XReg.X0, .X1, .X19, .X20].all fun q ↦ ((ldS .X19 (-48)).reg q).isSome &&
      (after b6a (ldS .X19 (-48))).reg q == (ldS .X19 (-48)).reg q) = true := by
  decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b5_restores : restores slots 32 (after b5 exitS) = true := by decide +kernel
public theorem b6b_restores : restores slots 32 (after b6b exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.ProdE
