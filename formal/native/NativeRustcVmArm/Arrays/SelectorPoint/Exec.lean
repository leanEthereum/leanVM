module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.SelectorPoint
public meta import NativeRustcVmArm.Code.Vm.SelectorPoint
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `selector_point`'s blocks, run by the symbolic executor

- `regsS`, registers only: the tests and set-ups (`b0`-`b3`, `b5`, `b6`), the return (`b8`);
- `loopS`, the unrolled loop (`b4`, four entries a turn): region 0 their 64 bytes, X13 their
  address plus `32`;
- `tailS`, the tail loop (`b7`): region 0 the entry, X8 its address.

An entry's low limb is `selBit idx cmp`: bit `idx` of X0, zero when `cmp > 63` (`csel … hi`).
-/

namespace NativeRustcVmArm.Arrays.SelectorPoint

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SelectorPoint

@[expose] public section

/-- Registers only. -/
def regsS : SState := init [] .sp
/-- The unrolled loop: region 0 four entries, X13 their address plus `32`. -/
def loopS : SState := init [(64, false)] .sp [(.X13, .ptr 0 32)]
/-- The tail loop: region 0 the entry, X8 its address. -/
def tailS : SState := init [(16, false)] .sp [(.X8, .ptr 0 0)]

/-- Bit `idx` of X0, `0` when `cmp > 63`. -/
def selBit (idx cmp : Sym) : Sym :=
  .ite (.and (.not (.cmp .ult .W64 cmp (.lit 63))) (.not (.cmp .eq .W64 cmp (.lit 63)))) (.lit 0)
    (.bin .and .W64 (.bin .lsrv .W64 (.reg .X0) idx) (.lit 1))

/-- The registers every block keeps. -/
def keptRegs : List XReg := calleeRegs ++ [.X0, .X1, .X2, .X30]

/-- An entry written at `o` of region 0: `v`, then the zero limb. -/
def EntryW (S : SState) (o : Nat) (v : Sym) : Bool :=
  (List.range 8).all (fun i ↦ findWrite 0 (o + i) S.mem == some (v, i)) &&
    (List.range 8).all (fun i ↦ findWrite 0 (o + 8 + i) S.mem == some (.lit 0, i))

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 loopS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 tailS
sym_block run_b8 := exec b8 regsS

public theorem b0_keeps : keepsAll regsS (after b0 regsS) keptRegs = true := by decide +kernel
public theorem b1_facts : keepsAll regsS (after b1 regsS) keptRegs = true ∧
    (after b1 regsS).reg .X8 =
      some (.bin .sub .W64 (.un (.ubfm 60 59) .W64 (.reg .X2)) (.lit 16)) ∧
    (after b1 regsS).reg .X10 = some (.un (.ubfm 60 59) .W64 (.reg .X2)) := by decide +kernel
public theorem b2_facts : keepsAll regsS (after b2 regsS) (.X10 :: keptRegs) = true ∧
    (after b2 regsS).reg .X8 = some (.reg .X1) ∧ (after b2 regsS).reg .X9 = some (.lit 0) := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) (.X10 :: keptRegs) = true := by
  decide +kernel
public theorem b4_facts : keepsAll loopS { after b4 loopS with mem := [] }
      ([.X8, .X9, .X10, .X12] ++ keptRegs) = true ∧
    (∀ w ∈ (after b4 loopS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    EntryW (after b4 loopS) 0 (selBit (.reg .X11) (.reg .X11)) = true ∧
    EntryW (after b4 loopS) 16 (selBit (.bin .add .W64 (.reg .X11) (.lit 1)) (.reg .X11)) = true ∧
    EntryW (after b4 loopS) 32 (selBit (.bin .add .W64 (.reg .X11) (.lit 2)) (.reg .X11)) = true ∧
    EntryW (after b4 loopS) 48 (selBit (.bin .add .W64 (.reg .X11) (.lit 3)) (.reg .X11)) = true ∧
    (after b4 loopS).reg .X11 = some (.bin .add .W64 (.reg .X11) (.lit 4)) ∧
    (after b4 loopS).reg .X13 = some (.ptr 0 96) := by
  decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) ([.X8, .X9, .X10] ++ keptRegs) = true := by
  decide +kernel
public theorem b6_facts : keepsAll regsS (after b6 regsS) ([.X8, .X9] ++ keptRegs) = true ∧
    (after b6 regsS).reg .X10 = some (.bin .add .W64 (.reg .X1) (.reg .X10)) := by decide +kernel
public theorem b7_facts : keepsAll tailS { after b7 tailS with mem := [] } (.X10 :: keptRegs) = true ∧
    (∀ w ∈ (after b7 tailS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    EntryW (after b7 tailS) 0 (selBit (.reg .X9) (.reg .X9)) = true ∧
    (after b7 tailS).reg .X8 = some (.ptr 0 16) ∧
    (after b7 tailS).reg .X9 = some (.bin .add .W64 (.reg .X9) (.lit 1)) := by
  decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) keptRegs = true := by decide +kernel

end NativeRustcVmArm.Arrays.SelectorPoint
