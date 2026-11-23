module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TableWeights
public meta import NativeRustcVmArm.Code.Vm.TableWeights

/-!
# `table_weights`'s blocks, run by the symbolic executor

Region 0 is always the 240-byte frame (SP inside the function, 16-byte aligned).
- `entryS`, at the entry (`b0`, then `b1` or `b12`): region 1 the six heights (X1), SP region
  0's end.
- `headS`, at the loop head `.LTableWeights_4` (`b10`, then `b11`) and at `.LTableWeights_3`
  (`b3`): region 1 the coordinate's challenge (X27).
- `eqS`, at `.LTableWeights_2` (`b2`): region 1 the equality point's coordinate (X23 - 8).
- `midS`, after a multiplication (`b4` to `b9`).
- `lastS`, at the exit `.LTableWeights_7` (`b13`): region 1 the 96 bytes at `out` (the word
  at 8).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableWeights

@[expose] public section

/-- At the entry. -/
def entryS : SState := init [(240, true), (48, false)] (.ptr 0 240) [(.X1, .ptr 1 0)]

/-- At the loop head. -/
def headS : SState := init [(240, true), (16, false)] (.ptr 0 0) [(.X27, .ptr 1 0)]

/-- At `.LTableWeights_2`. -/
def eqS : SState := init [(240, true), (16, false)] (.ptr 0 0) [(.X23, .ptr 1 8)]

/-- After a multiplication. -/
def midS : SState := init [(240, true)] (.ptr 0 0)

/-- After the last multiplication. -/
def lastS : SState := init [(240, true), (96, false)] (.ptr 0 0) [] [] [] [(.load 0 8 8, 1, 0)]

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

public theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) : after ds S = S₁ := by
  rw [after, h]

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b12 := exec b12 (after b0 entryS)
sym_block run_b10 := exec b10 headS
sym_block run_b11 := exec b11 (after b10 headS)
sym_block run_b3 := exec b3 headS
sym_block run_b2 := exec b2 eqS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b13 := exec b13 lastS

end NativeRustcVmArm.Tables.TableWeights
