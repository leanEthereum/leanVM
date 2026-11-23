module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Climb
public meta import NativeRustcVmArm.Code.Vm.Climb

/-!
# `climb`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, then `b1`): region 0 the 144-byte frame below SP, region 1 the
  node (X1);
- `headS`, at the loop head `.LClimb_4` (`b5`, `b6`, then `b2` or `b7`, `b9`, then `b3` ending in
  `bl hash_pair`): region 0 the frame (SP), region 1 the level's sibling (X23 − 16);
- `retS`, after `hash_pair` (`b4`): region 0 the frame;
- `exitS`, at `.LClimb_8` (`b10`): region 0 the frame, region 1 the output (X19).

`after ds S` is the state `exec ds S` ends in.
-/

namespace NativeRustcVmArm.Sumcheck.Climb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Climb

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- At the entry: the frame (region 0) and the node (region 1, X1). -/
def entryS : SState := init [(144, true), (32, false)] (.ptr 0 144) [(.X1, .ptr 1 0)]

/-- At the loop head: the frame (region 0, SP) and the sibling (region 1, X23 − 16). -/
def headS : SState := init [(144, true), (32, false)] (.ptr 0 0) [(.X23, .ptr 1 16)]

/-- After `hash_pair`: the frame (region 0, SP). -/
def retS : SState := init [(144, true)] (.ptr 0 0)

/-- At the exit: the frame (region 0, SP) and the output (region 1, X19). -/
def exitS : SState := init [(144, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 (after b5 headS)
sym_block run_b2 := exec b2 (after b6 (after b5 headS))
sym_block run_b3l := exec b3 (after b2 (after b6 (after b5 headS)))
sym_block run_b7 := exec b7 (after b6 (after b5 headS))
sym_block run_b9 := exec b9 (after b7 (after b6 (after b5 headS)))
sym_block run_b3r := exec b3 (after b9 (after b7 (after b6 (after b5 headS))))
sym_block run_b4 := exec b4 retS
sym_block run_b10 := exec b10 exitS

end NativeRustcVmArm.Sumcheck.Climb
