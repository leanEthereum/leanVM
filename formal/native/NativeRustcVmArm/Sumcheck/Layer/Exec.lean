module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer
public meta import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer

/-!
# `sumcheck` with `verify_layer`'s closure: its blocks, run by the symbolic executor

Region 0 the 176-byte frame below the entry's SP:
- `entryS`, at the entry (`b0`, `b1`);
- `frS`, in the frame (SP its base): `b2`, `b4` to `b7`, `b9`;
- `ptS`, at `b3`: region 1 the point's coordinate `i` (X25 its second word);
- `slotS`, at `b8`: region 1 the slot at X20;
- `outS`, at the exits `b10` to `b12`: region 1 the output at X19.
-/

namespace NativeRustcVmArm.Sumcheck.Layer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfVerifyLayer

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- At the entry: the frame, SP its end. -/
def entryS : SState := init [(176, true)] (.ptr 0 176)

/-- In the frame: SP its base. -/
def frS : SState := init [(176, true)] (.ptr 0 0)

/-- At `b3`: the frame and the point's coordinate at X25 − 8. -/
def ptS : SState := init [(176, true), (16, false)] (.ptr 0 0) [(.X25, .ptr 1 8)]

/-- At `b8`: the frame and the slot at X20. -/
def slotS : SState := init [(176, true), (16, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

/-- At the exits: the frame and the output at X19. -/
def outS : SState := init [(176, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 ptS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 slotS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 outS
sym_block run_b11 := exec b11 outS
sym_block run_b12a := exec b12 (after b10 outS)
sym_block run_b12b := exec b12 (after b11 outS)

end NativeRustcVmArm.Sumcheck.Layer
