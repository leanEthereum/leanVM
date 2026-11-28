module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly
public meta import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly

/-!
# `sumcheck_round_poly`'s blocks, run by the symbolic executor

- `entryS`, at the entry in equality mode (`b0`, then `b1`): region 0 the 112-byte frame below SP,
  region 1 the `Option<EW>` `eq` (X4); `entryN`, the same in plain mode (`b0`, then `b9`), region 1
  only `eq`'s tag (8 bytes);
- `bodyS`, after a call (`b2` to `b8`, `b10` to `b17`): region 0 the frame (SP), region 1 the
  message (X19);
- `exitS`, at `.L8`/`.L9` (`b18`, `b19`): region 0 the frame.
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- At the entry: the frame (region 0) and `eq` (region 1, X4). -/
def entryS : SState := init [(112, true), (24, false)] (.ptr 0 112) [(.X4, .ptr 1 0)]

/-- At the entry in plain mode: the frame (region 0) and `eq`'s tag (region 1, X4). -/
def entryN : SState := init [(112, true), (8, false)] (.ptr 0 112) [(.X4, .ptr 1 0)]

/-- After a call: the frame (region 0, SP) and the message (region 1, X19). -/
def bodyS : SState := init [(112, true), (80, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- At the exit: the frame (region 0, SP). -/
def exitS : SState := init [(112, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b0n := exec b0 entryN
sym_block run_b9 := exec b9 (after b0 entryN)
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 (after b2 bodyS)
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 (after b6 bodyS)
sym_block run_b8 := exec b8 bodyS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 (after b10 bodyS)
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 (after b12 bodyS)
sym_block run_b14 := exec b14 bodyS
sym_block run_b15 := exec b15 bodyS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 (after b16 bodyS)
sym_block run_b18 := exec b18 exitS
sym_block run_b19 := exec b19 exitS

end NativeRustcVmArm.Sumcheck.RoundPoly
