module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.FoldRound
public meta import NativeRustcVmArm.Code.Vm.FoldRound
public meta import NativeRustcVmArm.Whir.Common

/-!
# `fold_round`'s blocks, run by the symbolic executor

Region 0 is the 208-byte frame below the entry's SP throughout.
- `entryS` (`b0`): SP at the frame's top; the prologue, then `read_scalar` into the frame's
  `Option<EW>` at 88.
- `midS` (`b1` to `b11`, `b13` to `b17`): SP at the frame's base.
- `stateS` (`b12`, `b18`): the state's first 24 bytes (the claim, the `α`s' count) region 1, at
  X20.
- `pushS` (`b19`, `b21` after it): region 1 as in `stateS`, the `α`s' slot of index X8 region 2
  (X20 + 16 X8 + 24), the output region 3 (X19).
- `noneS` (`b20`, `b21` after it), `none0S` (`b21` from `b1`, X8 = 0): the output region 1 (X19).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRound

@[expose] public section

/-- At the entry. -/
def entryS : SState := init [(208, true)] (.ptr 0 208)
/-- Between the calls. -/
def midS : SState := init [(208, true)] (.ptr 0 0)
/-- With the state's head. -/
def stateS : SState := init [(208, true), (24, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]
/-- The address `b19` computes for the `α`s' slot, less its offset `24`. -/
def slotSym : Sym := .bin .add .W64 (.ptr 1 0) (.un (.shift .LSL 4) .W64 (.reg .X8))
/-- At the push. -/
def pushS : SState :=
  init [(208, true), (24, false), (16, false), (40, false)] (.ptr 0 0)
    [(.X20, .ptr 1 0), (.X19, .ptr 3 0)] [] [] [(slotSym, 2, -24)]
/-- At `None`. -/
def noneS : SState := init [(208, true), (40, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
/-- At `None` from `b1`. -/
def none0S : SState :=
  init [(208, true), (40, false)] (.ptr 0 0) [(.X19, .ptr 1 0), (.X8, .lit 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 stateS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 midS
sym_block run_b16 := exec b16 midS
sym_block run_b17 := exec b17 midS
sym_block run_b18 := exec b18 stateS
sym_block run_b19 := exec b19 pushS
sym_block run_b21p := exec b21 (after b19 pushS)
sym_block run_b20 := exec b20 noneS
sym_block run_b21n := exec b21 (after b20 noneS)
sym_block run_b21z := exec b21 none0S

end NativeRustcVmArm.Whir.FoldRound
