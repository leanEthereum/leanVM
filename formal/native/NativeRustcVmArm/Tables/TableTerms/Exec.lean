module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TableTerms
public meta import NativeRustcVmArm.Code.Vm.TableTerms

/-!
# `table_terms`'s blocks, run by the symbolic executor

Region 0 the 288-byte frame: `out` (X0) at `16`, the constraint powers (X2) at `24`, the form
powers (X3) at `32`, the point (X4, X5) at `40`, `48`, the `TState` (X1) at `56`, the summand at
`64`, the running sum across the call of `constraints_w` at `80`, the next weight's address (plus
`8`) at `96`, the next height's at `104`, the constraints at `112` (32 bytes), the three form values
at `144`, the saved registers from `192`. Each block runs from its own start state, SP the frame's
base:

- `entryS` (`b0`): region 0 the frame and the 16 bytes of stack arguments above it (the weights'
  and the evaluations' addresses, at `288`, `296`).
- `tabS` (`b1`, the loop head): region 1 table `i`'s 40-byte `TABLES` entry, X21 at its byte `8`.
- `evS` (`b2`: the length, `bl read_scalars`): region 1 the `i`th `TableEvalW` (1968 bytes) at X27.
- `tab19S` (`b4`: `bl constraints_w`; `b5`: `bl dot`): region 1 the `TABLES` entry, X19 at its
  byte `8`.
- `formS` (`b6` to `b8`: `bl evaluate`): region 1 the table's three `FormBuf`s (17784 bytes) at X20.
- `wS` (`b9`: `bl dot`): region 1 the table's weight, the word at `96` its end.
- `ptS` (`b10`: `Buf::extend` of the point): region 1 the `TableEvalW` at X27, region 2 the height,
  at the word at `104`.
- `outS` (`b14`, `b15`: the result): region 1 the 24 bytes at the word at `16`.
- `sF` (`b3`, `b11` to `b13`, `b16`): the frame only.
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableTerms

@[expose] public section

/-- At the entry: the frame and the stack arguments (region 0, 304 bytes). -/
def entryS : SState := init [(304, true)] (.ptr 0 288)
/-- At the loop head. -/
def tabS : SState := init [(288, true), (40, false)] (.ptr 0 0) [] [] [] [(.reg .X21, (1, 8))]
/-- At `b2`. -/
def evS : SState := init [(288, true), (1968, false)] (.ptr 0 0) [] [] [] [(.reg .X27, (1, 0))]
/-- At `b4`, `b5`. -/
def tab19S : SState := init [(288, true), (40, false)] (.ptr 0 0) [] [] [] [(.reg .X19, (1, 8))]
/-- At `b6` to `b8`. -/
def formS : SState :=
  init [(288, true), (17784, false)] (.ptr 0 0) [] [] [] [(.reg .X20, (1, 0))]
/-- At `b9`. -/
def wS : SState := init [(288, true), (16, false)] (.ptr 0 0) [] [] [] [(.load 0 96 8, (1, 8))]
/-- At `b10`. -/
def ptS : SState := init [(288, true), (1968, false), (8, false)] (.ptr 0 0) [] [] []
  [(.reg .X27, (1, 0)), (.load 0 104 8, (2, 0))]
/-- At `b14`, `b15`. -/
def outS : SState := init [(288, true), (24, false)] (.ptr 0 0) [] [] [] [(.load 0 16 8, (1, 0))]
/-- In the frame. -/
def sF : SState := init [(288, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tabS
sym_block run_b2 := exec b2 evS
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 tab19S
sym_block run_b5 := exec b5 tab19S
sym_block run_b6 := exec b6 formS
sym_block run_b7 := exec b7 formS
sym_block run_b8 := exec b8 formS
sym_block run_b9 := exec b9 wS
sym_block run_b10 := exec b10 ptS
sym_block run_b11 := exec b11 sF
sym_block run_b12 := exec b12 sF
sym_block run_b13 := exec b13 sF
sym_block run_b14 := exec b14 outS
sym_block run_b15 := exec b15 outS
sym_block run_b16 := exec b16 sF

end NativeRustcVmArm.Tables.TableTerms
