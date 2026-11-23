module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ClimbLevel
public meta import NativeRustcVmArm.Code.Vm.ClimbLevel

/-!
# `climb_level`'s blocks, run by the symbolic executor

Region 0 is the 224-byte frame below SP throughout.

- `entryS`: SP at the frame's end: the prologue (`b0`).
- `frS`: SP at the frame: the set-up, the loop's head, the calls, the checks, the exits.
- `scanS`: region 1 node `j` (X8 plus 40), region 2 node `i`'s key (X24): a step of the scan
  (`b8`); `scanSelfS` the same when `j = i`.
- `foundS`: region 1 node `j` (X8), region 2 sibling `i` (`X26 * 40 + X22`): the sibling found
  (`b9`).
- `carS`: region 1 node `i`'s key (X24), region 2 sibling `i`: the sibling read (`b13`).
- `storeS`: region 1 parent `p` (`X19 * 40 + [sp, #16]`): the parent stored (`b4`).
-/

namespace NativeRustcVmArm.Wire.ClimbLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ClimbLevel

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- Sibling `i`'s address (`madd x, x26, 40, x22`). -/
def sibAddr : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X26) (.lit 40)) (.reg .X22)

/-- Parent `p`'s address (`madd x8, x19, 40, [sp, #16]`). -/
def parAddr : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X19) (.lit 40)) (.load 0 16 8)

/-- At the entry: the frame (region 0), SP at its end. -/
def entryS : SState := init [(224, true)] (.ptr 0 224)

/-- In the frame (region 0, SP). -/
def frS : SState := init [(224, true)] (.ptr 0 0)

/-- A step of the scan: node `j` (region 1) at X8 plus 40, node `i`'s key (region 2) at X24. -/
def scanS : SState := init [(224, true), (40, false), (8, false)] (.ptr 0 0) [] [] []
  [(.reg .X8, 1, -40), (.reg .X24, 2, 0)]

/-- A step of the scan at node `i` itself (region 1). -/
def scanSelfS : SState := init [(224, true), (40, false)] (.ptr 0 0) [] [] []
  [(.reg .X8, 1, -40), (.reg .X24, 1, 0)]

/-- The sibling found: node `j` (region 1) at X8, sibling `i` (region 2). -/
def foundS : SState := init [(224, true), (40, false), (40, false)] (.ptr 0 0) [] [] []
  [(.reg .X8, 1, 0), (sibAddr, 2, 0)]

/-- The sibling read: node `i`'s key (region 1) at X24, sibling `i` (region 2), X27 the read
digest's place in the frame. -/
def carS : SState := init [(224, true), (8, false), (40, false)] (.ptr 0 0) [(.X27, .ptr 0 24)] []
  [] [(.reg .X24, 1, 0), (sibAddr, 2, 0)]

/-- The parent stored: parent `p` (region 1). -/
def storeS : SState := init [(224, true), (40, false)] (.ptr 0 0) [] [] [] [(parAddr, 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 storeS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 scanS
sym_block run_b8s := exec b8 scanSelfS
sym_block run_b9 := exec b9 foundS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 carS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS

end NativeRustcVmArm.Wire.ClimbLevel
