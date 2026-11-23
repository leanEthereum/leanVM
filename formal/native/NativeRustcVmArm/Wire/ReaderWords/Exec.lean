module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ReaderWords
public meta import NativeRustcVmArm.Code.Vm.ReaderWords

/-!
# `Reader::words`' blocks, run by the symbolic executor

- `entryS`: region 0 the 32-byte frame below SP, region 1 the reader (X0): the prologue and the
  bound check (`b0`).
- `frS`: region 0 the frame (SP): `None` (`b1`), the empty check (`b2`), the loop's set-up (`b3`),
  `Some` (`b7`).
- `loopS`: region 0 the frame, region 1 the next output word (X20): the call (`b4`), its check
  (`b5`), the store and the count (`b6`).
-/

namespace NativeRustcVmArm.Wire.ReaderWords

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReaderWords

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- At the entry: the frame (region 0), SP at its end; the reader (region 1, X0). -/
def entryS : SState := init [(32, true), (24, false)] (.ptr 0 32) [(.X0, .ptr 1 0)]

/-- In the frame (region 0, SP). -/
def frS : SState := init [(32, true)] (.ptr 0 0)

/-- In the loop: the frame (region 0, SP) and the next output word (region 1, X20). -/
def loopS : SState := init [(32, true), (8, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 loopS
sym_block run_b5 := exec b5 loopS
sym_block run_b6 := exec b6 (after b5 loopS)
sym_block run_b7 := exec b7 frS

end NativeRustcVmArm.Wire.ReaderWords
