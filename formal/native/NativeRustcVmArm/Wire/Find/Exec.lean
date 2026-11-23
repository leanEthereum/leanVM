module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Find
public meta import NativeRustcVmArm.Code.Vm.Find

/-!
# `find`'s blocks, run by the symbolic executor

`find` uses no stack.

- `regS`: no region: the empty check (`b0`), the loop's set-up (`b1`), `None` (`b4`), the return
  (`b5`).
- `headS`: region 0 the key of the node at X8: the loop's load and comparison (`b2`), then the
  count (`b3`).
-/

namespace NativeRustcVmArm.Wire.Find

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Find

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- No region. -/
def regS : SState := init [] .sp

/-- The key of the node at X8 (region 0). -/
def headS : SState := init [(8, false)] .sp [] [] [] [(.reg .X8, 0, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 (after b2 headS)
sym_block run_b4 := exec b4 regS
sym_block run_b5 := exec b5 regS

end NativeRustcVmArm.Wire.Find
