module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.PublicInputPhase
public meta import NativeRustcVmArm.Code.Vm.PublicInputPhase

/-!
# `public_input_phase`'s blocks, run by the symbolic executor

Region 0 the 608-byte frame: the point (`496` bytes from `0`), the two elements `multilinear_eval`
reads (`496`), its point (`528`), the saved registers (`544` on). `entryS` at the entry (`b0`: the
prologue, `bl squeeze`); `sF` in the frame (`b1`: the point zeroed, `bl placement`; `b2`: the
point's length; `b4`, `b7`: `bl push_claim`; `b5`: the first claim's result; `b8`, `b9`: the
epilogue); `pubS` with the public input at X20 (region 1; `b3`, `b6`: `bl multilinear_eval_by`).
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(608, true)] (.ptr 0 608)
/-- In the frame, SP at its base. -/
def sF : SState := init [(608, true)] (.ptr 0 0)
/-- In the frame, the public input at X20 (region 1). -/
def pubS : SState := init [(608, true), (32, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 sF
sym_block run_b3 := exec b3 pubS
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 sF
sym_block run_b6 := exec b6 pubS
sym_block run_b7 := exec b7 sF
sym_block run_b8 := exec b8 sF
sym_block run_b9 := exec b9 sF

end NativeRustcVmArm.Tables.PublicInputPhase
