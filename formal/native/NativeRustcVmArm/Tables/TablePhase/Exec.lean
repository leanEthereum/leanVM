module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TablePhase
public meta import NativeRustcVmArm.Code.Vm.TablePhase

/-!
# `table_phase`'s blocks, run by the symbolic executor

Region 0 the 128-byte frame: `ξ`'s five powers (`80` bytes from `0`), the saved registers (`80`
on). `entryS` at the entry (`b0`: the prologue, `bl bit_length`); `sF` in the frame (`b1`:
`bl grind`; `b2`: its result; `b3`: `bl squeeze`; `b4`: the powers zeroed, `bl powers`; `b5`:
`bl dot`; `b6`: `bl table_sumcheck`; `b7`: the epilogue).
-/

namespace NativeRustcVmArm.Tables.TablePhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TablePhase

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(128, true)] (.ptr 0 128)
/-- In the frame, SP at its base. -/
def sF : SState := init [(128, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 sF
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 sF
sym_block run_b6 := exec b6 sF
sym_block run_b7 := exec b7 sF

end NativeRustcVmArm.Tables.TablePhase
