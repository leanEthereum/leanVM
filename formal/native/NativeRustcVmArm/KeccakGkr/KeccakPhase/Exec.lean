module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.KeccakPhase
public meta import NativeRustcVmArm.Code.Vm.KeccakPhase

/-!
# `keccak_phase`'s blocks, run by the symbolic executor

Region 0 the 480-byte frame: below SP at the entry (`entryS`, `b0`), from SP after the prologue
(`midS`). Region 1 the tables' evaluations, X2 its base at the entry (`b0` reads `KECCAK`'s values'
count), X25 after (`evS`, `b3` reads `KECCAK`'s point's count).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.KeccakPhase

@[expose] public section

/-- At the entry: the frame below SP, the evaluations at X2. -/
def entryS : SState := init [(480, true), (11808, false)] (.ptr 0 480) [(.X2, .ptr 1 0)]
/-- After the prologue: the frame from SP. -/
def midS : SState := init [(480, true)] (.ptr 0 0)
/-- Before `verify_keccak`: the frame from SP, the evaluations at X25. -/
def evS : SState := init [(480, true), (11808, false)] (.ptr 0 0) [(.X25, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 evS
sym_block run_b4 := exec b4 midS

end NativeRustcVmArm.KeccakGkr.KeccakPhase
