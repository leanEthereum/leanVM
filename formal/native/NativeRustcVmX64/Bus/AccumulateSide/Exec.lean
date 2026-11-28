module

public import NativeRustcVmX64.Bus.AccumulateSide.States
public meta import NativeRustcVmX64.Bus.AccumulateSide.States
public meta import NativeRustcVmX64.Code.Vm.AccumulateSide

/-!
# `accumulate_side`'s blocks, run by the symbolic executor (x86-64)

Every block (or part of one) from its literal state (`States.lean`): `run_b<k>` is the
executor's summary.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.AccumulateSide

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 fS
sym_block run_b2a := exec b2a kAS
sym_block run_b2b := exec b2b kBS
sym_block run_b3 := exec b3 fS
sym_block run_b4 := exec b4 aS
sym_block run_b5 := exec b5 aS
sym_block run_b6 := exec b6 fS
sym_block run_b7 := exec b7 fS
sym_block run_b8 := exec b8 oS
sym_block run_b9 := exec b9 aS
sym_block run_b10 := exec b10 fS
sym_block run_b11 := exec b11 fS
sym_block run_b12 := exec b12 fS
sym_block run_b13 := exec b13 zS
sym_block run_b14 := exec b14 copyS
sym_block run_b15 := exec b15 slS
sym_block run_b16 := exec b16 aS
sym_block run_b17 := exec b17 pS
sym_block run_b18a := exec b18a bS
sym_block run_b18b := exec b18b aS
sym_block run_b19 := exec b19 fS
sym_block run_b20 := exec b20 bS
sym_block run_b21 := exec b21 tS
sym_block run_b22 := exec b22 fS
sym_block run_b23a := exec b23a hS
sym_block run_b23b := exec b23b aS
sym_block run_b24 := exec b24 fS
sym_block run_b25 := exec b25 fS
sym_block run_b26 := exec b26 fS
sym_block run_b27 := exec b27 aS
sym_block run_b28 := exec b28 fS
sym_block run_b29 := exec b29 fS
sym_block run_b30 := exec b30 outS
sym_block run_b31 := exec b31 outS
sym_block run_b32 := exec b32 fS

end NativeRustcVmX64.Bus.AccumulateSide
