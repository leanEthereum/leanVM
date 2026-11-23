module

public import NativeRustcVmX64.Top.Assembly.Bus
public import NativeRustcVmX64.Top.Assembly.Ring
public import NativeRustcVmX64.Top.Assembly.Tables
public import NativeRustcVmX64.Top.Assembly.Whir
public import NativeRustcVmX64.KeccakGkr.KeccakPhase
public import NativeRustcVmX64.Top.VerifyExecution
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# `verify_execution`, placed in `leanvm_verify`'s program

`verify_execution`'s contract instantiated at its place in `Vm.code` with its callees' instantiated
contracts.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem keccakPhase : ∀ a s cs layout evals, Spec (label NativeRustcVmX64.Vm.KeccakPhase.entryLabel)
    (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals) :=
  KeccakGkr.KeccakPhase.keccakPhase_spec (placed_KeccakPhase hP) (memcpy hP) (verifyKeccak hP)

theorem verifyExecution : ∀ a s, Spec (label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
    (VerifyExecutionPost a s) :=
  Top.VerifyExecution.verifyExecution_spec (placed_VerifyExecution hP) (readAnnouncedSizes hP)
    (commitStack hP) (readOod hP) (verifyBusBalance hP) (tablePhase hP)
    (tableColumnClaims hP) (publicInputPhase hP) (keccakPhase hP)
    (ringSwitch hP)
    (verifyStackedOpening hP)

end

end NativeRustcVmX64.Assembly
