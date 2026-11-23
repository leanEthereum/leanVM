module

public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Top.Assembly.Ring
public import NativeRustcVmArm.Top.Assembly.Tables
public import NativeRustcVmArm.Top.Assembly.Whir
public import NativeRustcVmArm.Top.VerifyExecution

/-!
# `verify_execution`, placed in `leanvm_verify`'s program

`verify_execution`'s contract instantiated at its place in `Vm.code` with its callees' instantiated
contracts, the callees not yet proved as hypotheses.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem verifyExecution
    (hbb : ∀ a s L, Spec (label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L))
    (hkp : ∀ a s cs layout evals, Spec (label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals))
    (hnl : ∀ a s level w rounds, Spec (label NativeRustcVmArm.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds)) :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s) :=
  Top.VerifyExecution.verifyExecution_spec (placed_VerifyExecution hP) (readAnnouncedSizes hP)
    (commitStack hP) (readOod hP) hbb (tablePhase hP) (tableColumnClaims hP)
    (publicInputPhase hP) hkp (ringSwitch hP) (verifyStackedOpening hP hnl hfl)

end

end NativeRustcVmArm.Assembly
