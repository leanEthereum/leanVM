module

public import NativeRustcVmArm.Code.Vm.FirstClaim.Names
public import NativeRustcVmArm.Code.Vm.InstanceWeights.Names
public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcVmArm.Code.Vm.LinearTranspose.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.SlotWeights.Names
public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Code.Vm.TableWeights.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Tables.TableWeights
public import NativeRustcVmArm.Tables.PublicInputPhase
public import NativeRustcVmArm.KeccakGkr.KeccakPi
public import NativeRustcVmArm.KeccakGkr.LinearTranspose
public import NativeRustcVmArm.KeccakGkr.InstanceWeights
public import NativeRustcVmArm.KeccakGkr.SlotWeights
public import NativeRustcVmArm.KeccakGkr.FirstClaim
public import NativeRustcVmArm.KeccakGkr.KeccakPhase
public import NativeRustcVmArm.KeccakGkr.VerifyLayer
public import NativeRustcVmArm.KeccakGkr.KeccakOpen
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak
public import NativeRustcVmArm.Tables.TablePhase
public import NativeRustcVmArm.Tables.ColumnClaims
public import NativeRustcVmArm.Tables.TableSumcheck
public import NativeRustcVmArm.Tables.TableTerms
public import NativeRustcVmArm.Top.Assembly.Sumcheck

/-!
# The tables' and Keccak GKR's functions, placed in `leanvm_verify`'s program

Those proved so far, instantiated at their places in `Vm.code` with their callees' instantiated
contracts, the callees not yet proved as hypotheses.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem tableWeights : Spec (label NativeRustcVmArm.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost :=
  Tables.TableWeights.table_weights_spec (placed_TableWeights hP) (ewMul hP)

theorem publicInputPhase :
    ∀ a s L pub cs, Spec (label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel) (PublicInputPhasePre a s L pub cs)
      (PublicInputPhasePost a s L pub cs) :=
  fun _ _ _ _ _ ↦ Tables.PublicInputPhase.publicInputPhase_spec (placed_PublicInputPhase hP)
    (squeeze hP) (layoutWPlacement hP) (mleOfMultilinearEval hP) (pushClaim hP)

theorem tableColumnClaims : ∀ ev cs, Spec (label NativeRustcVmArm.Vm.TableColumnClaims.entryLabel)
    (TableColumnClaimsPre ev cs) (TableColumnClaimsPost ev cs) :=
  fun _ _ ↦ Tables.ColumnClaims.tableColumnClaims_spec (placed_TableColumnClaims hP)
    (pushClaim hP)

theorem tableTerms : ∀ a s heights forms, Spec (label NativeRustcVmArm.Vm.TableTerms.entryLabel)
    (TableTermsPre a s heights forms) (TableTermsPost a s heights forms) :=
  fun _ _ _ _ ↦ Tables.TableTerms.tableTerms_spec (placed_TableTerms hP) (readScalars hP)
    (constraintsW hP) (dot hP) (evaluate hP) (bufEW30Extend hP) (ewMul hP)

theorem tableSumcheck :
    ∀ a s heights bus, Spec (label NativeRustcVmArm.Vm.TableSumcheck.entryLabel) (TableSumcheckPre a s heights bus)
      (TableSumcheckPost a s heights bus) :=
  fun _ _ _ _ ↦ Tables.TableSumcheck.tableSumcheck_spec (placed_TableSumcheck hP)
    (sumcheckPlain hP) (tableWeights hP) (tableTerms hP)

theorem tablePhase :
    ∀ a s L bus, Spec (label NativeRustcVmArm.Vm.TablePhase.entryLabel) (TablePhasePre a s L bus)
      (TablePhasePost a s L bus) :=
  fun _ _ _ _ ↦ Tables.TablePhase.tablePhase_spec (placed_TablePhase hP) (bitLength hP)
    (grind hP) (squeeze hP) (powers hP) (dot hP) (tableSumcheck hP)

theorem keccakPi : Spec (label NativeRustcVmArm.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost :=
  KeccakGkr.KeccakPi.keccakPi_spec (placed_KeccakPi hP)

theorem linearTranspose :
    ∀ ws, Spec (label NativeRustcVmArm.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws) :=
  KeccakGkr.LinearTranspose.linearTranspose_spec (placed_LinearTranspose hP) (keccakPi hP)

theorem instanceWeights :
    Spec (label NativeRustcVmArm.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost :=
  KeccakGkr.InstanceWeights.instanceWeights_spec (placed_InstanceWeights hP) (powers hP)
    (memcpy hP)

theorem slotWeights :
    ∀ c, Spec (label NativeRustcVmArm.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c) :=
  KeccakGkr.SlotWeights.slotWeights_spec (placed_SlotWeights hP) (eqKernel hP) (ewMul hP)

theorem firstClaim : ∀ inst segment lanePoint output, Spec (label NativeRustcVmArm.Vm.FirstClaim.entryLabel)
    (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output) :=
  KeccakGkr.FirstClaim.firstClaim_spec (placed_FirstClaim hP) (eqKernel hP) (ewMul hP) (dot hP)
    (bufEW30Extend hP) (memcpy hP)

theorem verifyLayer :
    ∀ a s c, Spec (label NativeRustcVmArm.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c) (VerifyLayerPost a s c) :=
  KeccakGkr.VerifyLayer.verifyLayer_spec (placed_VerifyLayer hP) (bitLength hP)
    (bufEW30Extend hP) (dot hP) (ewMul hP) (eqKernel hP) (instanceWeights hP)
    (linearTranspose hP) (memcpy hP) (polyEval hP) (squeeze hP) (sumE hP) (sumcheckPlain hP)
    (sumcheckLayer hP) (grind hP) (readScalars hP)

theorem keccakOpen :
    ∀ a s c, Spec (label NativeRustcVmArm.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c) :=
  KeccakGkr.KeccakOpen.keccakOpen_spec (placed_KeccakOpen hP) (ewMul hP) (memcpy hP)
    (slotWeights hP) (sumcheckPlain hP)

theorem verifyKeccak : ∀ a s cs inst output, Spec (label NativeRustcVmArm.Vm.VerifyKeccak.entryLabel)
    (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output) :=
  KeccakGkr.VerifyKeccak.verifyKeccak_spec (placed_VerifyKeccak hP) (bitLength hP) (grind hP)
    (sampleChallenges hP) (readScalar hP) (readScalars hP) (firstClaim hP) (memcpy hP)
    (verifyLayer hP) (keccakOpen hP) (ewMul hP) (bufEW36Extend hP) (pushClaim hP)
    (sumcheckPlain hP) (mleOfMultilinearEval hP) (dot hP)

theorem keccakPhase :
    ∀ a s cs layout evals, Spec (label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals) :=
  KeccakGkr.KeccakPhase.keccakPhase_spec (placed_KeccakPhase hP) (memcpy hP) (verifyKeccak hP)

end

end NativeRustcVmArm.Assembly
