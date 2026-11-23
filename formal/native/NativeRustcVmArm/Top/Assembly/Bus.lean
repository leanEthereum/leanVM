module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BlockForm.Names
public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Fingerprints.Names
public import NativeRustcVmArm.Code.Vm.GkrLayers.Names
public import NativeRustcVmArm.Code.Vm.GkrStep.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Top.Assembly.Sumcheck
public import NativeRustcVmArm.Bus.ComputedBytecodeValue
public import NativeRustcVmArm.Bus.Fingerprints
public import NativeRustcVmArm.Bus.FpClosure
public import NativeRustcVmArm.Bus.BlockForm
public import NativeRustcVmArm.Bus.GkrLayers
public import NativeRustcVmArm.Bus.VerifyGkr
public import NativeRustcVmArm.Bus.GkrStep
public import NativeRustcVmArm.Bus.BusLayout
public import NativeRustcVmArm.Bus.BytecodeShare
public import NativeRustcVmArm.Bus.VerifyBusBalance
public import NativeRustcVmArm.Bus.AccumulateSide

/-!
# The bus's functions, placed in `leanvm_verify`'s program

The functions of `bus.rs` and `gkr.rs`, instantiated at their places in `Vm.code` with their proved callees.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem computedBytecodeValue :
    Spec (label NativeRustcVmArm.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre ComputedBytecodeValuePost :=
  Bus.ComputedBytecodeValue.computedBytecodeValue_spec (placed_ComputedBytecodeValue hP)
    (mleOfComputedBytecodeValue hP)

theorem fingerprints : Spec (label NativeRustcVmArm.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost :=
  Bus.Fingerprints.fingerprints_spec (placed_Fingerprints hP) (kpow hP) (dot hP)
    (indexMleFrom hP)

theorem fpClosure : Spec (label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost :=
  Bus.FpClosure.fpClosure_spec (placed_VerifyBusBalanceClosure0 hP) (fingerprints hP)

theorem blockForm : Spec (label NativeRustcVmArm.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost :=
  Bus.BlockForm.blockForm_spec (placed_BlockForm hP) (formTerms hP) (formBufAddScaled hP)

theorem gkrStep : ∀ a s g, Spec (label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g) :=
  fun a _ _ ↦ Bus.GkrStep.gkrStep_spec (placed_GkrStep hP) (bitLength hP) (grind hP a)
    (squeeze hP) (polyEval hP) (sumcheckGkr hP a) (readScalars hP a) (prodE hP)
    (sampleChallenges hP a) (mleOfMultilinearEval hP)

theorem gkrLayers :
    ∀ a s g, Spec (label NativeRustcVmArm.Vm.GkrLayers.entryLabel) (GkrLayersPre a s g) (GkrLayersPost a s g) :=
  fun a _ _ ↦ Bus.GkrLayers.gkrLayers_spec (placed_GkrLayers hP) (gkrStep hP a)

theorem verifyGkr : ∀ a s, Spec (label NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s) :=
  fun a _ ↦ Bus.VerifyGkr.verifyGkr_spec (placed_VerifyGkrGrandProducts hP) (readScalar hP a)
    (gkrLayers hP a)

theorem busLayout : ∀ L bl, Spec (label NativeRustcVmArm.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl) :=
  fun _ _ ↦ Bus.BusLayout.busLayout_spec (placed_BusLayout hP) (memset hP) (memcpy hP)
    (stackOffsets hP)

theorem bytecodeShare :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s) :=
  fun a _ ↦ Bus.BytecodeShare.bytecodeShare_spec (placed_BytecodeShare hP) (readScalar hP a)
    (sumcheckPlain hP a) (eqKernel hP) (dot hP) (ewMul hP)

theorem accumulateSide : ∀ L rows bl F SL, Spec (label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
    (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL) :=
  fun _ _ _ _ _ ↦ Bus.AccumulateSide.accumulateSide_spec (placed_AccumulateSide hP)
    (eqEvalFn hP) (ewMul hP) (memcpy hP) (blockForm hP) (formBufAddScaled hP)
    (paddingWeight hP) (evaluate hP)

theorem verifyBusBalance :
    ∀ a s L, Spec (label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L) :=
  Bus.VerifyBusBalance.verifyBusBalance_spec (placed_VerifyBusBalance hP) (busLayout hP)
    (memcpy hP) (bitLength hP) (grind hP) (sampleChallenges hP) (squeeze hP) (verifyGkr hP)
    (readScalars hP) (readScalar hP) (pushClaim hP) (bytecodeShare hP)
    (computedBytecodeValue hP) (kpow hP) (accumulateSide hP) (bufEW63Extend hP) (fpClosure hP)

end

end NativeRustcVmArm.Assembly
