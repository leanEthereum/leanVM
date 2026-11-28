module

public import NativeRustcVmX64.Top.Assembly.Layout
public import NativeRustcVmX64.Top.Assembly.Sumcheck
public import NativeRustcVmX64.Bus.ComputedBytecodeValue
public import NativeRustcVmX64.Bus.Fingerprints
public import NativeRustcVmX64.Bus.VerifyBusBalanceClosure0
public import NativeRustcVmX64.Bus.BlockForm
public import NativeRustcVmX64.Bus.BytecodeShare
public import NativeRustcVmX64.Bus.GkrStep
public import NativeRustcVmX64.Bus.GkrLayers
public import NativeRustcVmX64.Bus.VerifyGkr
public import NativeRustcVmX64.Bus.BusLayout
public import NativeRustcVmX64.Bus.VerifyBusBalance.Main
public import NativeRustcVmX64.Bus.AccumulateSide
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Fingerprints.Names
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names

/-!
# The bus's functions, placed in `leanvm_verify`'s program

Those of `bus.rs` proved so far, instantiated at their places in `Vm.code` with their callees'
instantiated contracts.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem computedBytecodeValue :
    Spec (label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre ComputedBytecodeValuePost :=
  Bus.ComputedBytecodeValue.computedBytecodeValue_spec (placed_ComputedBytecodeValue hP)
    (mleOfComputedBytecodeValue hP)

theorem fingerprints : Spec (label NativeRustcVmX64.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost :=
  Bus.Fingerprints.fingerprints_spec (placed_Fingerprints hP) (kpow hP) (dot hP)
    (indexMleFrom hP)

theorem fpClosure : Spec (label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost :=
  Bus.FpClosure.fpClosure_spec (placed_VerifyBusBalanceClosure0 hP) (fingerprints hP)

theorem blockForm : Spec (label NativeRustcVmX64.Vm.BlockForm.entryLabel) BlockFormPre BlockFormPost :=
  Bus.BlockForm.blockForm_spec (placed_BlockForm hP) (formTerms hP) (formBufAddScaled hP)

theorem bytecodeShare :
    ∀ a s, Spec (label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s) :=
  fun a _ ↦ Bus.BytecodeShare.bytecodeShare_spec (placed_BytecodeShare hP) (readScalar hP a)
    (sumcheckPlain hP a) (eqKernel hP) (dot hP) (ewMul hP)

theorem gkrStep : ∀ a s g, Spec (label NativeRustcVmX64.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g) :=
  fun a _ _ ↦ Bus.GkrStep.gkrStep_spec (placed_GkrStep hP) (bitLength hP) (grind hP a)
    (squeeze hP) (polyEval hP) (sumcheckGkr hP a) (readScalars hP a) (prodE hP)
    (sampleChallenges hP a) (mleOfMultilinearEval hP)

theorem gkrLayers :
    ∀ a s g, Spec (label NativeRustcVmX64.Vm.GkrLayers.entryLabel) (GkrLayersPre a s g) (GkrLayersPost a s g) :=
  fun a _ _ ↦ Bus.GkrLayers.gkrLayers_spec (placed_GkrLayers hP) (gkrStep hP a)

theorem verifyGkr : ∀ a s, Spec (label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s) :=
  fun a _ ↦ Bus.VerifyGkr.verifyGkr_spec (placed_VerifyGkrGrandProducts hP) (readScalar hP a)
    (gkrLayers hP a)

theorem busLayout : ∀ L bl, Spec (label NativeRustcVmX64.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl) :=
  fun _ _ ↦ Bus.BusLayout.busLayout_spec (placed_BusLayout hP) (memset hP) (memcpy hP)
    (stackOffsets hP)

theorem accumulateSide : ∀ L rows bl F SL, Spec (label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
    (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL) :=
  Bus.AccumulateSide.accumulateSide_spec (placed_AccumulateSide hP) (eqEvalFn hP) (ewMul hP)
    (memcpy hP) (blockForm hP) (formBufAddScaled hP) (paddingWeight hP) (evaluate hP)

theorem verifyBusBalance : ∀ a s L, Spec (label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
    (VerifyBusBalancePost a s L) :=
  Bus.VerifyBusBalance.verifyBusBalance_spec (placed_VerifyBusBalance hP) (busLayout hP)
    (memcpy hP) (bitLength hP) (grind hP) (sampleChallenges hP) (squeeze hP) (verifyGkr hP)
    (readScalars hP) (readScalar hP) (pushClaim hP) (bytecodeShare hP)
    (computedBytecodeValue hP) (kpow hP) (fpClosure hP) (accumulateSide hP) (bufEW63Extend hP)

end

end NativeRustcVmX64.Assembly
