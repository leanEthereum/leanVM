module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.CheckAHead
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.InstanceWeights.Names
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# `verify_layer` meets its contract (x86-64)

From the entry to the first check passed (`toAfterA`: the product's read, its projection, ι's
segment kernel and bit weights, the first check), then the rest (`back_run`: the grind and `s`,
the instance weights, the two sumchecks, the values and the local kernel, the second check, the
grind and `β`, the layer's weights, their transpose and the new claim) (`verifyLayer_spec`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat}

/-- **`verify_layer` meets its contract**, given `bit_length`'s, `Buf<EW, 30>::extend`'s, `dot`'s,
`EW::mul`'s, `eq_kernel`'s, `instance_weights`'s, `linear_transpose`'s, `memcpy`'s,
`poly_eval`'s, `squeeze`'s, `sum_e`'s, the two sumchecks', `grind`'s and `read_scalars`'s. -/
theorem verifyLayer_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hiw : Spec (Labels.label NativeRustcVmX64.Vm.InstanceWeights.entryLabel) InstanceWeightsPre InstanceWeightsPost)
    (hlt : ∀ ws, Spec (Labels.label NativeRustcVmX64.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws)
      (LinearTransposePost ws))
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hspl : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hsl : ∀ a s pt, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt)
      (SumcheckLayerPost a s pt))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s)) :
    ∀ a s c, Spec (Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c) := by
  intro a s c m0 h
  have hl : Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b0Offset) := hp.label NativeRustcVmX64.Vm.VerifyLayer.entry_at
  rw [hl]
  exact toAfterA hp (hrs a s) hmul hek hsum h fun p s1 d hA hrun ↦
    back_run hp hbl hext hdot hmul hek hiw hlt hmemcpy hpe hsq hsum hspl hsl hgr hrs h hA hrun

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer

/-- info: 'NativeRustcVmX64.KeccakGkr.VerifyLayer.verifyLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.VerifyLayer.verifyLayer_spec
