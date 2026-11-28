module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Weights
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Tail
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

/-! # The layer verifier after the first check

The two sumchecks and second check either reject through the common epilogue or produce the
local kernel. The final grind and challenge feed the bounded weight loop, transpose and claim
update, preserving the original verifier contract.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)
open LeanVM.Parameters LeanVM.Protocol.Verifier

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s s1 : TState}
  {c : KeccakClaimW} {p : Array EW} {d : MachineData}

theorem back_run (hp : Placed code k)
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
      (ReadScalarsPost a s))
    (hpre : VerifyLayerPre a s c m0) (h : AfterA m0 a c p s1 d)
    (hrun : runL s c m0 = ((grind (grindingBits (productBits - 1))).run s1).bind
      fun q ↦ rest2 c p q.2) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b44Offset)⟩ := by
  refine grindSq hp hpre hbl (hgr a) hsq h hrun fun ch s2 d2 h2 hr2 ↦ ?_
  refine inst hp hpre hiw hsum hpe h2 fun d3 h3 ↦ ?_
  refine layer hp hpre (hsl a) h3 hr2 fun pt v s3 d4 h4 hr4 ↦ ?_
  refine plain hp hpre (hspl a) (hrs a) h4 hr4 fun lp t val s5 d5 h5 hr5 ↦ ?_
  refine check hp hpre hek hdot hmul h5 hr5 fun d6 h6 hr6 ↦ ?_
  refine beta hp hpre hbl (hgr a) hsq h6 hr6 fun b s6 d7 h7 hr7 ↦ ?_
  have hpt : pt.size ≤ 30 := by
    rw [h7.psz]
    exact (claimPt hpre (fun _ h ↦ h) h7.body).1
  exact weights_run hp hpre hmul h7 fun d8 hb8 h8 h15 ↦
    tail hp hpre hext hmul hlt hmemcpy hpt h7.psz h7.lsz hb8 h8 h15 hr7

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
