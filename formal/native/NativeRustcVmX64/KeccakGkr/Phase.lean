module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# Phase 6's entry on x86-64: `keccak_phase` (and `verify_keccak`)

The phase entry uses the proved `verify_keccak` contract. Its remaining hypotheses are precisely
the contracts of `verify_keccak`'s callees; no `verify_keccak` hypothesis remains.
-/

namespace NativeRustcVmX64.KeccakGkr

open NativeRustcX64 NativeVm.Model
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {kp kv : Nat}

theorem keccakPhase_spec
    (hp : Placed NativeRustcVmX64.Vm.KeccakPhase.code kp)
    (hv : Placed NativeRustcVmX64.Vm.VerifyKeccak.code kv)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hfc : ∀ inst segment lanePoint output, Spec (Labels.label NativeRustcVmX64.Vm.FirstClaim.entryLabel)
      (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output))
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hvl : ∀ a s c, Spec (Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c) (VerifyLayerPost a s c))
    (hko : ∀ a s c, Spec (Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hsp : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s))
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.KeccakPhase.entryLabel) (KeccakPhasePre a s cs layout evals)
      (KeccakPhasePost a s cs layout evals) :=
  KeccakPhase.keccakPhase_spec hp hmemcpy
    (VerifyKeccak.verifyKeccak_spec hv hbl hgr hsc hrs hrss hfc hmemcpy hvl hko hmul hext hpc hsp hmle hdot)
    a s cs layout evals

end

end NativeRustcVmX64.KeccakGkr

/-- info: 'NativeRustcVmX64.KeccakGkr.keccakPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.keccakPhase_spec
