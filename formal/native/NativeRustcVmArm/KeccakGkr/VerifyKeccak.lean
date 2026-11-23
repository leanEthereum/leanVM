module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.FirstClaim.Names
public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Out2

/-!
# `verify_keccak` on AArch64

The contract (`VerifyKeccakPre`, `VerifyKeccakPost`, `NativeRustcVmArm/Spec/KeccakGkr.lean`) from
the parts in the code's order: the grind and the challenges (`stepFront`), the first claim
(`stepFirst`), the copies (`stepCopies`), the twelve layers (`stepLayers0`, `stepLayers6`), the
committed outputs' opening, word and check (`stepOpen1`, `stepRead1`, `stepWord`), the column
claim (`stepPoint1`, `stepPoint2`), the sumcheck and the inputs' opening (`stepSum`,
`stepOpen2`), the slices and the final check (`stepFin1`, `stepFin2`), `KeccakOutW`'s point and
the return (`stepOut1`, `stepOut2`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeVm.Model NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`verify_keccak`'s contract.** -/
theorem verifyKeccak_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hfc : ∀ inst segment lanePoint output, Spec (Labels.label NativeRustcVmArm.Vm.FirstClaim.entryLabel)
      (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output))
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hvl : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    (hko : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c)
      (KeccakOpenPost a s c))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hsp : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost) :
    ∀ a s cs inst output, Spec (Labels.label NativeRustcVmArm.Vm.VerifyKeccak.entryLabel)
      (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output) := by
  intro a s cs inst output m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyKeccak.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyKeccak.entryOffset) NativeRustcVmArm.Vm.VerifyKeccak.entry_at]
  have h := P0.of hpre
  have hn := h.nums
  refine stepFront hp h hn hbl hgr hsc hrs fun m s4 seg lp c hc ↦ ?_
  refine stepFirst hp h hn (hfc inst seg lp output) hc fun m1 hf ↦ ?_
  refine stepCopies hp h hn hmemcpy hf fun m2 hl ↦ ?_
  refine stepLayers0 hp h hn hvl hl fun m3 s5 c5 hl5 ↦ ?_
  refine stepLayers6 hp h hn hvl hl5 fun m4 s6 c6 hl6 ↦ ?_
  refine stepOpen1 hp h hn hko hl6 fun m5 s7 sl ws v ho ↦ ?_
  refine stepRead1 hp h hn hrs ho fun m6 s8 w hr ↦ ?_
  refine stepWord hp h hn hmul hr fun m7 hw ↦ ?_
  refine stepPoint1 hp h hn hext hw fun m8 hq ↦ ?_
  refine stepPoint2 hp h hn hext hpc hq fun m9 hs ↦ ?_
  refine stepSum hp h hn hsp hs fun m10 s9 low v1 hu ↦ ?_
  refine stepOpen2 hp h hn hko hu fun m11 s10 sl2 ws2 v2 hv ↦ ?_
  refine stepFin1 hp h hn hrss hv fun m12 s11 xs hy ↦ ?_
  refine stepFin2 hp h hn hmle hdot hmul hy fun m13 hx ↦ ?_
  exact stepOut1 hp h hn hext hx fun m14 hz ↦ stepOut2 hp h hn hext hz

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
