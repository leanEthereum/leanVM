module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.LayersAll
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# `verify_keccak` from its entry to the first opening (x86-64)

`toB40`: `frontA`, `frontB`, `firstStep`, `copiesStep`, `layersStep` in a row, from the entry to
`b40` (`tL`): the last layer's claim at frame offset `992` and its bit weights at the scratch's
`weights`, the first claim at `1768` and its bit weights at the scratch's start, the model's run
the opening's (`restOpen`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **From the entry to `b40`.** -/
theorem toB40 (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hfc : ∀ inst segment lanePoint output, Spec (Labels.label NativeRustcVmX64.Vm.FirstClaim.entryLabel)
      (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output))
    (hvl : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    (cont : ∀ (st : MachineState) (s' : TState) (first cl : KeccakClaimW) (cm : EW),
      At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b40Offset wrA tL (vv m0 (V2 cm first.point.size)) st →
      TStateAt st.data.dmem (reg m0 .rdi) a s' →
      ClaimAt st.data.dmem (off (fb m0) 992) cl →
      WeightsAt st.data.dmem (off (reg m0 .r9) 25600) cl →
      ClaimAt st.data.dmem (off (fb m0) 1768) first →
      WeightsAt st.data.dmem (off (reg m0 .r9) 0) first →
      first.point.size = inst.size - 4 + 1 → cl.point.size = first.point.size →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (restOpen (reg m0 .rsi).toNat inst first cm cl).run s' →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0)
      ⟨m0, Labels.label NativeRustcVmX64.Vm.VerifyKeccak.entryLabel⟩ := by
  have hsz : inst.size = (reg m0 .rsi).toNat := hpre.2.2.2.2.2.2.2.2.2.1
  refine frontA hp hpre hbl hgr fun st s1 hat hts hrun ↦ ?_
  refine frontB hp hpre hsc hrs hat hts hrun fun st' s4 seg lp cm hat' hts' hseg1 hseg hlp5 hlp
    hcm hrun' ↦ ?_
  have hfp := first_point_size inst seg lp output cm hseg1
  refine firstStep hp hpre hfc hat' hts' hseg1 hseg hlp5 hlp hcm fun st9 hat9 hts9 hcl9 hw9 ↦ ?_
  refine copiesStep hp hpre hmemcpy hat9 hts9 hcl9 hw9
    fun st16 hat16 hts16 h992 h1768 hw0 hw1 ↦ ?_
  refine layersStep hp hpre hvl hat16 hts16 h992 hw1 h1768 hw0
    (by unfold SegmentsFit; rw [hfp, ← hsz]; omega) hrun'
    fun st40 s' cl hat40 hts40 hcl hcw hf hfw hcs hmod ↦ ?_
  exact cont st40 s' _ cl cm hat40 hts40 hcl hcw hf hfw hfp hcs hmod

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
