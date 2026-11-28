module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OutRest
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Claim
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-! # The input opening, final check, output point, and successful epilogue -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem tailStep (hp : Placed NativeRustcVmX64.Vm.VerifyKeccak.code k)
    (hpre : VerifyKeccakPre a s cs inst output m0)
    (hsum : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s))
    (hko : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c))
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} {s1 : TState} {cl : KeccakClaimW} {out : ColumnClaimW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b55Offset wrB t52 (vv m0 V) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s1)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (hcw : WeightsAt st.data.dmem (off (reg m0 .r9) 25600) cl)
    (hcls : NativeRustcVm.Layout.ClaimsWAt st.data.dmem (keccakClaims m0) (cs.push out))
    (hfit : SegmentsFit (reg m0 .rsi).toNat cl)
    (hmod : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (restSum (reg m0 .rsi).toNat cl #[out]).run s1) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h30 : inst.size ≤ 30 := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hsize : inst.size = (reg m0 .rsi).toNat := hpre.2.2.2.2.2.2.2.2.2.1
  refine sumStep hp hpre hsum hat hcl hts hmod
    fun st2 low v s2 hat2 hr2 hv2 hlow2 hts2 hc2 hk2 ↦ ?_
  have hcl2 := Chg.claimF c hc2 (by decide) (by decide) (by decide) (by decide) hcl
  have hcw2 := Chg.wtsR c hc2 (by decide) (by decide) (by decide) (by decide) hcw
  have h4 : low.size = 4 := by
    have hr := hr2
    rw [← NativeRustcVm.Sumcheck.sumcheckFn_none] at hr
    exact Bus.Gkr.sumcheckFn_size _ _ _ _ hr
  refine open2Step hp hpre hko hat2 hcl2 hcw2 hv2 hts2 hfit
    (fun hr ↦ hmod.trans (restSum_open_none hr2 hr))
    fun st3 slot ws v2 s3 hat3 hr3 hv3 hslot3 hws3 hts3 hc3 hk3 ↦ ?_
  obtain ⟨h6, hw64⟩ := open_weights_size hr3
  have hcl3 := Chg.claimF c hc3 (by decide) (by decide) (by decide) (by decide) hcl2
  have hlow3 := Chg.ewsF c hc3 (by decide) (by decide)
    (by rw [Array.length_toList, h4]; decide) (by rw [Array.length_toList, h4]; decide) hlow2
  refine readStep hp hpre hrs (At.widen hat3 (fun _ _ ↦ rfl)) hv3 hts3
    (fun hr ↦ hmod.trans (restSum_read_none hr2 hr3 hr))
    fun st4 sl s4 hat4 hr4 hsl4 hts4 hc4 hk4 ↦ ?_
  have hs64 : sl.size = 64 := NativeRustcVm.Sumcheck.readScalars_size hr4
  have hcl4 := Chg.claimF c hc4 (by decide) (by decide) (by decide) (by decide) hcl3
  have hlow4 := Chg.ewsF c hc4 (by decide) (by decide)
    (by rw [Array.length_toList, h4]; decide) (by rw [Array.length_toList, h4]; decide) hlow3
  have hslot4 := Chg.ewsF c hc4 (by decide) (by decide)
    (by rw [Array.length_toList, h6]; decide) (by rw [Array.length_toList, h6]; decide) hslot3
  have hws4 := Chg.ewsR c hc4 (by decide) (by decide) (i := 2) (o := 140288)
    (by decide) (by decide) (by rw [Array.length_toList, hw64]; decide)
    (by rw [Array.length_toList, hw64]; decide) hws3
  refine mleStep hp hpre hmle hat4 hcl4 hlow4 h4 fun st5 hat5 hc5 hk5 ↦ ?_
  have hws5 := Chg.ewsR c hc5 (by decide) rfl (i := 2) (o := 140288)
    (by decide) (by decide) rfl (by rw [Array.length_toList, hw64]; decide) hws4
  have hsl5 := Chg.ewsR c hc5 (by decide) rfl (i := 4) (o := 584)
    (by decide) (by decide) rfl (by rw [Array.length_toList, hs64]; decide) hsl4
  refine dotStep hp hpre hdot hat5 hws5 hsl5 hw64 hs64 fun st6 hat6 hc6 hk6 ↦ ?_
  refine checkStep hp hpre hmul hat6 rfl rfl rfl rfl rfl rfl
    (fun hb ↦ hmod.trans (restSum_bad hr2 hr3 hr4 hb))
    fun st7 hat7 hcheck hc7 hk7 ↦ ?_
  have hmodel := hmod.trans (restSum_ok hr2 hr3 hr4 hcheck)
  have hc47 := hc5.trans (hc6.trans hc7)
  have hlow7 := Chg.ewsF c hc47 (by decide) rfl
    (by rw [Array.length_toList, h4]; decide) (by rw [Array.length_toList, h4]; decide) hlow4
  refine outFirstStep hp hpre hext hat7 hlow7 h4 fun st8 hat8 hbuf8 hc8 hk8 ↦ ?_
  have hc48 := hc47.trans hc8
  have hcl8 := Chg.claimF c hc48 (by decide) (by decide) (by decide) (by decide) hcl4
  refine outHighStep hp hpre hext hat8 hbuf8 hcl8 h4 hfit rfl rfl
    fun st9 hat9 hbuf9 hc9 hk9 ↦ ?_
  have hc49 := hc48.trans hc9
  have hslot9 := Chg.ewsF c hc49 (by decide) (by decide)
    (by rw [Array.length_toList, h6]; decide) (by rw [Array.length_toList, h6]; decide) hslot4
  refine outSlotStep hp hpre hext hat9 hbuf9 hslot9 h6
    (by simp only [List.length_append, Array.length_toList, List.length_take, h4]; omega)
    fun st10 hat10 hal hbuf10 hc10 hk10 ↦ ?_
  have hc410 := hc49.trans hc10
  have hk410 := NativeRustcVmX64.Transcript.kept_trans hk5 (NativeRustcVmX64.Transcript.kept_trans hk6
    (NativeRustcVmX64.Transcript.kept_trans hk7 (NativeRustcVmX64.Transcript.kept_trans hk8
      (NativeRustcVmX64.Transcript.kept_trans hk9 hk10))))
  have hts10 := Chg.ts c hc410 (by decide) (by decide) (by decide) hk410 hts4
  have hsl10 := Chg.ewsR c hc410 (by decide) (by decide) (i := 4) (o := 584)
    (by decide) (by decide) (by rw [Array.length_toList, hs64]; decide)
    (by rw [Array.length_toList, hs64]; decide) hsl4
  have hcls10 := Chg.cls c (hc2.trans (hc3.trans (hc4.trans hc410)))
    (by decide) (by decide) (by decide) hcls
  refine okG hp hpre hat10 hal (by rw [hmodel]; rfl) ?_
  intro outs pt slices s' hr
  rw [hmodel] at hr
  cases hr
  refine ⟨hts10, ?_, ?_, hs64, hsl10⟩
  · simpa using hcls10
  · simpa [Array.toList_append, Array.toList_extract, List.append_assoc,
      NativeRustcVm.KeccakGkr.outPointCap] using hbuf10

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
