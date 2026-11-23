module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Layers
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Run2
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# `verify_keccak`: the twelve layers (x86-64)

From `b16` (`t16`, the first claim at frame offsets `992` and `1768`, its bit weights at the
scratch's `weights` and start) through the twelve `verify_layer` calls and their checks to `b40`
(`tL`): the last layer's claim at `992`, its bit weights at the scratch's `weights`, the first
claim and its bit weights kept, the model's run the opening's (`layersStep`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)
open LeanVM.Protocol.Verifier (keccakDepth)

public section

/-- `SegmentsFit` depends on the point's size only. -/
theorem fit_size {ls : Nat} {c c' : KeccakClaimW} (h : c'.point.size = c.point.size)
    (hf : SegmentsFit ls c) : SegmentsFit ls c' := by
  unfold SegmentsFit at *
  rw [h]
  exact hf

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **The layers** (`b16` to `b39`): at `b40` (`tL`) the last claim at `992`, its bit weights at
the scratch's `weights`, the first claim at `1768` and its bit weights at the scratch's start. -/
theorem layersStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hvl : ∀ s c, Spec (Labels.label NativeRustcVmX64.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    {st : MachineState} {s5 : TState} {first : KeccakClaimW} {cm : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b16Offset wrA t16 (vv m0 (V2 cm first.point.size)) st)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s5)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) first)
    (hcw : WeightsAt st.data.dmem (off (reg m0 .r9) 25600) first)
    (hf : ClaimAt st.data.dmem (off (fb m0) 1768) first)
    (hfw : WeightsAt st.data.dmem (off (reg m0 .r9) 0) first)
    (hfit : SegmentsFit (reg m0 .rsi).toNat first)
    (hmod : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      (afterLayers (reg m0 .rsi).toNat 0 inst first cm first).run s5)
    (cont : ∀ st' s' cl, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b40Offset wrA tL (vv m0 (V2 cm first.point.size)) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s' →
      ClaimAt st'.data.dmem (off (fb m0) 992) cl →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 25600) cl →
      ClaimAt st'.data.dmem (off (fb m0) 1768) first →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 0) first →
      cl.point.size = first.point.size →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (restOpen (reg m0 .rsi).toNat inst first cm cl).run s' →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  refine layerStep hp hpre hvl (j := 0) (by decide) b16_in_code (by simp [b16]) run_b16
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b17_in_code (by simp [b17]) run_b17 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat hts hcl hcw hf hfw hfit hmod
    fun st1 s1 c1 hat1 hts1 hcl1 hcw1 hf1 hfw1 hsz1 hmod1 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b16_next, NativeRustcVmX64.Vm.VerifyKeccak.b17_next] at hat1
  have hz1 := hsz1
  refine layerStep hp hpre hvl (j := 1) (by decide) b18_in_code (by simp [b18]) run_b18
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b19_in_code (by simp [b19]) run_b19 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat1 hts1 hcl1 hcw1 hf1 hfw1 (fit_size hz1 hfit) hmod1
    fun st2 s2 c2 hat2 hts2 hcl2 hcw2 hf2 hfw2 hsz2 hmod2 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b18_next, NativeRustcVmX64.Vm.VerifyKeccak.b19_next] at hat2
  have hz2 := hsz2.trans hz1
  refine layerStep hp hpre hvl (j := 2) (by decide) b20_in_code (by simp [b20]) run_b20
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b21_in_code (by simp [b21]) run_b21 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat2 hts2 hcl2 hcw2 hf2 hfw2 (fit_size hz2 hfit) hmod2
    fun st3 s3 c3 hat3 hts3 hcl3 hcw3 hf3 hfw3 hsz3 hmod3 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b20_next, NativeRustcVmX64.Vm.VerifyKeccak.b21_next] at hat3
  have hz3 := hsz3.trans hz2
  refine layerStep hp hpre hvl (j := 3) (by decide) b22_in_code (by simp [b22]) run_b22
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b23_in_code (by simp [b23]) run_b23 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat3 hts3 hcl3 hcw3 hf3 hfw3 (fit_size hz3 hfit) hmod3
    fun st4 s4 c4 hat4 hts4 hcl4 hcw4 hf4 hfw4 hsz4 hmod4 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b22_next, NativeRustcVmX64.Vm.VerifyKeccak.b23_next] at hat4
  have hz4 := hsz4.trans hz3
  refine layerStep hp hpre hvl (j := 4) (by decide) b24_in_code (by simp [b24]) run_b24
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b25_in_code (by simp [b25]) run_b25 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat4 hts4 hcl4 hcw4 hf4 hfw4 (fit_size hz4 hfit) hmod4
    fun st5 s5 c5 hat5 hts5 hcl5 hcw5 hf5 hfw5 hsz5 hmod5 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b24_next, NativeRustcVmX64.Vm.VerifyKeccak.b25_next] at hat5
  have hz5 := hsz5.trans hz4
  refine layerStep hp hpre hvl (j := 5) (by decide) b26_in_code (by simp [b26]) run_b26
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b27_in_code (by simp [b27]) run_b27 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat5 hts5 hcl5 hcw5 hf5 hfw5 (fit_size hz5 hfit) hmod5
    fun st6 s6 c6 hat6 hts6 hcl6 hcw6 hf6 hfw6 hsz6 hmod6 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b26_next, NativeRustcVmX64.Vm.VerifyKeccak.b27_next] at hat6
  have hz6 := hsz6.trans hz5
  refine layerStep hp hpre hvl (j := 6) (by decide) b28_in_code (by simp [b28]) run_b28
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b29_in_code (by simp [b29]) run_b29 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat6 hts6 hcl6 hcw6 hf6 hfw6 (fit_size hz6 hfit) hmod6
    fun st7 s7 c7 hat7 hts7 hcl7 hcw7 hf7 hfw7 hsz7 hmod7 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b28_next, NativeRustcVmX64.Vm.VerifyKeccak.b29_next] at hat7
  have hz7 := hsz7.trans hz6
  refine layerStep hp hpre hvl (j := 7) (by decide) b30_in_code (by simp [b30]) run_b30
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b31_in_code (by simp [b31]) run_b31 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat7 hts7 hcl7 hcw7 hf7 hfw7 (fit_size hz7 hfit) hmod7
    fun st8 s8 c8 hat8 hts8 hcl8 hcw8 hf8 hfw8 hsz8 hmod8 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b30_next, NativeRustcVmX64.Vm.VerifyKeccak.b31_next] at hat8
  have hz8 := hsz8.trans hz7
  refine layerStep hp hpre hvl (j := 8) (by decide) b32_in_code (by simp [b32]) run_b32
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b33_in_code (by simp [b33]) run_b33 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat8 hts8 hcl8 hcw8 hf8 hfw8 (fit_size hz8 hfit) hmod8
    fun st9 s9 c9 hat9 hts9 hcl9 hcw9 hf9 hfw9 hsz9 hmod9 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b32_next, NativeRustcVmX64.Vm.VerifyKeccak.b33_next] at hat9
  have hz9 := hsz9.trans hz8
  refine layerStep hp hpre hvl (j := 9) (by decide) b34_in_code (by simp [b34]) run_b34
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b35_in_code (by simp [b35]) run_b35 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat9 hts9 hcl9 hcw9 hf9 hfw9 (fit_size hz9 hfit) hmod9
    fun st10 s10 c10 hat10 hts10 hcl10 hcw10 hf10 hfw10 hsz10 hmod10 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b34_next, NativeRustcVmX64.Vm.VerifyKeccak.b35_next] at hat10
  have hz10 := hsz10.trans hz9
  refine layerStep hp hpre hvl (j := 10) (by decide) b36_in_code (by simp [b36]) run_b36
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b37_in_code (by simp [b37]) run_b37 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat10 hts10 hcl10 hcw10 hf10 hfw10
    (fit_size hz10 hfit) hmod10
    fun st11 s11 c11 hat11 hts11 hcl11 hcw11 hf11 hfw11 hsz11 hmod11 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b36_next, NativeRustcVmX64.Vm.VerifyKeccak.b37_next] at hat11
  have hz11 := hsz11.trans hz10
  refine layerStep hp hpre hvl (j := 11) (by decide) b38_in_code (by simp [b38]) run_b38
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) b39_in_code (by simp [b39]) run_b39 (by decide) (by decide) (by decide)
    (by decide) rfl rfl (by decide) hat11 hts11 hcl11 hcw11 hf11 hfw11
    (fit_size hz11 hfit) hmod11
    fun st12 s12 c12 hat12 hts12 hcl12 hcw12 hf12 hfw12 hsz12 hmod12 ↦ ?_
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b38_next, NativeRustcVmX64.Vm.VerifyKeccak.b39_next] at hat12
  have hz12 := hsz12.trans hz11
  exact cont st12 s12 c12 hat12 hts12 hcl12 hcw12 hf12 hfw12 hz12 (hmod12.trans (by
    rw [show (11 + 1 : Nat) = keccakDepth from rfl, afterLayers_end]))

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
