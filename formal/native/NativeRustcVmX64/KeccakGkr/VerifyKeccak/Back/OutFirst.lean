module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OutStep
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names

/-! # Resetting the final point and appending its four low coordinates (blocks 66–67) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem outFirstStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} {low : Array EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b66Offset wrAll t60 (vv m0 V) st)
    (hlow : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 168) low.toList)
    (h4 : low.size = 4) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b68Offset wrAll t60 (vv m0 V) st' →
      NativeRustcVm.BufEWAt st'.data.dmem (keccakOutArg m0) 36 low.toList →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [(4, 0, 584)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hm : ∀ ret, Match (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret) t66 st.data := by
    intro ret
    apply (hat.2.mt ret).withAlias
    change (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret).load 0 3360 8 =
      keccakOutArg m0 + BitVec.ofInt 64 0
    rw [argLoad c hat.2.same (i := 1) (by decide),
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    rfl
  have ho := fun ret ↦ argLoad c hat.2.same (vals := vv m0 V) (ret := ret) (i := 1) (by decide)
  refine stepHeader (T' := t60) (vals' := vv m0 V) hp c h hat b66_in_code (by simp [b66])
    run_b66 hm (by decide) (oc := 48) (by decide) rfl hext (Sk := bufEWExtendStack)
    (by rw [vk_eq]; decide) (fun mc hmc ca hsk hch hkk ↦ ?_)
    (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) rfl rfl rfl (by vtacC) rfl rfl
    rfl rfl rfl rfl rfl fun st1 hat1 ⟨mc, hmc, hq, hch⟩ hc1 hk1 ↦ ?_
  · have rdi : reg mc .rdi = keccakOutArg m0 := (hmc.regs .rdi _ rfl).trans (ho _)
    have rsi : reg mc .rsi = off (fb m0) 168 := (hmc.regs .rsi _ rfl).trans (ev_frame 168)
    have rdx : reg mc .rdx = 4#64 := hmc.regs .rdx _ rfl
    have hz : NativeRustcVm.WordAt mc.dmem (keccakOutArg m0) 0 := by
      simpa only [off0, Sym.eval, UInt64.ofBitVec_ofNat] using
        (wordAt_write hmc (r := 4) (o := 0) (b := keccakOutArg m0) (sz := 1608)
          rfl (by decide) (v := .lit 0) (by decide))
    unfold BufEWExtendPre
    rw [rdi, rsi, rdx, NativeRustcVm.wordOf_of_wordAt hz]
    refine ⟨hsk, by decide, ?_, ⟨mapF h ca (by decide), nwF c (by decide)⟩,
      ?_, ?_, ?_⟩
    · simpa only [off0, ob] using (show Readable mc (off (ob m0 4) 0) 584 from
        ⟨mapR h ca (by decide) (by decide) (by decide), nwR c (by decide) (by decide) (by decide)⟩)
    · have hs := (sepFX c (o := 168) (n := 64) (by decide) c.oS).symm
      change Sep (keccakOutArg m0).toNat 584 (off (fb m0) 168).toNat 64
      unfold Sep at hs ⊢
      omega
    · exact sep_stk' (stk_callee c ca (by rw [vk_eq]; decide)) (by
        have ho := c.oS
        unfold Sep at ho ⊢
        omega)
    · exact (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm
  · have rdi : reg mc .rdi = off (ob m0 4) 0 :=
      ((hmc.regs .rdi _ rfl).trans (ho _)).trans (off0 _).symm
    obtain ⟨-, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim
      (fun h ↦ .inr (inR_reg rdi List.mem_cons_self h)) .inl) hsv
  have rdi : reg mc .rdi = keccakOutArg m0 := (hmc.regs .rdi _ rfl).trans (ho _)
  have rsi : reg mc .rsi = off (fb m0) 168 := (hmc.regs .rsi _ rfl).trans (ev_frame 168)
  have rdx : reg mc .rdx = 4#64 := hmc.regs .rdx _ rfl
  have hz : NativeRustcVm.WordAt mc.dmem (keccakOutArg m0) 0 := by
    simpa only [off0, Sym.eval, UInt64.ofBitVec_ofNat] using
      (wordAt_write hmc (r := 4) (o := 0) (b := keccakOutArg m0) (sz := 1608)
        rfl (by decide) (v := .lit 0) (by decide))
  have hbuf : NativeRustcVm.BufEWAt mc.dmem (keccakOutArg m0) 36 [] :=
    ⟨by decide, hz, by simp [NativeRustcVm.EWsAt, NativeRustcVm.BytesAt]⟩
  have he := Chg.ewsF c hch (by decide) (by decide)
    (by rw [Array.length_toList, h4]; decide) (by rw [Array.length_toList, h4]; decide) hlow
  obtain ⟨hres, -, -⟩ := hq
  rw [rdi, rsi, rdx, NativeRustcVm.wordOf_of_wordAt hz, bufEWOf_of hbuf (by decide),
    slice_of he (by simp [h4])] at hres
  simp only [show (0 : UInt64).toNat + (4#64).toNat ≤ 36 from by decide, ↓reduceIte,
    List.nil_append] at hres
  obtain ⟨hal, hbuf1⟩ := hres
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b66_next] at hat1
  refine stepJ (T' := t60) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b67Offset) hp c h hat1 b67_in_code
    (by simp [b67]) run_b67 nofun (hat1.2.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [alCond] at hpc2
  have h1 : (reg st1.data .rax).toNat % 256 = 1 := hal
  simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0).regs .rax =
    reg st1.data .rax from rfl, h1, show ¬(1 = 0) from by decide, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc2
  refine cont st2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b67_next]), hB2⟩
    (NativeRustcVm.Layout.BufEWAt.of_same hbuf1
      (by simpa only [off0, ob] using
        (Chg.regS c hc2 (by decide) rfl (i := 4) (o := 0) (n := 584)
          (by decide) (by decide) rfl (by decide)))
      (by decide)) ?_ (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
  exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
