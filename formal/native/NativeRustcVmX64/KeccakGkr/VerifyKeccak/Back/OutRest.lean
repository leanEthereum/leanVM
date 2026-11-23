module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.OutExtend
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names

/-! # Appending the pack point and opening slot (blocks 68–70) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off ClaimAt)

public section

theorem pack_nat [Labels] (m : MachineData) :
    (packS.eval (Env.ofMachine m [])).toNat = (reg m .rsi).toNat - 4 := by
  unfold packS
  rw [eval_ite_ult _ _ _ (by decide)]
  change (if (reg m .rsi).toNat < 4 then 0#64 else
    BinOp.apply .sub .W64 (reg m .rsi) 4#64).toNat = _
  split
  · rename_i h
    change 0 = _
    omega
  · rename_i h
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub]
    have := BitVec.isLt (reg m .rsi)
    simp only [show (4#64).toNat = 4 from rfl]
    omega

theorem cmp64 (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [CmpOp.apply, low_W64]
  rw [BitVec.ult_iff_lt, BitVec.lt_def]

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem outHighStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} {low : Array EW} {cl : KeccakClaimW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b68Offset wrAll t60 (vv m0 V) st)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (keccakOutArg m0) 36 low.toList)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (h4 : low.size = 4) (hfit : SegmentsFit (reg m0 .rsi).toNat cl)
    (hpl : V.pl = BitVec.ofNat 64 cl.point.size) (hpp : V.pp = off (fb m0) 1280)
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b70Offset wrAll t69 (vv m0 V) st' →
      NativeRustcVm.BufEWAt st'.data.dmem (keccakOutArg m0) 36
        (low.toList ++ cl.point.toList.take ((reg m0 .rsi).toNat - 4)) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [(4, 0, 584)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  obtain ⟨h30, -, hpt⟩ := ClaimAt.pointAt hcl
  rw [koff] at hpt
  have hn : (reg m0 .rsi).toNat - 4 < cl.point.size := hfit.1
  have hcmp : ∀ ret, (SBool.cmp .ult .W64 (.var 12) (.var 25)).eval
      (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret) = true := by
    intro ret
    change CmpOp.apply .ult .W64 (packS.eval (Env.ofMachine m0 [])) V.pl = true
    rw [cmp64, hpl, pack_nat, ofNat_toNat (by omega)]
    exact decide_eq_true hn
  refine outExtendStep (T' := t69) hp hpre hext b68_in_code (by simp [b68]) run_b68
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
    rfl rfl (by decide) rfl rfl rfl rfl rfl hat hbuf
    (Sr := off (fb m0) 1280) (n := (reg m0 .rsi).toNat - 4)
    (ys := cl.point.toList.take ((reg m0 .rsi).toNat - 4))
    (fun mc hm ↦ (hm.regs .rsi _ rfl).trans hpp) (fun mc hm ↦ ?_)
    (fun mc hc ↦ ?_) (by simp; omega) (fun mc ca ↦ ?_) (by simp [h4]; omega)
    fun st1 hat1 hal hbuf1 hc1 hk1 ↦ ?_
  · change (mc.regs.get64 .rdx).toNat = _
    rw [hm.regs .rdx _ rfl]
    change (if (SBool.cmp .ult .W64 (.var 12) (.var 25)).eval _ then
      packS.eval (Env.ofMachine m0 []) else V.pl).toNat = _
    simp only [hcmp, ↓reduceIte, pack_nat]
  · exact (Chg.ewsF c hc (by decide) rfl
      (by simp only [Array.length_toList, missL, wsL]; simp; omega)
      (by simp; omega) hpt).take _
  · exact ⟨⟨mapF h ca (by omega), nwF c (by omega)⟩,
      (sepFX c (by omega) (by have ho := c.oS; unfold Sep at ho ⊢; omega)).symm,
      (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm⟩
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b68_next] at hat1
  refine stepJ (T' := t69) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b69Offset) hp c h hat1 b69_in_code
    (by simp [b69]) run_b69 nofun (hat1.2.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [alCond] at hpc2
  have h1 : (reg st1.data .rax).toNat % 256 = 1 := hal
  simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0).regs .rax =
    reg st1.data .rax from rfl, h1, show ¬(1 = 0) from by decide, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc2
  refine cont st2 ⟨hpc2.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b69_next]), hB2⟩
    (NativeRustcVm.Layout.BufEWAt.of_same hbuf1
      (by simpa only [off0, ob] using
        (Chg.regS c hc2 (by decide) rfl (i := 4) (o := 0) (n := 584)
          (by decide) (by decide) rfl (by decide)))
      (by decide)) ?_ (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
  exact Chg.mono c (hc1.trans hc2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem outSlotStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} {xs : List EW} {slot : Array EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b70Offset wrAll t69 (vv m0 V) st)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (keccakOutArg m0) 36 xs)
    (hslot : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 232) slot.toList)
    (h6 : slot.size = 6) (hfit : xs.length + 6 ≤ 36) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b71Offset wrAll t69 (vv m0 V) st' → boolRet st'.data = 1 →
      NativeRustcVm.BufEWAt st'.data.dmem (keccakOutArg m0) 36 (xs ++ slot.toList) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [(4, 0, 584)] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  refine outExtendStep (T' := t69) hp hpre hext b70_in_code (by simp [b70]) run_b70
    (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
    rfl rfl (by decide) rfl rfl rfl rfl rfl hat hbuf
    (Sr := off (fb m0) 232) (n := 6) (ys := slot.toList)
    (fun mc hm ↦ (hm.regs .rsi _ rfl).trans (ev_frame 232))
    (fun mc hm ↦ congrArg BitVec.toNat (hm.regs .rdx _ rfl))
    (fun mc hc ↦ Chg.ewsF c hc (by decide) rfl
      (by rw [Array.length_toList, h6]; decide) (by rw [Array.length_toList, h6]; decide) hslot)
    (by simpa using h6) (fun mc ca ↦ ?_) hfit ?_
  · exact ⟨⟨mapF h ca (by decide), nwF c (by decide)⟩,
      (sepFX c (by decide) (by have ho := c.oS; unfold Sep at ho ⊢; omega)).symm,
      (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm⟩
  · intro st' hat' hal hbuf' hc hk
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b70_next] at hat'
    exact cont st' hat' hal hbuf' hc hk

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
