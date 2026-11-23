module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.ExtFirst
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names

/-!
# The output claim's remaining coordinates

Blocks 49–52 append the remaining instance coordinates and the six opening-slot coordinates.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem extHighStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b49Offset wrA t45 (vv m0 V) st)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (off (fb m0) 408) 36 (inst.toList.take 4))
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b51Offset wrA t45 (vv m0 V) st' →
      NativeRustcVm.BufEWAt st'.data.dmem (off (fb m0) 408) 36 inst.toList →
      Chg m0 st.data.dmem st'.data.dmem [(0, 152), (408, 584), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have hsize : inst.size = (reg m0 .rcx).toNat := hpre.2.2.2.2.2.2.2.2.1
  have h30 : inst.size ≤ 30 := hpre.2.2.2.2.2.2.2.2.2.2.1
  have hi : NativeRustcVm.EWsAt m0.dmem (reg m0 .rdx) inst.toList :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hi0 := instAt_bound c hat.2 hi
  refine extStep (T' := t45) hp hpre hext b49_in_code (by simp [b49]) run_b49
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) rfl rfl rfl
    rfl rfl (by decide) rfl rfl rfl rfl rfl b50_in_code (by simp [b50]) run_b50
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) hat
    (Sr := rHighS.eval (Env.ofMachine m0 [])) (n := inst.size - 4)
    (xs := inst.toList.take 4) (ys := inst.toList.drop 4)
    (fun mc hmc ↦ hmc.regs .rsi _ rfl) (fun mc hmc ↦ ?_) (fun mc hmc hch ↦ ?_)
    (fun mc hmc ca ↦ high_footprint c ca hsize) (by simp; omega) ?_
  · change (mc.regs.get64 .rdx).toNat = _
    rw [hmc.regs .rdx _ rfl]
    change (hiS.eval (Env.ofMachine m0 [])).toNat = _
    rw [hi_value hsize, ofNat_toNat (by omega)]
  · refine ⟨NativeRustcVm.Layout.BufEWAt.of_same hbuf
      (Chg.frame c hch (n := 584) (by decide) rfl (by decide) (by decide)) (by decide),
      high_ews hsize (Chg.instAt c hch (by decide) rfl hi0), by simp⟩
  · intro st' hat' hbuf' hchg hkept
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b49_next, NativeRustcVmX64.Vm.VerifyKeccak.b50_next] at hat'
    rw [List.take_append_drop] at hbuf'
    exact cont st' hat' hbuf' hchg hkept

theorem extSlotStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} {slot : Array EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b51Offset wrA t45 (vv m0 V) st)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (off (fb m0) 408) 36 inst.toList)
    (hslot : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 232) slot.toList)
    (h6 : slot.size = 6) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b53Offset wrA t52 (vv m0 V) st' →
      NativeRustcVm.BufEWAt st'.data.dmem (off (fb m0) 408) 36 (inst.toList ++ slot.toList) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 152), (408, 584), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have h30 : inst.size ≤ 30 := hpre.2.2.2.2.2.2.2.2.2.2.1
  refine extStep (T' := t52) hp hpre hext b51_in_code (by simp [b51]) run_b51
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) rfl rfl rfl
    rfl rfl (by decide) rfl rfl rfl rfl rfl b52_in_code (by simp [b52]) run_b52
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) hat
    (Sr := off (fb m0) 232) (n := 6) (xs := inst.toList) (ys := slot.toList)
    (fun mc hmc ↦ (hmc.regs .rsi _ rfl).trans (ev_frame 232))
    (fun mc hmc ↦ congrArg BitVec.toNat (hmc.regs .rdx _ rfl))
    (fun mc hmc hch ↦ ?_) (fun mc hmc ca ↦ ?_) (by simp; omega) ?_
  · refine ⟨NativeRustcVm.Layout.BufEWAt.of_same hbuf
      (Chg.frame c hch (n := 584) (by decide) rfl (by decide) (by decide)) (by decide),
      Chg.ewsF c hch (by decide) rfl (by rw [Array.length_toList, h6]; decide)
        (by rw [Array.length_toList, h6]; decide) hslot, by simpa using h6⟩
  · exact ⟨⟨mapF h ca (by decide), nwF c (by decide)⟩,
      sepF0 c (by decide) (by decide) (by decide),
      (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm⟩
  · intro st' hat' hbuf' hchg hkept
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b51_next, NativeRustcVmX64.Vm.VerifyKeccak.b52_next] at hat'
    exact cont st' hat' hbuf' hchg hkept

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
