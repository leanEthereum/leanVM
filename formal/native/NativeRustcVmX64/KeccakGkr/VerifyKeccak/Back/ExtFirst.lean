module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Inst
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names

/-!
# The output claim's first extension

Blocks 47–48 reset the frame buffer and append the first four instance coordinates, or all
coordinates when the instance is shorter.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem extFirstStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {st : MachineState} {V : Vs} (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b47Offset wrA t45 (vv m0 V) st)
    {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b49Offset wrA t45 (vv m0 V) st' →
      NativeRustcVm.BufEWAt st'.data.dmem (off (fb m0) 408) 36 (inst.toList.take 4) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 152), (408, 584), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have hsize : inst.size = (reg m0 .rcx).toNat := hpre.2.2.2.2.2.2.2.2.1
  have hi : NativeRustcVm.EWsAt m0.dmem (reg m0 .rdx) inst.toList :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have hi0 := instAt_bound c hat.2 hi
  refine extStep (T' := t45) hp hpre hext b47_in_code (by simp [b47]) run_b47
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) rfl rfl rfl
    rfl rfl (by decide) rfl rfl rfl rfl rfl b48_in_code (by simp [b48]) run_b48
    (by decide) (by decide) (by decide) (by decide) rfl rfl (by decide) hat
    (Sr := reg m0 .rdx) (n := min inst.size 4) (xs := []) (ys := inst.toList.take 4)
    (fun mc hmc ↦ hmc.regs .rsi _ rfl) (fun mc hmc ↦ ?_) (fun mc hmc hch ↦ ?_)
    (fun mc hmc ca ↦ ?_) (by simp) ?_
  · change (mc.regs.get64 .rdx).toNat = _
    rw [hmc.regs .rdx _ rfl]
    change (min4S.eval (Env.ofMachine m0 [])).toNat = _
    rw [min4_value hsize, ofNat_toNat (by omega)]
  · refine ⟨⟨by decide, ?_, ?_⟩, (Chg.instAt c hch (by decide) rfl hi0).take 4, ?_⟩
    · exact wordAt_write hmc (r := 0) (o := 408) (b := fb m0) (sz := 3368)
        rfl (by decide) (v := .lit 0) (by decide)
    · simp [NativeRustcVm.EWsAt, NativeRustcVm.BytesAt]
    · simp [List.length_take, Nat.min_comm]
  · simpa only [Nat.mul_zero, off0] using
      inst_slice_footprint c ca (j := 0) (n := min inst.size 4) (by omega)
        (by simpa using BitVec.isLt (reg m0 .rdx))
  · intro st' hat' hbuf hchg hkept
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b47_next, NativeRustcVmX64.Vm.VerifyKeccak.b48_next] at hat'
    exact cont st' hat' hbuf hchg hkept

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
