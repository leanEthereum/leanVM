module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Mle
public import NativeRustcVmX64.Code.Vm.Dot.Names

/-! # Taking the dot product of the opening weights and slices (block 62) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

@[expose] def Vd (V : Vs) (v : EW) : Vs := { V with d0 := v.c0.toBitVec, d1 := v.c1.toBitVec }

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem dotStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    {st : MachineState} {V : Vs} {ws sl : Array EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b62Offset wrAll t61 (vv m0 V) st)
    (hw : NativeRustcVm.EWsAt st.data.dmem (off (reg m0 .r9) 140288) ws.toList)
    (hs : NativeRustcVm.EWsAt st.data.dmem (off (keccakOutArg m0) 584) sl.toList)
    (hw64 : ws.size = 64) (hs64 : sl.size = 64) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b63Offset wrAll t62 (vv m0 (Vd V (dot ws sl))) st' →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  refine stepC (T' := t62) (vals' := vv m0 (Vd V (dot ws sl))) hp c h hat
    b62_in_code (by simp [b62]) run_b62 hat.2.mt (by decide) (oc := 48) (by decide) rfl
    (dotCall hdot ws sl) (Sk := dotStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := []) (Oc := [])
    (fun mc m' hmc hq ↦ chgQ (changes_zero hq.2.1) (fun _ h ↦ .inl h) hq.2.2)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi mc m' hmc hq ↦ by
      cases tregE (rfl : t62.reg .rax = some (.var 33)) hi
      exact ewRet_lo hq.1)
    (fun i hi mc m' hmc hq ↦ by
      cases tregE (rfl : t62.reg .rdx = some (.var 34)) hi
      exact ewRet_hi hq.1)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st' hpc' hB' _ hc' hk' ↦ ?_
  · have ca : CallAt m0 wrAll 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (reg m0 .r9) 140288 := (hmc.regs .rdi _ rfl).trans (add64 _ _)
    have rdx : reg mc .rdx = off (keccakOutArg m0) 584 := (hmc.regs .rdx _ rfl).trans (add64 _ _)
    have rsi : reg mc .rsi = 64#64 := hmc.regs .rsi _ rfl
    have rcx : reg mc .rcx = 64#64 := hmc.regs .rcx _ rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold DotPre SliceOk
      rw [rdi, rdx, rsi, rcx]
      exact ⟨hsk,
        ⟨⟨mapR h ca (i := 2) (by decide) (by decide) (by decide),
            nwR c (i := 2) (by decide) (by decide) (by decide)⟩,
          sepRF c (i := 2) (by decide) (by decide) (by decide) (by decide)
            (stk_callee c ca (by rw [vk_eq]; decide))⟩,
        ⟨⟨mapR h ca (i := 4) (by decide) (by decide) (by decide),
            nwR c (i := 4) (by decide) (by decide) (by decide)⟩,
          sepRF c (i := 4) (by decide) (by decide) (by decide) (by decide)
            (stk_callee c ca (by rw [vk_eq]; decide))⟩⟩
    · rw [rdi, rsi]
      have he := Chg.ewsR c hch (by decide) rfl (i := 2) (o := 140288)
        (by decide) (by decide) rfl (by rw [Array.length_toList, hw64]; decide) hw
      simpa only [ob] using slice_of he (by simp [hw64])
    · rw [rdx, rcx]
      have he := Chg.ewsR c hch (by decide) rfl (i := 4) (o := 584)
        (by decide) (by decide) rfl (by rw [Array.length_toList, hs64]; decide) hs
      simpa only [ob] using slice_of he (by simp [hs64])
  · refine cont st' ⟨hpc'.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b62_next]), hB'⟩ ?_ hk'
    exact Chg.mono c hc' (by decide) rfl (by decide) rfl (by decide) rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
