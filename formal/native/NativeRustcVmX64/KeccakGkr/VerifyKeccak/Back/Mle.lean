module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.MathCall
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names

/-! # Evaluating the last claim's instance weights (block 61) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off ClaimAt)

public section

@[expose] def Ve (V : Vs) (v : EW) : Vs := { V with e0 := v.c0.toBitVec, e1 := v.c1.toBitVec }

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem mleStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {st : MachineState} {V : Vs} {cl : KeccakClaimW} {low : Array EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b61Offset wrAll t60 (vv m0 V) st)
    (hcl : ClaimAt st.data.dmem (off (fb m0) 992) cl)
    (hlow : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 168) low.toList)
    (h4 : low.size = 4) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b62Offset wrAll t61 (vv m0 (Ve V (multilinearEval cl.mu low))) st' →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  obtain ⟨h16, hw, hmu⟩ := ClaimAt.muAt hcl
  rw [koff] at hw hmu
  have hl := fun ret ↦ ld_frame (rs := rsOf m0) (vals := vv m0 V) (ret := ret) hw
  have h17 : ∀ ret, ((Sym.load 0 1008 8).eval
      (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret)).toNat < 17 := by
    intro ret
    change ((envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 V) ret).load 0 1008 8).toNat < 17
    rw [hl, UInt64.toNat_toBitVec, toUInt64_toNat_of (by omega)]
    omega
  refine stepC (T' := t61) (vals' := vv m0 (Ve V (multilinearEval cl.mu low))) hp c h hat
    b61_in_code (by simp [b61]) run_b61 hat.2.mt (by decide) (oc := 48) (by decide) rfl
    (mleCall hmle cl.mu low) (Sk := mleStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := []) (Oc := [])
    (fun mc m' hmc hq ↦ chgQ (changes_zero hq.2.1) (fun _ h ↦ .inl h) hq.2.2)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi mc m' hmc hq ↦ by
      cases tregE (rfl : t61.reg .rax = some (.var 30)) hi
      exact ewRet_lo hq.1)
    (fun i hi mc m' hmc hq ↦ by
      cases tregE (rfl : t61.reg .rdx = some (.var 31)) hi
      exact ewRet_hi hq.1)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st' hpc' hB' _ hc' hk' ↦ ?_
  · have ca : CallAt m0 wrAll 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = cl.mu.size.toUInt64.toBitVec := by
      change mc.regs.get64 .rdi = _
      rw [hmc.regs .rdi _ rfl, eval_ite_ult_pos _ _ _ (by decide) (h17 _)]
      exact hl _
    have rdx : reg mc .rdx = cl.mu.size.toUInt64.toBitVec := by
      change mc.regs.get64 .rdx = _
      rw [hmc.regs .rdx _ rfl, eval_ite_ult_pos _ _ _ (by decide) (h17 _)]
      exact hl _
    have rsi : reg mc .rsi = off (fb m0) 1016 := by
      change mc.regs.get64 .rsi = _
      rw [hmc.regs .rsi _ rfl, eval_ite_ult_pos _ _ _ (by decide) (h17 _)]
      exact ev_frame 1016
    have rcx : reg mc .rcx = off (fb m0) 168 := (hmc.regs .rcx _ rfl).trans (ev_frame 168)
    have r8 : reg mc .r8 = 4#64 := hmc.regs .r8 _ rfl
    have hn : cl.mu.size.toUInt64.toBitVec.toNat = cl.mu.size := by
      rw [UInt64.toNat_toBitVec, toUInt64_toNat_of (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · unfold MleOfMultilinearEvalPre SliceOk
      rw [rdi, rdx, rsi, rcx, r8, hn]
      exact ⟨hsk, rfl, by decide,
        ⟨⟨mapF h ca (by omega), nwF c (by omega)⟩,
          (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm⟩,
        ⟨⟨mapF h ca (by decide), nwF c (by decide)⟩,
          (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm⟩⟩
    · rw [rsi, rdx]
      have he := Chg.ewsF c hch (by decide) rfl
        (by simp only [Array.length_toList, missL, wsL]; simp; omega)
        (by simp; omega) hmu
      simpa using slice_of he (by simpa using hn)
    · rw [rcx, r8]
      have he := Chg.ewsF c hch (by decide) rfl
        (by rw [Array.length_toList, h4]; decide) (by rw [Array.length_toList, h4]; decide) hlow
      simpa using slice_of he (by simp [h4])
  · refine cont st' ⟨hpc'.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b61_next]), hB'⟩ ?_ hk'
    exact Chg.mono c hc' (by decide) rfl (by decide) rfl (by decide) rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
