module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Dot
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-! # Multiplication and the final two-limb equality check (blocks 63–65) -/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

theorem checkStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {V : Vs} {x y v : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b63Offset wrAll t62 (vv m0 V) st)
    (he0 : V.e0 = x.c0.toBitVec) (he1 : V.e1 = x.c1.toBitVec)
    (hd0 : V.d0 = y.c0.toBitVec) (hd1 : V.d1 = y.c1.toBitVec)
    (hf0 : V.f0 = v.c0.toBitVec) (hf1 : V.f1 = v.c1.toBitVec)
    (hfail : (x * y == v) = false →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s = none)
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b66Offset wrAll t60 (vv m0 V) st' → (x * y == v) = true →
      Chg m0 st.data.dmem st'.data.dmem [(0, 88), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st') :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  refine stepC (T' := t60) (vals' := vv m0 V) hp c h hat b63_in_code (by simp [b63])
    run_b63 hat.2.mt (by decide) (oc := 48) (by decide) rfl hmul (Sk := ewMulStack)
    (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ hsk)
    (Lc := []) (Oc := []) (fun mc m' hmc hq ↦ chgQ hq.2.2.1 (fun _ h ↦ .inl h) hq.2.2.2)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t60.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t60.reg .rdx = some (.reg .rdx)) hi)
    rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, _⟩ hc1 hk1 ↦ ?_
  have rdi : reg mc .rdi = x.c0.toBitVec := (hmc.regs .rdi _ rfl).trans he0
  have rsi : reg mc .rsi = x.c1.toBitVec := (hmc.regs .rsi _ rfl).trans he1
  have rdx : reg mc .rdx = y.c0.toBitVec := (hmc.regs .rdx _ rfl).trans hd0
  have rcx : reg mc .rcx = y.c1.toBitVec := (hmc.regs .rcx _ rfl).trans hd1
  obtain ⟨hax, hdx, -, -⟩ := hq
  rw [rdi, rsi, rdx, rcx, ew_mk, ew_mk] at hax hdx
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b63_next] at hpc1
  refine stepJ (T' := t60) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b64Offset) hp c h ⟨hpc1, hB1⟩ b64_in_code
    (by simp [b64]) run_b64 nofun (hB1.mt 0) (by decide) rfl rfl (by vtacJ)
    (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st2 hpc2 hB2 hm2 hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [eval_ne64, show (Sym.reg .rax).eval (envZ m0 st1.data 3344 3368 (rsOf m0)
    (vv m0 V) 0) = (x * y).c0.toBitVec from hax,
    show (Sym.var 27).eval (envZ m0 st1.data 3344 3368 (rsOf m0) (vv m0 V) 0) =
      v.c0.toBitVec from hf0, beq_toBitVec] at hpc2
  by_cases heq0 : (x * y).c0 = v.c0
  · simp only [heq0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    rw [NativeRustcVmX64.Vm.VerifyKeccak.b64_next] at hpc2
    have hdx2 : reg st2.data .rdx = (x * y).c1.toBitVec := (hm2.regs .rdx _ rfl).trans hdx
    refine stepJ (T' := t60) (vals' := vv m0 V) (o := NativeRustcVmX64.Vm.VerifyKeccak.b65Offset) hp c h ⟨hpc2, hB2⟩ b65_in_code
      (by simp [b65]) run_b65 nofun (hB2.mt 0) (by decide) rfl rfl (by vtacJ)
      (by decide) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
      fun st3 hpc3 hB3 _ hc3 hk3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [eval_ne64, show (Sym.reg .rdx).eval (envZ m0 st2.data 3344 3368 (rsOf m0)
      (vv m0 V) 0) = (x * y).c1.toBitVec from hdx2,
      show (Sym.var 28).eval (envZ m0 st2.data 3344 3368 (rsOf m0) (vv m0 V) 0) =
        v.c1.toBitVec from hf1, beq_toBitVec] at hpc3
    by_cases heq1 : (x * y).c1 = v.c1
    · simp only [heq1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
      refine cont st3 ⟨hpc3.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b65_next]), hB3⟩
        (by rw [ew_beq, heq0, heq1, beq_self_eq_true, beq_self_eq_true, Bool.and_self]) ?_
        (NativeRustcVmX64.Transcript.kept_trans hk1 (NativeRustcVmX64.Transcript.kept_trans hk2 hk3))
      exact Chg.mono c (hc1.trans (hc2.trans hc3)) (by decide) rfl (by decide) rfl (by decide) rfl
    · simp only [beq_false_of_ne heq1, Bool.not_false, ↓reduceIte] at hpc3
      exact failG hp hpre hB3 hpc3 (by decide) (hfail (by
        rw [ew_beq, heq0, beq_self_eq_true, Bool.true_and]; exact beq_false_of_ne heq1))
  · simp only [beq_false_of_ne heq0, Bool.not_false, ↓reduceIte] at hpc2
    exact failG hp hpre hB2 hpc2 (by decide) (hfail (by
      rw [ew_beq, beq_false_of_ne heq0, Bool.false_and]))

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
