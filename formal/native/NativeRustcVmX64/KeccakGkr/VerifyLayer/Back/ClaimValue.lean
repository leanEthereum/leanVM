module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Transpose
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-! # Computing the new claim's value -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea)

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {k : Nat}

theorem claim_value (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hpt : pt.size ≤ 30)
    {d : MachineData} (hb : Body m0 (outs m0) 24 d) (h : TailLive m0 a c ch b pt lp t s6 d.dmem)
    {R : MachineState → Prop}
    (cont : ∀ d', Body m0 (outs m0) 24 d' → TailLive m0 a c ch b pt lp t s6 d'.dmem →
      ewArg (reg d' .rax) (reg d' .rdx) = b * (t.getD 1 0 + b * t.getD 2 0) →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b82Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b80Offset)⟩ := by
  have g := geo_of hpre
  have cx := ctx hpre (F := 2000) (by decide)
  have hw24 := h.fw (24, b.c0) (by apply List.mem_append_left; fw_mem)
  have hw40 := h.fw (40, b.c1) (by apply List.mem_append_left; fw_mem)
  have hw104 := h.fw (104, (t.getD 2 0).c1) (by apply List.mem_append_right; fw_mem)
  have hw112 := h.fw (112, (t.getD 2 0).c0) (by apply List.mem_append_right; fw_mem)
  have hwf := wf0 (pre_stack hpre) hb (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b80Offset + b80.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b80Offset + b80.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb hwf (blk hp b80_in_code (by simp [b80])) e80
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have h1 := h.blk hpre hpt hwf hm1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hbx1 := (hm1.regs .rbx _ rfl).trans (fload8 hw24)
  have h14_1 := (hm1.regs .r14 _ rfl).trans (fload8 hw40)
  have hA1 : ewArg (reg st.data .rdi) (reg st.data .rsi) = b := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    simp only [Sym.eval]
    rw [fload8 hw24, fload8 hw40, ewArg_ew]
  have hB1 : ewArg (reg st.data .rdx) (reg st.data .rcx) = t.getD 2 0 := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval]
    rw [fload8 hw112, fload8 hw104, ewArg_ew]
  refine leafX hpre (fun _ h ↦ h) (Sk := ewMulStack) (by decide) hmul
    (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hpc1 hb1
    (cx.stackOk (hb1.at_ hpre (fun _ h ↦ h) (by decide)) (by decide))
    fun d2 hq2 hb2 hf2 ht2 hc2 hs2 ↦ ?_
  have h2 := h1.leaf hpre hpt hb1 hf2 (ht2 _ h1.ts) (by decide) hs2
  have hm2 := mulE hq2
  rw [hA1, hB1] at hm2
  have hbx2 := (hc2 .rbx rfl).trans hbx1
  have h14_2 := (hc2 .r14 rfl).trans h14_1
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b80Offset + b80.length = k + NativeRustcVmX64.Vm.VerifyLayer.b81Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b80_next]]
  have hwf3 := wf0 (pre_stack hpre) hb2 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b81Offset + b81.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b81Offset + b81.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  have hw184 := h2.fw (184, (t.getD 1 0).c0) (by apply List.mem_append_right; fw_mem)
  have hw72 := h2.fw (72, (t.getD 1 0).c1) (by apply List.mem_append_right; fw_mem)
  refine Body.blk (o' := 16) g hb2 hwf3 (blk hp b81_in_code (by simp [b81])) e81
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  have h4 := h2.blk hpre hpt hwf3 hm4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hA4 : ewArg (reg st3.data .rdi) (reg st3.data .rsi) = b := by
    rw [show reg st3.data .rdi = _ from hm4.regs .rdi _ rfl,
      show reg st3.data .rsi = _ from hm4.regs .rsi _ rfl]
    change ewArg (reg d2 .rbx) (reg d2 .r14) = _
    rw [hbx2, h14_2, ewArg_ew]
  have hB4 : ewArg (reg st3.data .rdx) (reg st3.data .rcx) = t.getD 1 0 + b * t.getD 2 0 := by
    rw [show reg st3.data .rdx = _ from hm4.regs .rdx _ rfl,
      show reg st3.data .rcx = _ from hm4.regs .rcx _ rfl]
    simp only [Sym.eval, NativeRustcVmX64.Arrays.xor_eval]
    rw [fload8 hw184, fload8 hw72, NativeRustcVmX64.Arrays.ewArg_xor, ewArg_ew]
    exact congrArg (fun x ↦ t.getD 1 0 + x) hm2
  refine leafX hpre (fun _ h ↦ h) (Sk := ewMulStack) (by decide) hmul
    (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hpc4 hb4
    (cx.stackOk (hb4.at_ hpre (fun _ h ↦ h) (by decide)) (by decide))
    fun d5 hq5 hb5 hf5 ht5 hc5 hs5 ↦ ?_
  have h5 := h4.leaf hpre hpt hb4 hf5 (ht5 _ h4.ts) (by decide) hs5
  have hm5 := mulE hq5
  rw [hA4, hB4] at hm5
  exact cont d5 hb5 h5 hm5

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
