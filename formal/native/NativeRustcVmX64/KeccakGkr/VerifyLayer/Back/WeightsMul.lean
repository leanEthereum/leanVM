module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.WeightsRead
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-! # The two multiplications in one layer-weight iteration -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (DecArea off)
open LeanVM.Protocol.Verifier

@[expose] public section

structure WMul (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch b : EW)
    (pt lp t : Array EW) (s6 : TState) (j : Nat) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  mem : WMem m0 a c ch b pt lp t s6 j d.dmem
  rbp : reg d .rbp = BitVec.ofNat 64 j
  rbx : reg d .rbx = BitVec.ofNat 64 (16 * j)
  w32 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 32) ((eqKernel lp).getD j 0).c1
  w48 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 48) ((eqKernel lp).getD j 0).c0
  value : ewArg (reg d .rax) (reg d .rdx) =
    b * ((eqKernel lp).getD (keccakAlong j 4) 0 + b * (eqKernel lp).getD (keccakAlong j 3) 0)

end

public section

variable [Host] {m0 : MachineData} {a : DecArea} {s s6 : TState} {c : KeccakClaimW}
  {ch b : EW} {pt lp t : Array EW} {j k : Nat}

theorem weights_mul (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpt : pt.size ≤ 30) (hlp : lp.size = 11)
    {d : MachineData} (h : WHead m0 a c ch b pt lp t s6 j d)
    (h14 : reg d .r14 = ((eqKernel lp).getD (keccakAlong j 4) 0).c0.toBitVec)
    (h12 : reg d .r12 = ((eqKernel lp).getD (keccakAlong j 4) 0).c1.toBitVec)
    (he3 : ewArg (reg d .rdx) (reg d .rcx) = (eqKernel lp).getD (keccakAlong j 3) 0)
    {R : MachineState → Prop}
    (cont : ∀ d', WMul m0 a c ch b pt lp t s6 j d' →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b73Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset)⟩ := by
  have g := geo_of hpre
  have cx := ctx hpre (F := 2000) (by decide)
  have hWo := wFront_outs hpre
  have hw80 := h.mem.fw (80, .ofBitVec (sA m0)) (by apply List.mem_append_left; fw_mem)
  have hw24 := h.mem.fw (24, b.c0) (by apply List.mem_append_left; fw_mem)
  have hw40 := h.mem.fw (40, b.c1) (by apply List.mem_append_left; fw_mem)
  have hwf := wfScratch hpre h.body (p := 107520 + 16 * j) (n := 16)
    (by have := h.lt; omega) (by have := h.lt; omega)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length)).toBitVec)
  have hal1 : a71a.eval (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * j), 16)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length)).toBitVec) =
      sA m0 + BitVec.ofNat 64 (107520 + 16 * j) + BitVec.ofInt 64 (-107520) := by
    change BinOp.apply .add .W64 (reg d .r15) (reg d .rbx) = _
    rw [add64, h.r15, h.rbx]
    bv_omega
  have hal2 : a71b.eval (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * j), 16)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length)).toBitVec) =
      sA m0 + BitVec.ofNat 64 (107520 + 16 * j) + BitVec.ofInt 64 (-107520) := by
    simp only [a71b, Sym.eval]
    rw [fload8 hw80, add64]
    change sA m0 + reg d .rbx = _
    rw [h.rbx]
    bv_omega
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (107520 + 16 * j), 16)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length)).toBitVec)
      (fr 24 [16] [] [] [(a71a, 1, -107520), (a71b, 1, -107520)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial ⟨hal1, hal2, trivial⟩
  have hj := h.lt
  have hl := scratchLoads (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length)).toBitVec) h.mem.eq
    (i := j) (by rw [NativeVm.Math.Keccak.eqKernel_size, hlp]; omega)
  refine Body.blk (o' := 16) g h.body hwf (blk hp b71_in_code (by simp [b71])) e71
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hm1' := h.mem.blk hpre hpt hlp (by omega) hwf hm1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hw32 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 32)
      ((eqKernel lp).getD j 0).c1 := fwW hm1 (o := 32) (v := .load 1 8 8)
        rfl rfl (by decide) (by decide +kernel) hl.2
  have hw48 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 48)
      ((eqKernel lp).getD j 0).c0 := fwW hm1 (o := 48) (v := .load 1 0 8)
        rfl rfl (by decide) (by decide +kernel) hl.1
  have hA1 : ewArg (reg st.data .rdi) (reg st.data .rsi) = b := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    simp only [Sym.eval]
    rw [fload8 hw24, fload8 hw40, ewArg_ew]
  have hB1 : ewArg (reg st.data .rdx) (reg st.data .rcx) = (eqKernel lp).getD (keccakAlong j 3) 0 := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    exact he3
  have h15_1 := (hm1.regs .r15 _ rfl).trans (fload8 hw24)
  have h13_1 := (hm1.regs .r13 _ rfl).trans (fload8 hw40)
  have h14_1 := (hm1.regs .r14 _ rfl).trans h14
  have h12_1 := (hm1.regs .r12 _ rfl).trans h12
  have hbp1 := (hm1.regs .rbp _ rfl).trans h.rbp
  have hbx1 := (hm1.regs .rbx _ rfl).trans h.rbx
  refine leafX hpre hWo (Sk := ewMulStack) (by decide) hmul
    (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hpc1 hb1
    (cx.stackOk (hb1.at_ hpre hWo (by decide)) (by decide))
    fun d2 hq2 hb2 hf2 ht2 hc2 hs2 ↦ ?_
  have hm2 := hm1'.leaf hpre hpt hlp (by omega) hb1 hf2 (ht2 _ hm1'.ts) (by decide) hs2
  have hp2 := mulE hq2
  rw [hA1, hB1] at hp2
  have h15_2 := (hc2 .r15 rfl).trans h15_1
  have h13_2 := (hc2 .r13 rfl).trans h13_1
  have h14_2 := (hc2 .r14 rfl).trans h14_1
  have h12_2 := (hc2 .r12 rfl).trans h12_1
  have hbp2 := (hc2 .rbp rfl).trans hbp1
  have hbx2 := (hc2 .rbx rfl).trans hbx1
  have hw32_2 := (hf2.sub (o' := 32) (n' := 8) (by decide) (by decide)).word hw32 (by decide)
  have hw48_2 := (hf2.sub (o' := 48) (n' := 8) (by decide) (by decide)).word hw48 (by decide)
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b71Offset + b71.length = k + NativeRustcVmX64.Vm.VerifyLayer.b72Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b71_next]]
  have hwf3 := wf0 (pre_stack hpre) hb2 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b72Offset + b72.length)).toBitVec)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b72Offset + b72.length)).toBitVec)
      (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hb2 hwf3 (blk hp b72_in_code (by simp [b72])) e72
    (fun _ _ ↦ rfl) hm3 (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  have hm4' := hm2.blk hpre hpt hlp (by omega) hwf3 hm4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hf4 := frSame_blk (o := 24) (n := 1944) hwf3 hm4 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hA4 : ewArg (reg st3.data .rdi) (reg st3.data .rsi) = b := by
    rw [show reg st3.data .rdi = _ from hm4.regs .rdi _ rfl,
      show reg st3.data .rsi = _ from hm4.regs .rsi _ rfl]
    change ewArg (reg d2 .r15) (reg d2 .r13) = _
    rw [h15_2, h13_2, ewArg_ew]
  have hB4 : ewArg (reg st3.data .rdx) (reg st3.data .rcx) =
      (eqKernel lp).getD (keccakAlong j 4) 0 + b * (eqKernel lp).getD (keccakAlong j 3) 0 := by
    rw [show reg st3.data .rdx = _ from hm4.regs .rdx _ rfl,
      show reg st3.data .rcx = _ from hm4.regs .rcx _ rfl]
    simp only [Sym.eval, NativeRustcVmX64.Arrays.xor_eval]
    rw [NativeRustcVmX64.Arrays.ewArg_xor]
    change ewArg (reg d2 .r14) (reg d2 .r12) + ewArg (reg d2 .rax) (reg d2 .rdx) = _
    rw [h14_2, h12_2, ewArg_ew, hp2]
  have hbp4 := (hm4.regs .rbp _ rfl).trans hbp2
  have hbx4 := (hm4.regs .rbx _ rfl).trans hbx2
  refine leafX hpre hWo (Sk := ewMulStack) (by decide) hmul
    (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hpc4 hb4
    (cx.stackOk (hb4.at_ hpre hWo (by decide)) (by decide))
    fun d5 hq5 hb5 hf5 ht5 hc5 hs5 ↦ ?_
  have hm5 := hm4'.leaf hpre hpt hlp (by omega) hb4 hf5 (ht5 _ hm4'.ts) (by decide) hs5
  have hp5 := mulE hq5
  rw [hA4, hB4] at hp5
  have hfAll := hf4.trans (hf5.sub (by decide) (by decide))
  exact cont d5 ⟨hb5, hm5, (hc5 .rbp rfl).trans hbp4, (hc5 .rbx rfl).trans hbx4,
    (hfAll.sub (o' := 32) (n' := 8) (by decide) (by decide)).word hw32_2 (by decide),
    (hfAll.sub (o' := 48) (n' := 8) (by decide) (by decide)).word hw48_2 (by decide), hp5⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
