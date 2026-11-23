module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Sample
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `verify_stacked_opening`: the batching challenge (x86-64)

`sample_b20`: from `NativeRustcVmX64.Vm.VerifyStackedOpening.label_16` (`AtB20`), `b20` and `b22` check the count
(`placed + 2`, at most `162`: never too many), `b21` saves the `TState` and the Keccak output and
squeezes the challenge (`Parts.squeeze`), `b23` saves the claims and the rate: at
`NativeRustcVmX64.Vm.VerifyStackedOpening.label_19` (`b24`, `AtB24`). `sample_b3`: with no claim, `b3` saves the four
words and squeezes, `b4` sets the count `2`. Helpers: the `TState` across a block writing the
frame (`Ok.ts_block`), the frame's words `fwL` from five words (`fwL_of`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- The `TState` across a step writing the frame only. -/
theorem Ok.ts_block (h : Parts a s layout target coefficients point slices cs z value m0)
    {d d' : Mem 64} {s' : TState} (hts : TStateAt d (tA m0) a s') (hk : Keeps d d')
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (stackBelow m0 512) 512)) :
    TStateAt d' (tA m0) a s' :=
  hts.frame hk (fun _ hq ↦ h.frame_not_t (inRange_mono hq (by omega))) hs

omit [Labels] in
/-- The frame's words `fwL` from its five words. -/
theorem fwL_of {d : Mem 64}
    (h24 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 24) (UInt64.ofBitVec (tA m0)))
    (h40 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 40) (UInt64.ofBitVec (clA m0)))
    (h48 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 48) (UInt64.ofBitVec (reg m0 .rdx)))
    (h56 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 56) (UInt64.ofBitVec (reg m0 .r8)))
    (h64 : NativeRustcVm.WordAt d (off (stackBelow m0 512) 64) (UInt64.ofBitVec (reg m0 .rcx))) :
    FW d m0 (fwL m0) := fun p hp ↦ by
  simp only [fwL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact h24
  · exact h40
  · exact h48
  · exact h56
  · exact h64

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

section
variable (h : Parts a s layout target coefficients point slices cs z value m0)
  (hp : Placed code k)
  (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
include h hp hsq

omit hsq in
/-- **`b22`, `b23`** after the squeeze: the count checked, the claims and the rate saved. -/
theorem after_squeeze {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b22Offset))
    (hok : Ok m0 st.data 8) (hts : TStateAt st.data.dmem (tA m0) a (sq s).2)
    (hfw : FW st.data.dmem m0 [(24, UInt64.ofBitVec (tA m0)), (56, UInt64.ofBitVec (reg m0 .r8)),
      (64, UInt64.ofBitVec (reg m0 .rcx))])
    (hax : reg st.data .rax = (sq s).1.c0.toBitVec) (hdx : reg st.data .rdx = (sq s).1.c1.toBitVec)
    (hbx : (reg st.data .rbx).toNat = cntOf layout cs) (hbp : reg st.data .rbp = layA m0)
    (h12 : reg st.data .r12 = clA m0) (h13 : reg st.data .r13 = off (clA m0) 8)
    (h14 : reg st.data .r14 = reg m0 .rdx) (h15 : (reg st.data .r15).toNat = cs.size)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b24Offset) → AtB24 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hn := h.n_le
  have hP := placedOf_le_self (layout := layout) (cs := cs) cs.size
  refine h.run hp b22_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.wf0 h) hok.m_reg run_b22
    (o := 8) (by decide +kernel) (by decide) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hd1 := hm1.dmem_eq (hok.wf0 h) rfl
  simp only [PcOk] at hpc1
  rw [eval_gt _ (by decide)] at hpc1
  have hX : ((Sym.reg .rbx).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b22Offset + b22.length)).toBitVec)).toNat = cntOf layout cs := hbx
  rw [hX] at hpc1
  simp only [show ¬ (162 < cntOf layout cs) by unfold cntOf; omega, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc1
  refine h.run hp b23_in_code (List.cons_ne_nil _ _)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b22_next)) hok1 (vars := fun _ ↦ 0) (hok1.wf0 h) hok1.m_reg run_b23
    (o := 8) (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hfw2 := FW.block_os (hok1.wf0 h) hm2 rfl (by rw [hd1]; exact hfw) [24, 56, 64] rfl
    (by decide +kernel)
  have r : ∀ r : Reg64, r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r13, .r15] →
      reg st2.data r = reg st.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (regKeep hm2 _ rfl).trans (regKeep hm1 _ rfl)
  refine cont st2 (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b23_next))
    ⟨hok2, ?_, ?_, by rw [r .rax (by simp)]; exact hax, by rw [r .rdx (by simp)]; exact hdx,
      by rw [r .rbx (by simp)]; exact hbx, by rw [r .rbp (by simp)]; exact hbp,
      by rw [r .r13 (by simp)]; exact h13, by rw [r .r15 (by simp)]; exact h15⟩
  · exact Ok.ts_block h (Ok.ts_block h hts (hm1.kept (hok.wf0 h)) hs1) (hm2.kept (hok1.wf0 h)) hs2
  · have w40 := fw_write hm2 (o := 40) (by omega) (v := .reg .r12) (by decide +kernel)
    have w48 := fw_write hm2 (o := 48) (by omega) (v := .reg .r14) (by decide +kernel)
    have e12 : reg st1.data .r12 = clA m0 := (regKeep hm1 .r12 rfl).trans h12
    have e14 : reg st1.data .r14 = reg m0 .rdx := (regKeep hm1 .r14 rfl).trans h14
    refine fwL_of (hfw2.get (by simp)) ?_ ?_ (hfw2.get (by simp)) (hfw2.get (by simp))
    · rw [← e12]; exact w40
    · rw [← e14]; exact w48

/-- **The challenge** with claims: from `NativeRustcVmX64.Vm.VerifyStackedOpening.label_16` to `b24`. -/
theorem sample_b20 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b20Offset))
    (hA : AtB20 a s layout cs m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b24Offset) → AtB24 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hn := h.n_le
  have hP := placedOf_le_self (layout := layout) (cs := cs) cs.size
  have hc := hA.cb
  refine h.cbRun hp b20_in_code (List.cons_ne_nil _ _) hpc hc run_b20 (by decide +kernel) rfl
    (by decide +kernel) fun st1 hc1 hd1 hm1 hpc1 ↦ ?_
  have hX : ((Sym.bin .add .W64 (.lit 2) (.reg .rbx)).eval (frameEnv m0 st.data 512 []
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b20Offset + b20.length)).toBitVec)).toNat = cntOf layout cs := by
    rw [eval_add64]
    show (BitVec.ofNat 64 2 + reg st.data .rbx).toNat = _
    have h2 : (BitVec.ofNat 64 2).toNat = 2 := rfl
    rw [toNat_add_small (by rw [h2, hA.rbx]; omega), h2, hA.rbx]
    unfold cntOf
    omega
  have hbx1 : (reg st1.data .rbx).toNat = cntOf layout cs := by
    rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ rfl]; exact hX
  simp only [PcOk] at hpc1
  rw [eval_gt _ (by decide), hX] at hpc1
  simp only [show ¬ (512 < cntOf layout cs) by unfold cntOf; omega, decide_false,
    Bool.false_eq_true, ↓reduceIte] at hpc1
  have hok1 := hc1.ok
  refine h.run hp b21_in_code (List.cons_ne_nil _ _)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b20_next)) hok1 (vars := fun _ ↦ 0) (hok1.wf0 h) hok1.m_reg run_b21
    (o := 0) (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2 hpc2 ↦ ?_
  have hts2 := Ok.ts_block h hc1.ts (hm2.kept (hok1.wf0 h)) hs2
  have hfw2 : FW st2.data.dmem m0 [(24, UInt64.ofBitVec (tA m0)),
      (56, UInt64.ofBitVec (reg m0 .r8)), (64, UInt64.ofBitVec (reg m0 .rcx))] := by
    have w24 := fw_write hm2 (o := 24) (by omega) (v := .reg .rdi) (by decide +kernel)
    have w56 := fw_write hm2 (o := 56) (by omega) (v := .reg .r8) (by decide +kernel)
    have w64 := FW.block_os (L := [(64, UInt64.ofBitVec (reg m0 .rcx))]) (hok1.wf0 h) hm2 rfl
      (FW.cons hc1.ring (FW.nil _ _)) [64] rfl (by decide +kernel)
    refine FW.cons ?_ (FW.cons ?_ w64)
    · rw [← hc1.rdi]; exact w24
    · rw [← hc1.r8]; exact w56
  have hdi2 : reg st2.data .rdi = tA m0 := (regKeep hm2 .rdi rfl).trans hc1.rdi
  refine h.squeeze hsq hok2 hts2 hdi2 hpc2 fun st3 hpc3 hok3 hfs3 hts3 hax3 hdx3 hcs3 ↦ ?_
  have rr : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
    (hcs3 r hr).trans (regKeep hm2 r (by cases r <;> first | rfl | exact absurd hr (by decide)))
  exact after_squeeze h hp (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b21_next)) hok3 hts3
    (hfw2.call hfs3 (le_of_map [24, 56, 64] rfl (by decide))) hax3 hdx3 (by rw [rr .rbx rfl]; exact hbx1)
    (by rw [rr .rbp rfl]; exact hc1.rbp) (by rw [rr .r12 rfl]; exact hc1.r12)
    (by rw [rr .r13 rfl]; exact hc1.r13) (by rw [rr .r14 rfl]; exact hc1.r14)
    (by rw [rr .r15 rfl]; exact hc1.r15) cont

/-- **The challenge** with no claim: `b3`, the squeeze, `b4` (the count `2`) to `b24`. -/
theorem sample_b3 {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b3Offset))
    (hc : CB a s cs m0 st.data) (hz : cs.size = 0) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b24Offset) → AtB24 a s layout cs m0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hc.ok
  have hcnt : cntOf layout cs = 2 := by
    unfold cntOf placedOf
    rw [hz]
    simp
  refine h.run hp b3_in_code (List.cons_ne_nil _ _) hpc hok (vars := fun _ ↦ 0) (hok.wf0 h) hok.m_reg run_b3
    (o := 0) (by decide +kernel) (by decide) fun st2 hok2 hs2 hm2 hpc2 ↦ ?_
  have hts2 := Ok.ts_block h hc.ts (hm2.kept (hok.wf0 h)) hs2
  have w24 := fw_write hm2 (o := 24) (by omega) (v := .reg .rdi) (by decide +kernel)
  have w40 := fw_write hm2 (o := 40) (by omega) (v := .reg .r12) (by decide +kernel)
  have w48 := fw_write hm2 (o := 48) (by omega) (v := .reg .r14) (by decide +kernel)
  have w56 := fw_write hm2 (o := 56) (by omega) (v := .reg .r8) (by decide +kernel)
  have w64 := FW.block_os (L := [(64, UInt64.ofBitVec (reg m0 .rcx))]) (hok.wf0 h) hm2 rfl
    (FW.cons hc.ring (FW.nil _ _)) [64] rfl (by decide +kernel)
  have hfw2 : FW st2.data.dmem m0 (fwL m0) := by
    refine fwL_of ?_ ?_ ?_ ?_ (w64.get (by simp))
    · rw [← hc.rdi]; exact w24
    · rw [← hc.r12]; exact w40
    · rw [← hc.r14]; exact w48
    · rw [← hc.r8]; exact w56
  have hdi2 : reg st2.data .rdi = tA m0 := (regKeep hm2 .rdi rfl).trans hc.rdi
  refine h.squeeze hsq hok2 hts2 hdi2 hpc2 fun st3 hpc3 hok3 hfs3 hts3 hax3 hdx3 hcs3 ↦ ?_
  have rr : ∀ r, calleeSaved r = true → reg st3.data r = reg st.data r := fun r hr ↦
    (hcs3 r hr).trans (regKeep hm2 r (by cases r <;> first | rfl | exact absurd hr (by decide)))
  have hfw3 := hfw2.call hfs3 (le_of_map [24, 40, 48, 56, 64] rfl (by decide))
  refine h.run hp b4_in_code (List.cons_ne_nil _ _)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b3_next)) hok3 (vars := fun _ ↦ 0) (hok3.wf0 h) hok3.m_reg run_b4
    (o := 8) (by decide +kernel) (by decide) fun st4 hok4 hs4 hm4 hpc4 ↦ ?_
  have hd4 := hm4.dmem_eq (hok3.wf0 h) rfl
  simp only [PcOk] at hpc4
  rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_19_at] at hpc4
  have r4 : ∀ r : Reg64, r ∈ [Reg64.rax, .rdx, .rbp, .r13, .r15] →
      reg st4.data r = reg st3.data r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regKeep hm4 _ rfl
  refine cont st4 hpc4 ⟨hok4, Ok.ts_block h hts3 (hm4.kept (hok3.wf0 h)) hs4,
    by rw [hd4]; exact hfw3, by rw [r4 .rax (by simp)]; exact hax3,
    by rw [r4 .rdx (by simp)]; exact hdx3, ?_, by rw [r4 .rbp (by simp), rr .rbp rfl]; exact hc.rbp,
    by rw [r4 .r13 (by simp), rr .r13 rfl]; exact hc.r13,
    by rw [r4 .r15 (by simp), rr .r15 rfl]; exact hc.r15⟩
  rw [show reg st4.data .rbx = BitVec.ofNat 64 2 from hm4.regs .rbx _ rfl, hcnt]
  rfl

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
