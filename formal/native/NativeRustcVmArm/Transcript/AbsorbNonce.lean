module

public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Transcript.AbsorbNonce.Exec

/-!
# `SpongeW::absorb_nonce` on AArch64

**`absorbNonce_spec`**: X0 becomes `sp.absorbNonce`'s lane and the sponge at X0 its sponge, given
the contracts of `absorb` and `duplex`. `b0` saves X30, X19 and calls `absorb` with the tag `4`;
`b1` calls `duplex`; `b2` returns the third lane and stores the first two as the ground challenge
(tag `1`).
-/

namespace NativeRustcVmArm.Transcript.AbsorbNonce

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWAbsorbNonce
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 16 := by decide

/-- `absorbNonce` on the lanes as a list. -/
theorem absorbNonce_eq (sp : SpongeW) (x : EW) :
    sp.absorbNonce x = ((sp.absorb x 4).duplex.state.toList[2]'(by simp),
      { (sp.absorb x 4).duplex with ground := some ⟨(sp.absorb x 4).duplex.state.toList[0]'(by simp),
        (sp.absorb x 4).duplex.state.toList[1]'(by simp)⟩ }) := by
  simp [SpongeW.absorbNonce, SpongeW.challengeOf, LeanVM.Protocol.Compile.dsPowNonce]

theorem ofBitVec_toBitVec' (w : UInt64) : UInt64.ofBitVec w.toBitVec = w := rfl

variable [Host] {k : Nat}

/-- **`SpongeW::absorb_nonce` meets its contract.** -/
theorem absorbNonce_spec (hp : Placed code k)
    (habs : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp))
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp⟩
  set p := m0.regs.X0.toBitVec with hpdef
  have hN : absorbNonceStack = 480 := rfl
  have hn : absorbNonceStack ≤ m0.regs.SP.toNat := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (m := m0) (F := 16) (by omega)
  have hapF : NativeRustcVm.Apart p 328 (frameBase m0 16) 16 := apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q → ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hstnw : NativeRustcVm.NoWrap (stackBelow m0 absorbNonceStack) absorbNonceStack := by
    show _ + absorbNonceStack ≤ _
    rw [toNat_stackBelow hst.2.1]; have := m0.regs.SP.toNat_lt; omega
  -- What the function may change: the sponge and its stack; the round constants are apart.
  have hrcOut : ∀ q, (NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := fun q hq h ↦ by
    rcases hq with hq | hq
    · exact not_inRange_of_apart (Apart.symm' hapR) hrc.2.1 hnw h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hstnw h hq
  -- `b0`: the prologue, `bl absorb`.
  have hwf0 : (frameEnv m0 m0 16 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 16) hst (by decide), hfnw⟩, ⟨hmap, hnw⟩, trivial⟩
      (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm0 : Match (frameEnv m0 m0 16 [(p, 328)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entryOffset) NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hw0, hx0, hx1, hx2, hx3, hx19⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (frameBase m0 16) 16) :=
    sameOutside_region hwf0 hm1 rfl hw0
  have hso1 : SameOutside m0.dmem st1.data.dmem (fun q ↦ NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack hn (by decide) hq)
  have hsp1 : SpongeAt st1.data.dmem p sp := hsp.frame hnw (fun q hq h ↦ hpF q h hq) hs1
  have hX0 : st1.data.regs.X0.toBitVec = p := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ hx0]; exact eval_ptr rfl
  have hX19 : st1.data.regs.X19.toBitVec = p := by
    show (st1.data.regs.getXReg .X19).toBitVec = _
    rw [hm1.regs .X19 _ hx19]; exact eval_ptr rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ hx1)
  have hX2 : st1.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ hx2)
  have hX3 : st1.data.regs.X3 = 4 := by
    have h := hm1.regs .X3 _ hx3
    rw [show (Sym.lit 4).eval (frameEnv m0 m0 16 [(p, 328)]) = (4 : UInt64).toBitVec from rfl] at h
    exact UInt64.toBitVec_inj.mp h
  -- `absorb`.
  have h1sp : st1.data.regs.SP.toNat = m0.regs.SP.toNat - 16 := by
    rw [← UInt64.toNat_toBitVec, hf1.sp, frameBase_toNat hn (by decide)]
  have hpre1 : AbsorbPre sp st1.data := by
    unfold AbsorbPre
    rw [hX0]
    exact ⟨stackOk_callee hst hf1.kept hf1.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso1 hrcOut) hn (by decide) h1sp (by decide),
      ⟨Mapped.keeps hmap hf1.kept, hnw, apart_callee hapS hf1.sp hn (by decide) (by decide), hapR⟩,
      hsp1⟩
  refine call_then hpc1 (habs sp) hpre1 fun st2 hpc2 ⟨hsp2, hs2, hsv2⟩ => ?_
  rw [hX0, hX1, hX2, hX3] at hsp2
  rw [hX0] at hs2
  have hcal2 : ∀ q, NativeRustcVm.InRange (stackBelow st1.data absorbStack) absorbStack q →
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q ∧
        ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ inRange_callee hf1.sp hn (by decide) (by decide) hq
  have hf2 : Frame m0 16 slots st2.data := by
    refine Frame.call hf1 hsv2 hs2 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q hq
    · exact (hcal2 q hq).2
  have hso2 : SameOutside m0.dmem st2.data.dmem (fun q ↦ NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs2 q (fun h ↦ by
      rcases h with h | h
      · exact hq.1 h
      · exact hq.2 (hcal2 q h).1)]
    exact hso1 q (by simp only [not_or]; exact hq)
  -- `b1`: `bl duplex`.
  have hX19' : st2.data.regs.X19.toBitVec = p := by
    show (st2.data.regs.getXReg .X19).toBitVec = _
    rw [hsv2.1 .X19 rfl]; exact hX19
  have hwf2 : (frameEnv m0 st2.data 16 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf2.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st2.data 16 []) callS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWAbsorbNonce.b0Offset + NativeRustcVmArm.Vm.SpongeWAbsorbNonce.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWAbsorbNonce.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWAbsorbNonce.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx0', hx19'⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 16 slots st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hX0' : st3.data.regs.X0.toBitVec = p := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ hx0']; exact hX19'
  have hX19'' : st3.data.regs.X19.toBitVec = p := by
    show (st3.data.regs.getXReg .X19).toBitVec = _
    rw [hm3.regs .X19 _ hx19']; exact hX19'
  -- `duplex`.
  have h3sp : st3.data.regs.SP.toNat = m0.regs.SP.toNat - 16 := by
    rw [← UInt64.toNat_toBitVec, hf3.sp, frameBase_toNat hn (by decide)]
  have hso3 : SameOutside m0.dmem st3.data.dmem (fun q ↦ NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) := by
    rw [show st3.data.dmem = st2.data.dmem from hd3]; exact hso2
  have hpre3 : DuplexPre (sp.absorb ⟨m0.regs.X1, m0.regs.X2⟩ 4) st3.data := by
    unfold DuplexPre
    rw [hX0']
    exact ⟨stackOk_callee hst hf3.kept hf3.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hn (by decide) h3sp (by decide),
      ⟨Mapped.keeps hmap hf3.kept, hnw, apart_callee hapS hf3.sp hn (by decide) (by decide), hapR⟩,
      hd3 ▸ hsp2⟩
  refine call_then hpc3 (hdup _) hpre3 fun st4 hpc4 ⟨hsp4, hs4, hsv4⟩ => ?_
  rw [hX0'] at hsp4 hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data duplexStack) duplexStack q →
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q ∧
        ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ inRange_callee hf3.sp hn (by decide) (by decide) hq
  have hf4 : Frame m0 16 slots st4.data := by
    refine Frame.call hf3 hsv4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q hq
    · exact (hcal4 q hq).2
  have hso4 : SameOutside m0.dmem st4.data.dmem (fun q ↦ NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs4 q (fun h ↦ by
      rcases h with h | h
      · exact hq.1 h
      · exact hq.2 (hcal4 q h).1)]
    exact hso3 q (by simp only [not_or]; exact hq)
  -- `b2`: the third lane, the ground challenge, the epilogue.
  set sd := (sp.absorb ⟨m0.regs.X1, m0.regs.X2⟩ 4).duplex with hsd
  have hX19''' : st4.data.regs.X19.toBitVec = p := by
    show (st4.data.regs.getXReg .X19).toBitVec = _
    rw [hsv4.1 .X19 rfl]; exact hX19''
  have hwf4 : (frameEnv m0 st4.data 16 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf4.kept, hfnw⟩,
      ⟨Mapped.keeps hmap hf4.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm4 : Match (frameEnv m0 st4.data 16 [(p, 328)]) exitS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX19''', trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWAbsorbNonce.b1_next])) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hx0'', hwt, hwc0, hwc1, hws5⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (0, .X30) (List.mem_cons_self ..)
  have hs5 := sameOutside_touch hwf4 hm5 (r := 1) rfl (by decide) hws5
  have hA5 : Agree st4.data.dmem st5.data.dmem p spongeBytes (fun j ↦ 304 ≤ j) :=
    (agree_of_sameOutside hnw (fun _ h ↦ h.elim) hs5).mono fun j h ↦ h.1
  have hws := wordsAt_iff.mp hsp4.state
  have hl0 : NativeRustcVm.WordAt st4.data.dmem (off p 0) (sd.state.toList[0]'(by simp)) :=
    hws 0 (by simp)
  have hl1 : NativeRustcVm.WordAt st4.data.dmem (off p 8) (sd.state.toList[1]'(by simp)) :=
    hws 1 (by simp)
  have hl2 : NativeRustcVm.WordAt st4.data.dmem (off p 16) (sd.state.toList[2]'(by simp)) :=
    hws 2 (by simp)
  have ht := wordAt_write hm5 (r := 1) (o := 304) (b := p) (sz := 328) rfl (by decide) hwt
  rw [show UInt64.ofBitVec ((Sym.lit 1).eval (frameEnv m0 st4.data 16 [(p, 328)])) = 1 from rfl]
    at ht
  have hc0 := wordAt_write hm5 (r := 1) (o := 312) (b := p) (sz := 328) rfl (by decide) hwc0
  rw [show (Sym.load 1 0 8).eval (frameEnv m0 st4.data 16 [(p, 328)]) = _ from
    load_ofMachine (o := 0) rfl hl0, ofBitVec_toBitVec'] at hc0
  have hc1 := wordAt_write hm5 (r := 1) (o := 320) (b := p) (sz := 328) rfl (by decide) hwc1
  rw [show (Sym.load 1 8 8).eval (frameEnv m0 st4.data 16 [(p, 328)]) = _ from
    load_ofMachine (o := 8) rfl hl1, ofBitVec_toBitVec'] at hc1
  have hg : OptEWAt st5.data.dmem (off p 304)
      (some ⟨sd.state.toList[0]'(by simp), sd.state.toList[1]'(by simp)⟩) := by
    refine ⟨ht, ewAt_iff.mpr ⟨?_, ?_⟩⟩
    · rw [off_off]; exact hc0
    · rw [off_off, off_off]; exact hc1
  refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], ?_, ?_, ?_,
    hsv5⟩
  · rw [absorbNonce_eq]
    exact UInt64.toBitVec_inj.mp ((hm5.regs .X0 _ hx0'').trans (load_ofMachine (o := 16) rfl hl2))
  · rw [absorbNonce_eq]
    exact hsp4.with_ground hA5 hg
  · intro q hq
    rw [hs5 q (fun h ↦ by
      rcases h with h | h
      · exact hq (Or.inl (inRange_of_touch hnw h))
      · exact h)]
    exact hso4 q hq

end

end NativeRustcVmArm.Transcript.AbsorbNonce
