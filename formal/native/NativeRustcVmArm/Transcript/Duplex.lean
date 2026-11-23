module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.Duplex.Exec

/-!
# `SpongeW::duplex` on AArch64

**`duplex_spec`**: the sponge at X0 becomes `sp.duplex`, given the contracts of `duplex_input` and
`keccak_f`. The prologue saves X30 and X19 in a 16-byte frame (`Frame`); `duplex_input` writes
the rate lanes; `keccak_f` permutes the 25 lanes, its stack below the frame; `b2` zeroes the queue's
count and restores the registers.
-/

namespace NativeRustcVmArm.Transcript.Duplex

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWDuplex
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 16 := by decide

theorem duplex_eq (sp : SpongeW) :
    sp.duplex = { { { sp with state := sp.duplexInput } with
      state := LeanVM.Semantics.keccakF1600 sp.duplexInput } with pending := #[] } := rfl

variable [Host] {k : Nat}

/-- **`SpongeW::duplex` meets its contract.** -/
theorem duplex_spec (hp : Placed code k)
    (hdi : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp))
    (hkf : Spec (Labels.label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp⟩
  set p := m0.regs.X0.toBitVec with hpdef
  have hn : 416 ≤ m0.regs.SP.toNat := hst.2.1
  have hD : duplexStack = 416 := rfl
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (m := m0) (F := 16) (by omega)
  have hapF : NativeRustcVm.Apart p 328 (frameBase m0 16) 16 := apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q → ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hrcS := hrc.2.2
  have hrcnw : rcAddr.toNat + 192 ≤ 2 ^ 64 := hrc.2.1
  -- `b0`: the prologue, `bl duplex_input`.
  have hwf0 : (frameEnv m0 m0 16 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 16) hst (by decide), hfnw⟩, ⟨hmap, hnw⟩, trivial⟩
      (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm0 : Match (frameEnv m0 m0 16 [(p, 328)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplex.entryOffset) NativeRustcVmArm.Vm.SpongeWDuplex.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hx0, hx19, hw0⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (frameBase m0 16) 16) :=
    sameOutside_region hwf0 hm1 rfl hw0
  have hX0 : st1.data.regs.X0.toBitVec = p := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ hx0]; exact eval_ptr rfl
  have hX19 : st1.data.regs.X19.toBitVec = p := by
    show (st1.data.regs.getXReg .X19).toBitVec = _
    rw [hm1.regs .X19 _ hx19]; exact eval_ptr rfl
  have hk1 : Kept m0.dmem st1.data.dmem := hf1.kept
  have hsp1 : SpongeAt st1.data.dmem p sp :=
    hsp.frame hnw (fun q hq h ↦ hpF q h hq) hs1
  -- `duplex_input`.
  have hpre1 : DuplexInputPre sp st1.data := by
    refine ⟨stackOk_callee hst hk1 hf1.sp (by decide) (by decide) (by decide), ?_, ?_⟩
    · rw [hX0]
      exact ⟨Mapped.keeps hmap hk1, hnw,
        apart_callee hapS hf1.sp hn (by decide) (by decide), hapR⟩
    · rw [hX0]; exact hsp1
  refine call_then hpc1 (hdi sp) hpre1 fun st2 hpc2 ⟨hsp2, hs2, hsv2⟩ => ?_
  rw [hX0] at hsp2 hs2
  have hf2 : Frame m0 16 slots st2.data :=
    Frame.call hf1 hsv2 hs2 (fun q hq ↦ hpF q hq) hfnw slots_le
  -- `b1`: `bl keccak_f`.
  have hwf2 : (frameEnv m0 st2.data 16 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf2.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st2.data 16 []) midS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWDuplex.b0Offset + NativeRustcVmArm.Vm.SpongeWDuplex.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWDuplex.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWDuplex.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid, hmem3, hx0', hx19'⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 16 slots st3.data := Frame.of_block hf2 hwf2 hm3 hmid slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hX19' : st2.data.regs.X19.toBitVec = p := by
    show (st2.data.regs.getXReg .X19).toBitVec = _
    rw [hsv2.1 .X19 rfl]; exact hX19
  have hX0' : st3.data.regs.X0.toBitVec = p := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ hx0']; exact hX19'
  have hX19'' : st3.data.regs.X19.toBitVec = p := by
    show (st3.data.regs.getXReg .X19).toBitVec = _
    rw [hm3.regs .X19 _ hx19']; exact hX19'
  -- `keccak_f`.
  have hrc0 : ∀ i < 192, st3.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
    intro i hi
    have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
      inRange_off_self hi (by omega)
    rw [hd3, hs2 _ fun h ↦ not_inRange_of_apart (Apart.symm' hapR) hrc.2.1 hnw hq h,
      hs1 _ fun h ↦ not_inRange_of_apart (apart_frame hrcS hn (by decide)) hrc.2.1 hfnw hq h]
  have h3sp : st3.data.regs.SP.toNat = m0.regs.SP.toNat - 16 := by
    rw [← UInt64.toNat_toBitVec, hf3.sp, frameBase_toNat hn (by decide)]
  have hap200 : NativeRustcVm.Apart p 200 (stackBelow m0 duplexStack) duplexStack := by
    have h : NativeRustcVm.Apart p 328 (stackBelow m0 duplexStack) duplexStack := hapS
    unfold NativeRustcVm.Apart at h ⊢; omega
  have hapR200 : NativeRustcVm.Apart p 200 rcAddr 192 := by
    have h : NativeRustcVm.Apart p 328 rcAddr 192 := hapR
    unfold NativeRustcVm.Apart at h ⊢; omega
  have hstk3 : StackOk st3.data keccakFStack :=
    stackOk_callee hst hf3.kept hf3.sp (by decide) (by decide) (by decide)
  have hrc3 : RcAt st3.data keccakFStack := by
    have h := RcAt.call (F := 16) hrc hrc0 hn (by decide) h3sp
    rwa [show duplexStack - 16 = keccakFStack from rfl] at h
  have hapK : NativeRustcVm.Apart p 200 (stackBelow st3.data keccakFStack) keccakFStack :=
    apart_callee hap200 hf3.sp hn (by decide) (by decide)
  have hmapK : Mapped st3.data.dmem p 200 := fun i hi ↦ Mapped.keeps hmap hf3.kept i (by
    show i < 328; omega)
  have hpre3 : KeccakFPre st3.data := by
    unfold KeccakFPre
    rw [hX0']
    exact ⟨hstk3, hrc3, hmapK, show p.toNat + 200 ≤ 2 ^ 64 by omega, hapK, hapR200⟩
  refine call_then hpc3 hkf hpre3 fun st4 hpc4 ⟨hkw, hs4, hsv4⟩ => ?_
  rw [hX0'] at hkw hs4
  have hstnw : NativeRustcVm.NoWrap (stackBelow m0 duplexStack) duplexStack := by
    show _ + duplexStack ≤ _
    rw [toNat_stackBelow hst.2.1]; have := m0.regs.SP.toNat_lt; omega
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st3.data keccakFStack) keccakFStack q →
      NativeRustcVm.InRange (stackBelow m0 duplexStack) duplexStack q ∧
        ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ inRange_callee hf3.sp hn (by decide) (by decide) hq
  have hf4 : Frame m0 16 slots st4.data := by
    refine Frame.call hf3 hsv4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q (inRange_mono hq (by decide))
    · exact (hcal q hq).2
  -- The lanes permuted, the rest of the sponge kept.
  have hsp2' : SpongeAt st3.data.dmem p { sp with state := sp.duplexInput } := hd3 ▸ hsp2
  have hA4 : Agree st3.data.dmem st4.data.dmem p spongeBytes (· < 200) := by
    refine agree_of_sameOutside (R := fun q ↦ NativeRustcVm.InRange (stackBelow st3.data keccakFStack)
      keccakFStack q) hnw (fun q hq h ↦ ?_) (SameOutside.mono hs4 fun q hq ↦ ?_)
    · exact not_inRange_of_apart (Apart.symm' hapS) hstnw hnw (hcal q hq).1 h
    · rcases hq with hq | hq
      · obtain ⟨j, hj, hw, rfl⟩ := touch_of_inRange (b := p) (o := 0) (n := 200) (N := 328) hnw
          (by decide) (by rwa [off_zero])
        exact Or.inl ⟨j, hj, by omega, rfl⟩
      · exact Or.inr hq
  have hsp4 : SpongeAt st4.data.dmem p
      { { sp with state := sp.duplexInput } with state := LeanVM.Semantics.keccakF1600 sp.duplexInput } :=
    hsp2'.with_state hA4 (hkw _ hsp2'.state)
  -- `b2`: the count zeroed, the epilogue.
  have hX19'' : st4.data.regs.X19.toBitVec = p := by
    show (st4.data.regs.getXReg .X19).toBitVec = _
    rw [hsv4.1 .X19 rfl]; exact hX19''
  have hwf4 : (frameEnv m0 st4.data 16 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf4.kept, hfnw⟩,
      ⟨Mapped.keeps hmap hf4.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm4 : Match (frameEnv m0 st4.data 16 [(p, 328)]) exitS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX19'', trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWDuplex.b1_next])) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hw5, hws5⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (0, .X30) (List.mem_cons_self ..)
  have hs5 := sameOutside_touch hwf4 hm5 (r := 1) rfl (by decide) hws5
  have hA5 : Agree st4.data.dmem st5.data.dmem p spongeBytes (fun j ↦ 200 ≤ j ∧ j < 304) :=
    (agree_of_sameOutside hnw (fun _ h ↦ h.elim) hs5).mono fun j h ↦ by omega
  refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], ?_, ?_, hsv5⟩
  · rw [duplex_eq]
    refine hsp4.with_pending hA5 (by decide) ?_ nofun
    have := wordAt_write hm5 (r := 1) (o := 296) rfl (by decide) hw5
    exact this
  · intro q hq
    simp only [not_or] at hq
    obtain ⟨hqp, hqs⟩ := hq
    have hqf : ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
      fun h ↦ hqs (inRange_frame_stack hst.2.1 (by decide) h)
    rw [hs5 q (fun h ↦ by
        rcases h with h | h
        · exact hqp (inRange_of_touch hnw h)
        · exact h)]
    rw [show (frameEnv m0 st4.data 16 [(p, 328)]).mem0 = st4.data.dmem from rfl, hs4 q (fun h ↦ by
        rcases h with h | h
        · exact hqp (inRange_mono h (by decide))
        · exact hqs (hcal q h).1),
      hd3, hs2 q hqp, hs1 q hqf]

end

end NativeRustcVmArm.Transcript.Duplex
