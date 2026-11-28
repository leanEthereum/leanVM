module

public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.Squeeze.Exec

/-!
# `SpongeW::squeeze` on AArch64

**`squeeze_spec`**: X0, X1 become `sp.squeeze`'s challenge and the sponge at X0 its sponge, given
`duplex`'s contract. `b0` saves X30, X19, loads the ground challenge, zeroes its tag and branches on
it: a ground challenge is returned (`b3`); otherwise `duplex` permutes (`b1`) and the first two
lanes are returned (`b2`, `b3`).
-/

namespace NativeRustcVmArm.Transcript.Squeeze

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWSqueeze
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 16 := by decide

theorem squeeze_some {sp : SpongeW} {c : EW} (h : sp.ground = some c) :
    sp.squeeze = (c, { sp with ground := none }) := by
  simp only [SpongeW.squeeze, h]

theorem squeeze_none {sp : SpongeW} (h : sp.ground = none) :
    sp.squeeze = (SpongeW.challengeOf sp.duplex.state, sp.duplex) := by
  simp only [SpongeW.squeeze, h]

theorem with_none {sp : SpongeW} (h : sp.ground = none) : { sp with ground := none } = sp := by
  cases sp; simp_all

theorem challengeOf_c0 (st : LeanVM.Semantics.KeccakState) :
    (SpongeW.challengeOf st).c0 = st.toList[0]'(by simp) := by
  simp [SpongeW.challengeOf]

theorem challengeOf_c1 (st : LeanVM.Semantics.KeccakState) :
    (SpongeW.challengeOf st).c1 = st.toList[1]'(by simp) := by
  simp [SpongeW.challengeOf]

variable [Host] {k : Nat}

/-- What the epilogue leaves, from `.LSpongeWSqueeze_2` with the frame. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 squeezeStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWSqueeze.b3Offset)) (hf : Frame m0 16 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = st.data.regs.X0 ∧
      st'.data.regs.X1 = st.data.regs.X1 ∧ st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 16) (by
    have := hst.2.1; have e : squeezeStack = 432 := rfl; omega)
  have hwf : (frameEnv m0 st.data 16 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 16 []) exitS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf hpc hm fun st' hm' hpc' => ?_
  obtain ⟨hepi, hmem, hx0, hx1⟩ := after_eq run_b3 ▸ ok_b3
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm' hepi
  have hx30 : st'.data.regs.X30 = m0.regs.X30 := hsl (0, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc']; simp only [retOf, hx30],
    UInt64.toBitVec_inj.mp (hm'.regs .X0 _ hx0), UInt64.toBitVec_inj.mp (hm'.regs .X1 _ hx1),
    hm'.dmem_eq hwf hmem, hsv⟩

/-- **`SpongeW::squeeze` meets its contract.** -/
theorem squeeze_spec (hp : Placed code k)
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp⟩
  set p := m0.regs.X0.toBitVec with hpdef
  have hQ : squeezeStack = 432 := rfl
  have hn : squeezeStack ≤ m0.regs.SP.toNat := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (m := m0) (F := 16) (by omega)
  have hapF : NativeRustcVm.Apart p 328 (frameBase m0 16) 16 := apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q → ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  -- `b0`.
  have hwf0 : (frameEnv m0 m0 16 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 16) hst (by decide), hfnw⟩, ⟨hmap, hnw⟩, trivial⟩
      (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm0 : Match (frameEnv m0 m0 16 [(p, 328)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.SpongeWSqueeze.entryOffset) NativeRustcVmArm.Vm.SpongeWSqueeze.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hx0, hx1, hx19, hwt, hws⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (fun q ↦
      Touch p 328 (fun j ↦ 304 ≤ j ∧ j < 312) q ∨ NativeRustcVm.InRange (frameBase m0 16) 16 q) :=
    fun q hq ↦ hm1.get?_mem0 hwf0 fun hW ↦ hq (touch_of_written2 hwf0 (r := 1) (r' := 0) rfl rfl
      (by decide) hws hW)
  have hA1 : Agree m0.dmem st1.data.dmem p spongeBytes (fun j ↦ 304 ≤ j) :=
    (agree_of_sameOutside hnw (fun q hq h ↦ hpF q h hq) hs1).mono fun j h ↦ h.1
  -- The zero tag: rewrite the stored literal first (unifying it with `0` by whnf times out).
  have hg0 := wordAt_write hm1 (r := 1) (o := 304) (b := p) (sz := 328) rfl (by decide) hwt
  rw [show UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 m0 16 [(p, 328)])) = 0 from rfl] at hg0
  have hg1 : OptEWAt st1.data.dmem (off p 304) none := hg0
  have hsp1 : SpongeAt st1.data.dmem p { sp with ground := none } := hsp.with_ground hA1 hg1
  have hX19 : st1.data.regs.X19.toBitVec = p := by
    show (st1.data.regs.getXReg .X19).toBitVec = _
    rw [hm1.regs .X19 _ hx19]; exact eval_ptr rfl
  have hso1 : SameOutside m0.dmem st1.data.dmem (fun q ↦ NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 squeezeStack) squeezeStack q) :=
    SameOutside.mono hs1 fun q hq ↦ by
      rcases hq with hq | hq
      · exact Or.inl (inRange_of_touch hnw hq)
      · exact Or.inr (inRange_frame_stack hn (by decide) hq)
  have hgr := hsp.ground
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  cases hg : sp.ground with
  | some c =>
    -- A ground challenge: returned.
    rw [hg] at hgr
    obtain ⟨htag, hc⟩ := hgr
    rw [ewAt_iff, off_off, off_off] at hc
    have htag4 : (frameEnv m0 m0 16 [(p, 328)]).load 1 304 4 = BitVec.ofNat 64 1 :=
      load4_of_tag (Or.inr rfl) htag
    rw [htag4] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    refine Eventually.mono (finish hp hst (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWSqueeze.b3Offset) NativeRustcVmArm.Vm.SpongeWSqueeze.label_2_at)) hf1)
      fun st' ⟨hpc', hx0', hx1', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, ?_, hsv'⟩
    · rw [hx0', squeeze_some hg]
      exact UInt64.toBitVec_inj.mp ((hm1.regs .X0 _ hx0).trans (load_ofMachine (o := 312) rfl hc.1))
    · rw [hx1', squeeze_some hg]
      exact UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ hx1).trans (load_ofMachine (o := 320) rfl hc.2))
    · rw [hd', squeeze_some hg]; exact hsp1
    · intro q hq; rw [hd']; exact hso1 q hq
  | none =>
    -- None: `duplex`, the first two lanes.
    rw [hg] at hgr
    have htag4 : (frameEnv m0 m0 16 [(p, 328)]).load 1 304 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (Or.inl rfl) hgr
    rw [htag4] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    rw [with_none hg] at hsp1
    -- `b1`: `bl duplex`.
    have hwf1 : (frameEnv m0 st1.data 16 []).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf1.kept, hfnw⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm1' : Match (frameEnv m0 st1.data 16 []) callS st1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
        (by rw [hf1.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
      (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWSqueeze.b0Offset + NativeRustcVmArm.Vm.SpongeWSqueeze.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWSqueeze.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWSqueeze.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
    obtain ⟨hmid2, hmem2, hx0', hx19'⟩ := after_eq run_b1 ▸ ok_b1
    have hf2 : Frame m0 16 slots st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
    have hX0' : st2.data.regs.X0.toBitVec = p := by
      show (st2.data.regs.getXReg .X0).toBitVec = _
      rw [hm2.regs .X0 _ hx0']; exact hX19
    have hX19' : st2.data.regs.X19.toBitVec = p := by
      show (st2.data.regs.getXReg .X19).toBitVec = _
      rw [hm2.regs .X19 _ hx19']; exact hX19
    -- `duplex`.
    have h2sp : st2.data.regs.SP.toNat = m0.regs.SP.toNat - 16 := by
      rw [← UInt64.toNat_toBitVec, hf2.sp, frameBase_toNat hn (by decide)]
    have hrc0 : ∀ i < 192, st2.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
        m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
      intro i hi
      have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
        inRange_off_self hi (by have := hrc.2.1; omega)
      rw [hd2]
      refine hs1 _ fun h ↦ ?_
      rcases h with h | h
      · exact not_inRange_of_apart (Apart.symm' hapR) hrc.2.1 hnw hq (inRange_of_touch hnw h)
      · exact not_inRange_of_apart (apart_frame hrc.2.2 hn (by decide)) hrc.2.1 hfnw hq h
    have hrc2 : RcAt st2.data duplexStack := by
      have h := RcAt.call (F := 16) hrc hrc0 hn (by decide) h2sp
      rwa [show squeezeStack - 16 = duplexStack from rfl] at h
    have hpre2 : DuplexPre sp st2.data := by
      unfold DuplexPre
      rw [hX0']
      exact ⟨stackOk_callee hst hf2.kept hf2.sp (by decide) (by decide) (by decide), hrc2,
        ⟨Mapped.keeps hmap hf2.kept, hnw, apart_callee hapS hf2.sp hn (by decide) (by decide), hapR⟩,
        hd2 ▸ hsp1⟩
    refine call_then hpc2 (hdup sp) hpre2 fun st3 hpc3 ⟨hsp3, hs3, hsv3⟩ => ?_
    rw [hX0'] at hsp3 hs3
    have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st2.data duplexStack) duplexStack q →
        NativeRustcVm.InRange (stackBelow m0 squeezeStack) squeezeStack q ∧
          ¬ NativeRustcVm.InRange (frameBase m0 16) 16 q :=
      fun q hq ↦ inRange_callee hf2.sp hn (by decide) (by decide) hq
    have hf3 : Frame m0 16 slots st3.data := by
      refine Frame.call hf2 hsv3 hs3 (fun q hq ↦ ?_) hfnw slots_le
      rcases hq with hq | hq
      · exact hpF q hq
      · exact (hcal q hq).2
    -- `b2`: the first two lanes.
    have hX19'' : st3.data.regs.X19.toBitVec = p := by
      show (st3.data.regs.getXReg .X19).toBitVec = _
      rw [hsv3.1 .X19 rfl]; exact hX19'
    have hwf3 : (frameEnv m0 st3.data 16 [(p, 328)]).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 16) hst (by decide)) hf3.kept, hfnw⟩,
        ⟨Mapped.keeps hmap hf3.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
    have hm3 : Match (frameEnv m0 st3.data 16 [(p, 328)]) loadS st3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
        (by rw [hf3.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX19'', trivial⟩ trivial trivial
        trivial
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
      (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWSqueeze.b1_next])) hm3 fun st4 hm4 hpc4 => ?_
    obtain ⟨hmid4, hmem4, hl0, hl1⟩ := after_eq run_b2 ▸ ok_b2
    have hf4 : Frame m0 16 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
    have hws := wordsAt_iff.mp hsp3.state
    have hw0 : NativeRustcVm.WordAt st3.data.dmem (off p 0) (sp.duplex.state.toList[0]'(by simp)) :=
      hws 0 (by simp)
    have hw1 : NativeRustcVm.WordAt st3.data.dmem (off p 8) (sp.duplex.state.toList[1]'(by simp)) :=
      hws 1 (by simp)
    have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWSqueeze.b3Offset) := by
      simp only [PcOk] at hpc4
      rw [hpc4, Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWSqueeze.b2_next]
    refine Eventually.mono (finish hp hst hpc4' hf4)
      fun st' ⟨hpc', hx0', hx1', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, ?_, hsv'⟩
    · rw [hx0', squeeze_none hg, challengeOf_c0]
      exact UInt64.toBitVec_inj.mp ((hm4.regs .X0 _ hl0).trans (load_ofMachine (o := 0) rfl hw0))
    · rw [hx1', squeeze_none hg, challengeOf_c1]
      exact UInt64.toBitVec_inj.mp ((hm4.regs .X1 _ hl1).trans (load_ofMachine (o := 8) rfl hw1))
    · rw [hd', hd4, squeeze_none hg]; exact hsp3
    · intro q hq
      simp only [not_or] at hq
      obtain ⟨hqp, hqs⟩ := hq
      rw [hd', hd4, hs3 q (fun h ↦ by
          rcases h with h | h
          · exact hqp h
          · exact hqs (hcal q h).1), hd2]
      exact hso1 q (by simp only [not_or]; exact ⟨hqp, hqs⟩)

end

end NativeRustcVmArm.Transcript.Squeeze
