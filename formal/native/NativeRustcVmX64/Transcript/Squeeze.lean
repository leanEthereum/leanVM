module

public import NativeRustcVmX64.Transcript.Squeeze.Exec
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `SpongeW::squeeze` on x86-64

**`squeeze_spec`**: RAX, RDX become `sp.squeeze`'s challenge and the sponge at RDI its sponge,
given `duplex`'s contract. `b0` loads the ground challenge, zeroes its tag and branches on it: a
ground challenge is returned (`b3`); otherwise RBX is pushed, `duplex` permutes (`b1`) and the
first two lanes are returned (`b2`, `b3`).
-/

namespace NativeRustcVmX64.Transcript.Squeeze

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWSqueeze
open NativeRustcVm.Transcript NativeVm.Model

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

/-- **`SpongeW::squeeze` meets its contract.** -/
theorem squeeze_spec (hp : Placed code k)
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp, hgot⟩
  set p := reg m0 .rdi with hpdef
  have hn : squeezeStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (F := 16) hst (by decide)
  have hapF : NativeRustcVm.Apart p 328 (stackBelow m0 16) (16 + 8) :=
    apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hrest : ∀ d : MachineData, Kept m0.dmem d.dmem → ∀ x ∈ [(p, 328)],
      NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2 := by
    intro d hk x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps hmap hk, hnw⟩
  -- `b0`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 16) (rest := [(p, 328)]) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩ (hrest m0 fun _ h ↦ h)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  unfold NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SpongeWSqueeze.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 => ?_
  obtain ⟨hmid1, hx0, hx2, hx7, hwt, hws⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 [] 16 st1.data := Frame.of_block Frame.entry hwf0 hm1 hmid1 nofun
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (fun q ↦ Touch p 328 (fun j ↦ 304 ≤ j ∧ j < 312) q) :=
    sameOutside_touch hwf0 hm1 (r := 1) rfl (by decide) hws
  have hA1 : Agree m0.dmem st1.data.dmem p spongeBytes (fun j ↦ 304 ≤ j) :=
    (agree_of_sameOutside (R := fun _ ↦ False) hnw (fun _ h ↦ h.elim)
      (SameOutside.mono hs1 fun _ h ↦ Or.inl h)).mono fun j h ↦ h.1
  have hg0 := wordAt_write hm1 (r := 1) (o := 304) (b := p) (sz := 328) rfl (by decide) hwt
  rw [show UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 m0 16 [(p, 328)] (fun _ ↦ 0) 0)) = 0
    from rfl] at hg0
  have hg1 : OptEWAt st1.data.dmem (off p 304) none := hg0
  have hsp1 : SpongeAt st1.data.dmem p { sp with ground := none } := hsp.with_ground hA1 hg1
  have hX7 : reg st1.data .rdi = p := (hm1.regs .rdi _ hx7).trans (eval_ptr rfl)
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (fun q ↦
      NativeRustcVm.InRange p 328 q ∨
        NativeRustcVm.InRange (stackBelow m0 squeezeStack) squeezeStack q) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inl (inRange_of_touch hnw hq)
  have hgr := hsp.ground
  simp only [PcOk] at hpc1
  sym_simp_at hpc1
  cases hg : sp.ground with
  | some c =>
    -- A ground challenge: returned.
    rw [hg] at hgr
    obtain ⟨htag, hc⟩ := hgr
    rw [ewAt_iff, off_off, off_off] at hc
    have htag1 : (frameEnv m0 m0 16 [(p, 328)] (fun _ ↦ 0) 0).load 1 304 1 = BitVec.ofNat 64 1 :=
      load1_of_tag (Or.inr rfl) htag
    simp only [htag1] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 16) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf1.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf1 nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.SpongeWSqueeze.label_2_at))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st' hm' hpc' => ?_
    obtain ⟨hepi, hmem, hrax, hrdx⟩ := after_eq run_b3 ▸ ok_b3
    obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf1 hwf1 hm' hepi
    have hd' : st'.data.dmem = st1.data.dmem := hm'.dmem_eq hwf1 hmem
    simp only [PcOk] at hpc'
    refine .done _ ⟨by rw [hpc']; exact hf1.load_ret hst (by decide), hrsp, ?_, ?_, ?_, ?_, hsv⟩
    · rw [squeeze_some hg]
      exact (hm'.regs .rax _ hrax).trans ((hm1.regs .rax _ hx0).trans
        (load_ofMachine (o := 312) rfl hc.1))
    · rw [squeeze_some hg]
      exact (hm'.regs .rdx _ hrdx).trans ((hm1.regs .rdx _ hx2).trans
        (load_ofMachine (o := 320) rfl hc.2))
    · rw [hd', squeeze_some hg]; exact hsp1
    · intro q hq; rw [hd']; exact hso1 q hq
  | none =>
    -- None: `duplex`, the first two lanes.
    rw [hg] at hgr
    have htag1 : (frameEnv m0 m0 16 [(p, 328)] (fun _ ↦ 0) 0).load 1 304 1 = BitVec.ofNat 64 0 :=
      load1_of_tag (Or.inl rfl) hgr
    simp only [htag1] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    rw [with_none hg] at hsp1
    -- `b1`: RBX pushed, `call duplex`.
    have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 16) (rest := []) (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWSqueeze.b1Offset + b1.length)).toBitVec)
      ⟨Mapped.keeps (frame_mapped hst (by decide)) hf1.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 (fun _ _ ↦ rfl)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWSqueeze.b0_next))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st2 hm2 hpc2 => ?_
    obtain ⟨hpro2, hw2, hx7', hx3'⟩ := after_eq run_b1 ▸ ok_b1
    have hf2 : Frame m0 16 slots 0 st2.data :=
      Frame.of_prologue hf1 hwf1 hm2 hpro2 slots_le (by decide)
    have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 16) 16) :=
      sameOutside_low hwf1 hm2 (r := 0) rfl (by decide) hw2
    have hX7' : reg st2.data .rdi = p := (hm2.regs .rdi _ hx7').trans hX7
    have hX3' : reg st2.data .rbx = p := (hm2.regs .rbx _ hx3').trans hX7
    have hsp2r : rspOf st2.data = stackBelow m0 16 := by rw [hf2.sp, off_zero]
    -- `duplex`.
    have hrc2 : ∀ i < 192, st2.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
        m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
      intro i hi
      have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
        inRange_off_self hi (by have := hrc.2.1; unfold NativeRustcVm.NoWrap at this; omega)
      refine (hs2 _ fun h ↦ not_inRange_of_apart (apart_frame hrc.2.2 hn (by decide)) hrc.2.1
        hfnw hq (inRange_mono h (by decide))).trans (hs1 _ fun h ↦ ?_)
      exact not_inRange_of_apart (Apart.symm' hapR) hrc.2.1 hnw hq (inRange_of_touch hnw h)
    have hsp2 : SpongeAt st2.data.dmem p sp :=
      hsp1.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs2
    have hgot2 := got_keep hgot hst (writes := [(p, spongeBytes)])
      (by simp [p]) (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact hnw)
      (d := st2.data) (by
        intro q hq
        have hs : ¬ NativeRustcVm.InRange (stackBelow m0 squeezeStack) squeezeStack q :=
          fun h => hq (Or.inr h)
        refine (hs2 q fun h => hs (inRange_frame_stack h8 hn (by decide) h)).trans ?_
        apply hso1 q
        simpa [spongeBytes] using hq)
    have hpre2 : DuplexPre sp st2.data := by
      unfold DuplexPre
      rw [hX7']
      exact ⟨stackOk_callee hst hf2.kept hsp2r (by decide),
        RcAt.callee hrc hrc2 hsp2r hn (by decide),
        ⟨Mapped.keeps hmap hf2.kept, hnw, apart_callee hapS hsp2r hn (by decide), hapR⟩, hsp2,
        got_callee hgot hgot2 hsp2r hn (by decide) (fun l hl => (hgot.1 l hl).2.2.2)⟩
    refine call_then hpc2 (hdup sp) hpre2 fun st3 hpc3 hrsp3 ⟨hsp3, hs3, hsv3⟩ => ?_
    rw [hX7'] at hsp3 hs3
    have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st2.data duplexStack) duplexStack q →
        NativeRustcVm.InRange (stackBelow m0 squeezeStack) squeezeStack q ∧
          ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
      fun q hq ↦ inRange_callee hsp2r h8 hn (by decide) hq
    have hf3 : Frame m0 16 slots 8 st3.data := by
      refine Frame.call hf2 hsv3 hrsp3 hs3 (fun q hq ↦ ?_) hfnw slots_le
      rcases hq with hq | hq
      · exact hpF q hq
      · exact (hcal q hq).2
    -- `b2`, `b3`: the first two lanes, RBX popped, `ret`.
    have hX3'' : reg st3.data .rbx = p := (hsv3.1 .rbx rfl).trans hX3'
    have hwf3 := frame_wf (m0 := m0) (d := st3.data) (F := 16) (rest := [(p, 328)])
      (vars := fun _ ↦ 0) (ret := 0)
      ⟨Mapped.keeps (frame_mapped hst (by decide)) hf3.kept, hfnw⟩ (hrest _ hf3.kept)
      (List.pairwise_pair.mpr (Apart.symm' hapF))
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3 nofun
      (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWSqueeze.b1_next))
      (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.rsp_eval, known_ptr rfl hX3'', trivial⟩ trivial
        trivial trivial) fun st4 hm4 hpc4 => ?_
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2 run_b3') hwf3 nofun
      hpc4 hm4 fun st5 hm5 hpc5 => ?_
    obtain ⟨hepi, hmem5, hl0, hl1⟩ := after_eq run_b3' ▸ ok_b23
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf3 hwf3 hm5 hepi
    have hd5 : st5.data.dmem = st3.data.dmem := hm5.dmem_eq hwf3 hmem5
    have hws := wordsAt_iff.mp hsp3.state
    have hw0 : NativeRustcVm.WordAt st3.data.dmem (off p 0)
        (sp.duplex.state.toList[0]'(by simp)) := hws 0 (by simp)
    have hw1 : NativeRustcVm.WordAt st3.data.dmem (off p 8)
        (sp.duplex.state.toList[1]'(by simp)) := hws 1 (by simp)
    simp only [PcOk] at hpc5
    refine .done _ ⟨by rw [hpc5]; exact hf3.load_ret hst (by decide), hrsp5, ?_, ?_, ?_, ?_,
      hsv5⟩
    · rw [squeeze_none hg, challengeOf_c0]
      exact (hm5.regs .rax _ hl0).trans (load_ofMachine (o := 0) rfl hw0)
    · rw [squeeze_none hg, challengeOf_c1]
      exact (hm5.regs .rdx _ hl1).trans (load_ofMachine (o := 8) rfl hw1)
    · rw [hd5, squeeze_none hg]; exact hsp3
    · intro q hq
      simp only [not_or] at hq
      obtain ⟨hqp, hqs⟩ := hq
      rw [hd5, hs3 q (fun h ↦ by
          rcases h with h | h
          · exact hqp h
          · exact hqs (hcal q h).1)]
      refine (hs2 q fun h ↦ hqs (inRange_frame_stack h8 hn (by decide) h)).trans ?_
      exact hso1 q (by simp only [not_or]; exact ⟨hqp, hqs⟩)

end

end NativeRustcVmX64.Transcript.Squeeze
