module

public import NativeRustcVmX64.Transcript.AbsorbNonce.Exec
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names

/-!
# `SpongeW::absorb_nonce` on x86-64

**`absorbNonce_spec`**: RAX becomes `sp.absorbNonce`'s lane and the sponge at RDI its sponge,
given the contracts of `absorb` and `duplex`. `b0` pushes RBX and calls `absorb` with the tag `4`;
`b1` calls `duplex`; `b2` returns the third lane and stores the first two as the ground challenge
(tag `1`).
-/

namespace NativeRustcVmX64.Transcript.AbsorbNonce

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWAbsorbNonce
open NativeRustcVm.Transcript NativeVm.Model

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
    (habs : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp))
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp, hgot⟩
  set p := reg m0 .rdi with hpdef
  have hn : absorbNonceStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (F := 16) hst (by decide)
  have hapF : NativeRustcVm.Apart p 328 (stackBelow m0 16) (16 + 8) :=
    apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hstnw : NativeRustcVm.NoWrap (stackBelow m0 absorbNonceStack) absorbNonceStack :=
    stack_noWrap hst
  have hrest : ∀ d : MachineData, Kept m0.dmem d.dmem → ∀ x ∈ [(p, 328)],
      NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2 := by
    intro d hk x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps hmap hk, hnw⟩
  -- What the function may change: the sponge and its stack; the round constants are apart.
  have hrcOut : ∀ q, (NativeRustcVm.InRange p 328 q ∨
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := fun q hq h ↦ by
    rcases hq with hq | hq
    · exact not_inRange_of_apart (Apart.symm' hapR) hrc.2.1 hnw h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 (noWrap_stackBelow hst) h (inRange_mono hq (by omega))
  -- `b0`: RBX pushed, `call absorb`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 16) (rest := [(p, 328)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWAbsorbNonce.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (hrest m0 fun _ h ↦ h) (List.pairwise_pair.mpr (Apart.symm' hapF))
  unfold NativeRustcVmX64.Vm.SpongeWAbsorbNonce.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SpongeWAbsorbNonce.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hw0, hx7, hx4, hx2, hx1, hx3⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 16) 16) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw0
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (fun q ↦
      NativeRustcVm.InRange p 328 q ∨
        NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack h8 hn (by decide) hq)
  have hsp1 : SpongeAt st1.data.dmem p sp :=
    hsp.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs1
  have hX7 : reg st1.data .rdi = p := (hm1.regs .rdi _ hx7).trans (eval_ptr rfl)
  have hX3 : reg st1.data .rbx = p := (hm1.regs .rbx _ hx3).trans (eval_ptr rfl)
  have hX4 : reg st1.data .rsi = reg m0 .rsi := hm1.regs .rsi _ hx4
  have hX2 : reg st1.data .rdx = reg m0 .rdx := hm1.regs .rdx _ hx2
  have hX1 : (UInt64.ofBitVec (reg st1.data .rcx) : UInt64) = 4 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hx1]; rfl
  have hsp1r : rspOf st1.data = stackBelow m0 16 := by rw [hf1.sp, off_zero]
  -- `absorb`.
  have hpre1 : AbsorbPre sp st1.data := by
    unfold AbsorbPre
    rw [hX7]
    exact ⟨stackOk_callee hst hf1.kept hsp1r (by decide),
      RcAt.callee hrc (rc_keep hso1 hrcOut) hsp1r hn (by decide),
      ⟨Mapped.keeps hmap hf1.kept, hnw, apart_callee hapS hsp1r hn (by decide), hapR⟩, hsp1,
      got_callee hgot (got_keep hgot hst (writes := [(p, spongeBytes)])
        (by simp [p]) (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact hnw)
        (by simpa [spongeBytes] using hso1))
        hsp1r hn (by decide) (fun l hl => (hgot.1 l hl).2.2.2)⟩
  refine call_then hpc1 (habs sp) hpre1 fun st2 hpc2 hrsp2 ⟨hsp2, hs2, hsv2⟩ => ?_
  simp only [hX7, hX4, hX2, hX1] at hsp2 hs2
  have hcal2 : ∀ q, NativeRustcVm.InRange (stackBelow st1.data absorbStack) absorbStack q →
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ inRange_callee hsp1r h8 hn (by decide) hq
  have hf2 : Frame m0 16 slots 8 st2.data := by
    refine Frame.call hf1 hsv2 hrsp2 hs2 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q hq
    · exact (hcal2 q hq).2
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange p 328 q ∨
        NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      rw [hs2 q (fun h ↦ by
        rcases h with h | h
        · exact hq.1 h
        · exact hq.2 (hcal2 q h).1)]
      exact hso1 q (by simp only [not_or]; exact hq)
  -- `b1`: `call duplex`.
  have hX3' : reg st2.data .rbx = p := (hsv2.1 .rbx rfl).trans hX3
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 16) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWAbsorbNonce.b1Offset + b1.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf2.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWAbsorbNonce.b0_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hw3, hx7', hx3'⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 16 slots 0 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 16) 8) :=
    sameOutside_low hwf2 hm3 (r := 0) rfl (by decide) hw3
  have hX7' : reg st3.data .rdi = p := (hm3.regs .rdi _ hx7').trans hX3'
  have hX3'' : reg st3.data .rbx = p := (hm3.regs .rbx _ hx3').trans hX3'
  have hsp3r : rspOf st3.data = stackBelow m0 16 := by rw [hf3.sp, off_zero]
  -- `duplex`.
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange p 328 q ∨
        NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      rw [hs3 q fun h ↦ hq.2 (inRange_frame_stack h8 hn (by decide) (inRange_mono h (by decide)))]
      exact hso2 q (by simp only [not_or]; exact hq)
  have hsp3 := hsp2.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs3
  have hpre3 : DuplexPre (sp.absorb ⟨.ofBitVec (reg m0 .rsi), .ofBitVec (reg m0 .rdx)⟩ 4)
      st3.data := by
    unfold DuplexPre
    rw [hX7']
    exact ⟨stackOk_callee hst hf3.kept hsp3r (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hsp3r hn (by decide),
      ⟨Mapped.keeps hmap hf3.kept, hnw, apart_callee hapS hsp3r hn (by decide), hapR⟩, hsp3,
      got_callee hgot (got_keep hgot hst (writes := [(p, spongeBytes)])
        (by simp [p]) (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact hnw)
        (by simpa [spongeBytes] using hso3))
        hsp3r hn (by decide) (fun l hl => (hgot.1 l hl).2.2.2)⟩
  refine call_then hpc3 (hdup _) hpre3 fun st4 hpc4 hrsp4 ⟨hsp4, hs4, hsv4⟩ => ?_
  rw [hX7'] at hsp4 hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data duplexStack) duplexStack q →
      NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ inRange_callee hsp3r h8 hn (by decide) hq
  have hf4 : Frame m0 16 slots 8 st4.data := by
    refine Frame.call hf3 hsv4 hrsp4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q hq
    · exact (hcal4 q hq).2
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange p 328 q ∨
        NativeRustcVm.InRange (stackBelow m0 absorbNonceStack) absorbNonceStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      rw [hs4 q (fun h ↦ by
        rcases h with h | h
        · exact hq.1 h
        · exact hq.2 (hcal4 q h).1)]
      exact hso3 q (by simp only [not_or]; exact hq)
  -- `b2`: the third lane, the ground challenge, the epilogue.
  set sd := (sp.absorb ⟨.ofBitVec (reg m0 .rsi), .ofBitVec (reg m0 .rdx)⟩ 4).duplex with hsd
  have hX3''' : reg st4.data .rbx = p := (hsv4.1 .rbx rfl).trans hX3''
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 16) (rest := [(p, 328)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩ (hrest _ hf4.kept)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWAbsorbNonce.b1_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl hX3''', trivial⟩ trivial
      trivial trivial) fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hx0'', hwt, hwc0, hwc1, hws5⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hs5 := sameOutside_touch hwf4 hm5 (r := 1) rfl (by decide) hws5
  have hA5 : Agree st4.data.dmem st5.data.dmem p spongeBytes (fun j ↦ 304 ≤ j) :=
    (agree_of_sameOutside (R := fun _ ↦ False) hnw (fun _ h ↦ h.elim)
      (SameOutside.mono hs5 fun _ h ↦ Or.inl h)).mono fun j h ↦ h.1
  have hws := wordsAt_iff.mp hsp4.state
  have hl0 : NativeRustcVm.WordAt st4.data.dmem (off p 0) (sd.state.toList[0]'(by simp)) :=
    hws 0 (by simp)
  have hl1 : NativeRustcVm.WordAt st4.data.dmem (off p 8) (sd.state.toList[1]'(by simp)) :=
    hws 1 (by simp)
  have hl2 : NativeRustcVm.WordAt st4.data.dmem (off p 16) (sd.state.toList[2]'(by simp)) :=
    hws 2 (by simp)
  have ht := wordAt_write hm5 (r := 1) (o := 304) (b := p) (sz := 328) rfl (by decide) hwt
  rw [show UInt64.ofBitVec ((Sym.lit 1).eval
    (frameEnv m0 st4.data 16 [(p, 328)] (fun _ ↦ 0) 0)) = 1 from rfl] at ht
  have hc0 := wordAt_write hm5 (r := 1) (o := 312) (b := p) (sz := 328) rfl (by decide) hwc0
  rw [show (Sym.load 1 0 8).eval (frameEnv m0 st4.data 16 [(p, 328)] (fun _ ↦ 0) 0) = _ from
    load_ofMachine (o := 0) rfl hl0, ofBitVec_toBitVec'] at hc0
  have hc1 := wordAt_write hm5 (r := 1) (o := 320) (b := p) (sz := 328) rfl (by decide) hwc1
  rw [show (Sym.load 1 8 8).eval (frameEnv m0 st4.data 16 [(p, 328)] (fun _ ↦ 0) 0) = _ from
    load_ofMachine (o := 8) rfl hl1, ofBitVec_toBitVec'] at hc1
  have hg : OptEWAt st5.data.dmem (off p 304)
      (some ⟨sd.state.toList[0]'(by simp), sd.state.toList[1]'(by simp)⟩) := by
    refine ⟨ht, ewAt_iff.mpr ⟨?_, ?_⟩⟩
    · rw [off_off]; exact hc0
    · rw [off_off, off_off]; exact hc1
  simp only [PcOk] at hpc5
  refine .done _ ⟨by rw [hpc5]; exact hf4.load_ret hst (by decide), hrsp5, ?_, ?_, ?_, hsv5⟩
  · rw [absorbNonce_eq]
    exact (hm5.regs .rax _ hx0'').trans (load_ofMachine (o := 16) rfl hl2)
  · rw [absorbNonce_eq]
    exact hsp4.with_ground hA5 hg
  · intro q hq
    rw [hs5 q fun h ↦ hq (Or.inl (inRange_of_touch hnw h))]
    exact hso4 q hq

end

end NativeRustcVmX64.Transcript.AbsorbNonce
