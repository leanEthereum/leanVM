module

public import NativeRustcVmX64.Transcript.Duplex.Exec
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput.Names

/-!
# `SpongeW::duplex` on x86-64

**`duplex_spec`**: the sponge at RDI becomes `sp.duplex`, given the contracts of `duplex_input`
and `keccak_f`. The prologue pushes RBX into a 16-byte frame (`Frame`); `duplex_input` writes the
rate lanes; `keccak_f` permutes the 25 lanes, its stack below the frame; `b2` zeroes the queue's
count, pops RBX and returns.
-/

namespace NativeRustcVmX64.Transcript.Duplex

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWDuplex
open NativeRustcVm.Transcript NativeVm.Model

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 16 := by decide

theorem duplex_eq (sp : SpongeW) :
    sp.duplex = { { { sp with state := sp.duplexInput } with
      state := LeanVM.Semantics.keccakF1600 sp.duplexInput } with pending := #[] } := rfl

variable [Host] {k : Nat}

/-- **`SpongeW::duplex` meets its contract.** -/
theorem duplex_spec (hp : Placed code k)
    (hdi : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp))
    (hkf : Spec (Labels.label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp, hgot⟩
  set p := reg m0 .rdi with hpdef
  have hn : duplexStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (F := 16) hst (by decide)
  have hapF : NativeRustcVm.Apart p 328 (stackBelow m0 16) (16 + 8) :=
    apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hrcF : NativeRustcVm.Apart rcAddr 192 (stackBelow m0 16) (16 + 8) :=
    apart_frame hrc.2.2 hn (by decide)
  have hrcnw : NativeRustcVm.NoWrap rcAddr 192 := hrc.2.1
  -- `b0`: the prologue, `call duplex_input`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 16) (rest := [(p, 328)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWDuplex.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hst (by decide), hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hmap, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  unfold NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SpongeWDuplex.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hrdi, hrbx, hw0⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 16 slots 0 st1.data := Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 16) 16) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw0
  have hX0 : reg st1.data .rdi = p := (hm1.regs .rdi _ hrdi).trans (eval_ptr rfl)
  have hX1 : reg st1.data .rbx = p := (hm1.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have hsp1 : rspOf st1.data = stackBelow m0 16 := by rw [hf1.sp, off_zero]
  have hk1 : Kept m0.dmem st1.data.dmem := hf1.kept
  have hsp1' : SpongeAt st1.data.dmem p sp :=
    hsp.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs1
  -- `duplex_input`.
  have hpre1 : DuplexInputPre sp st1.data := by
    refine ⟨stackOk_callee hst hk1 hsp1 (by decide), ?_, ?_⟩
    · rw [hX0]
      exact ⟨Mapped.keeps hmap hk1, hnw,
        apart_callee (n' := duplexInputStack) hapS hsp1 hn (by decide), hapR⟩
    · rw [hX0]; exact hsp1'
  refine call_then hpc1 (hdi sp) hpre1 fun st2 hpc2 hrsp2 ⟨hsp2, hs2, hsv2⟩ => ?_
  rw [hX0] at hsp2 hs2
  have hf2 : Frame m0 16 slots 8 st2.data :=
    Frame.call hf1 hsv2 hrsp2 hs2 (fun q hq ↦ hpF q hq) hfnw slots_le
  -- `b1`: `call keccak_f`.
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 16) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWDuplex.b1Offset + b1.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf2.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 (fun _ _ ↦ rfl)
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWDuplex.b0_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid, hw3, hrdi3, hrbx3⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 16 slots 0 st3.data := Frame.of_block hf2 hwf2 hm3 hmid slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 16) 16) :=
    sameOutside_low hwf2 hm3 (r := 0) rfl (by decide) hw3
  have hX2 : reg st2.data .rbx = p := (hsv2.1 .rbx rfl).trans hX1
  have hX3 : reg st3.data .rdi = p := (hm3.regs .rdi _ hrdi3).trans hX2
  have hX3' : reg st3.data .rbx = p := (hm3.regs .rbx _ hrbx3).trans hX2
  have hsp3 : rspOf st3.data = stackBelow m0 16 := by rw [hf3.sp, off_zero]
  -- `keccak_f`.
  have hnF : ∀ {q : BitVec 64}, NativeRustcVm.InRange rcAddr 192 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 16) 16 q :=
    fun hq h ↦ not_inRange_of_apart hrcF hrcnw hfnw hq (inRange_mono h (by decide))
  have hrc3 : ∀ i < 192, st3.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
    intro i hi
    have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
      inRange_off_self hi (by omega)
    exact (hs3 _ (hnF hq)).trans ((hs2 _ fun h ↦ not_inRange_of_apart (Apart.symm' hapR) hrcnw
      hnw hq h).trans (hs1 _ (hnF hq)))
  have hap200 : NativeRustcVm.Apart p 200 (stackBelow m0 duplexStack) (duplexStack + 8) := by
    have h : NativeRustcVm.Apart p 328 (stackBelow m0 duplexStack) (duplexStack + 8) := hapS
    unfold NativeRustcVm.Apart at h ⊢; omega
  have hapR200 : NativeRustcVm.Apart p 200 rcAddr 192 := by
    have h : NativeRustcVm.Apart p 328 rcAddr 192 := hapR
    unfold NativeRustcVm.Apart at h ⊢; omega
  have hgot3 := got_keep hgot hst (writes := [(p, spongeBytes)])
    (by simp [p]) (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact hnw)
    (d := st3.data) (by
      intro q hq
      have hpq : ¬ NativeRustcVm.InRange p spongeBytes q :=
        fun h => hq (Or.inl ⟨(p, spongeBytes), by simp, h⟩)
      have hsq : ¬ NativeRustcVm.InRange (stackBelow m0 duplexStack) duplexStack q :=
        fun h => hq (Or.inr h)
      have hfq : ¬ NativeRustcVm.InRange (stackBelow m0 16) 16 q :=
        fun h => hsq (inRange_frame_stack h8 hn (by decide) h)
      exact (hs3 q hfq).trans ((hs2 q hpq).trans (hs1 q hfq)))
  have hpre3 : KeccakFPre st3.data := by
    unfold KeccakFPre
    rw [hX3]
    exact ⟨stackOk_callee hst hf3.kept hsp3 (by decide), RcAt.callee hrc hrc3 hsp3 hn (by decide),
      fun i hi ↦ Mapped.keeps hmap hf3.kept i (by unfold spongeBytes; omega), show p.toNat + 200 ≤ 2 ^ 64 by omega,
      apart_callee hap200 hsp3 hn (by decide), hapR200,
      got_callee hgot hgot3 hsp3 hn (by decide) (by
        intro l hl b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact Apart.sub ((hgot.1 l hl).2.2.2 (p, spongeBytes) (by simp [p]))
            (Nat.le_refl _) (by simp only [spongeBytes]; omega)
        · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp))⟩
  refine call_then hpc3 hkf hpre3 fun st4 hpc4 hrsp4 ⟨hkw, hs4, hsv4⟩ => ?_
  rw [hX3] at hkw hs4
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st3.data keccakFStack) keccakFStack q →
      NativeRustcVm.InRange (stackBelow m0 duplexStack) duplexStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 16) (16 + 8) q :=
    fun q hq ↦ inRange_callee hsp3 h8 hn (by decide) hq
  have hf4 : Frame m0 16 slots 8 st4.data := by
    refine Frame.call hf3 hsv4 hrsp4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact hpF q (inRange_mono hq (by decide))
    · exact (hcal q hq).2
  -- The lanes permuted, the rest of the sponge kept.
  have hsp2' : SpongeAt st3.data.dmem p { sp with state := sp.duplexInput } :=
    hsp2.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs3
  have hstnw : NativeRustcVm.NoWrap (stackBelow m0 duplexStack) duplexStack := stack_noWrap hst
  have hA4 : Agree st3.data.dmem st4.data.dmem p spongeBytes (· < 200) := by
    refine agree_of_sameOutside (R := fun q ↦
      NativeRustcVm.InRange (stackBelow st3.data keccakFStack) keccakFStack q) hnw
      (fun q hq h ↦ ?_) (SameOutside.mono hs4 fun q hq ↦ ?_)
    · have h' : NativeRustcVm.Apart (stackBelow m0 duplexStack) duplexStack p 328 := by
        have h0 : NativeRustcVm.Apart p 328 (stackBelow m0 duplexStack) (duplexStack + 8) := hapS
        unfold NativeRustcVm.Apart at h0 ⊢; omega
      exact not_inRange_of_apart h' hstnw hnw (hcal q hq).1 h
    · rcases hq with hq | hq
      · obtain ⟨j, hj, hw, rfl⟩ := touch_of_inRange (b := p) (o := 0) (n := 200) (N := 328) hnw
          (by decide) (by rwa [off_zero])
        exact Or.inl ⟨j, hj, by omega, rfl⟩
      · exact Or.inr hq
  have hsp4 : SpongeAt st4.data.dmem p
      { { sp with state := sp.duplexInput } with
        state := LeanVM.Semantics.keccakF1600 sp.duplexInput } :=
    hsp2'.with_state hA4 (hkw _ hsp2'.state)
  -- `b2`: the count zeroed, the epilogue.
  have hX4 : reg st4.data .rbx = p := (hsv4.1 .rbx rfl).trans hX3'
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 16) (rest := [(p, 328)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hmap hf4.kept, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWDuplex.b1_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl hX4, trivial⟩ trivial
      trivial trivial) fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hw5, hws5⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hs5 := sameOutside_touch hwf4 hm5 (r := 1) rfl (by decide) hws5
  have hA5 : Agree st4.data.dmem st5.data.dmem p spongeBytes (fun j ↦ 200 ≤ j ∧ j < 304) :=
    (agree_of_sameOutside (R := fun _ ↦ False) hnw (fun _ h ↦ h.elim)
      (SameOutside.mono hs5 fun _ h ↦ Or.inl h)).mono fun j h ↦ by omega
  simp only [PcOk] at hpc5
  refine .done _ ⟨by rw [hpc5]; exact hf4.load_ret hst (by decide), hrsp5, ?_, ?_, hsv5⟩
  · have hw296 := wordAt_write hm5 (r := 1) (o := 296) (b := p) (sz := 328) rfl (by decide) hw5
    have hw0 : NativeRustcVm.WordAt st5.data.dmem (off p 296)
        (#[] : Array (EW × UInt64)).size.toUInt64 := hw296
    have hle0 : (#[] : Array (EW × UInt64)).size ≤ 4 := Nat.zero_le _
    rw [duplex_eq]
    exact hsp4.with_pending hA5 hle0 hw0 nofun
  · intro q hq
    simp only [not_or] at hq
    obtain ⟨hqp, hqs⟩ := hq
    have hqf : ¬ NativeRustcVm.InRange (stackBelow m0 16) 16 q :=
      fun h ↦ hqs (inRange_frame_stack h8 hn (by decide) h)
    refine (hs5 q fun h ↦ hqp (inRange_of_touch hnw' h)).trans
      ((hs4 q fun h ↦ ?_).trans ((hs3 q hqf).trans ((hs2 q hqp).trans (hs1 q hqf))))
    rcases h with h | h
    · exact hqp (inRange_mono h (by decide))
    · exact hqs (hcal q h).1

end

end NativeRustcVmX64.Transcript.Duplex
