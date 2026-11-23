module

public import NativeRustcVmX64.Transcript.Absorb.Tail
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names

/-!
# `SpongeW::absorb` on x86-64

**`absorb_spec`**: the sponge at RDI becomes `sp.absorb ⟨RSI, RDX⟩ RCX`, given `duplex`'s
contract. The prologue (`b0`) pushes five registers and compares the queue's count with `4`;
below it, the scalar is pushed (`tail`); at `4`, `duplex` empties the queue (`b1`), the count is
reloaded (`b2`, `0`), and the scalar pushed.
-/

namespace NativeRustcVmX64.Transcript.Absorb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWAbsorb
open NativeRustcVm.Transcript NativeVm.Model LeanVM.Protocol.Compile

public section

theorem absorb_lt {sp : SpongeW} (h : sp.pending.size ≠ rateScalars) (x : EW) (tag : UInt64) :
    sp.absorb x tag = { sp with pending := sp.pending.push (x, tag) } := by
  simp only [SpongeW.absorb, h, ite_false]

theorem absorb_eq {sp : SpongeW} (h : sp.pending.size = rateScalars) (x : EW) (tag : UInt64) :
    sp.absorb x tag = { sp.duplex with pending := sp.duplex.pending.push (x, tag) } := by
  simp only [SpongeW.absorb, h, ite_true]

theorem toNat_toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

variable [Host] {k : Nat}

/-- **`SpongeW::absorb` meets its contract.** -/
theorem absorb_spec (hp : Placed code k)
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp, hgot⟩
  set p := reg m0 .rdi with hpdef
  have hn : absorbStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hfnw := frame_noWrap (F := 48) hst (by decide)
  have hapF : NativeRustcVm.Apart p 328 (stackBelow m0 48) (48 + 8) :=
    apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 48) (48 + 8) q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hle := hsp.pending_le
  unfold rateScalars at hle
  -- `b0`: the prologue, the count against `4`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 48) (rest := [(p, 328)]) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hmap, hnw⟩)
    (List.pairwise_pair.mpr (Apart.symm' hapF))
  obtain ⟨x0, hrun0, hpro, hw0, hx0, hx3, hx12, hx15, hx14, rfl⟩ := ok_b0
  unfold NativeRustcVmX64.Vm.SpongeWAbsorb.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SpongeWAbsorb.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) hrun0 hwf0 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial) fun st1 hm1 hpc1 => ?_
  have hf1 : Frame m0 48 slots 8 st1.data := Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 48) 48) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw0
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack h8 hn (by decide) hq)
  have hsp1 : SpongeAt st1.data.dmem p sp :=
    hsp.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs1
  have hcnt : (frameEnv m0 m0 48 [(p, 328)] (fun _ ↦ 0) 0).load 1 296 8 =
      sp.pending.size.toUInt64.toBitVec :=
    load_ofMachine (o := 296) rfl hsp.n_pending
  have hX0 : reg st1.data .rax = BitVec.ofNat 64 sp.pending.size :=
    (hm1.regs .rax _ hx0).trans hcnt
  have hX3 : reg st1.data .rbx = p := (hm1.regs .rbx _ hx3).trans (eval_ptr rfl)
  have hX12 : reg st1.data .r12 = reg m0 .rsi := hm1.regs .r12 _ hx12
  have hX15 : reg st1.data .r15 = reg m0 .rdx := hm1.regs .r15 _ hx15
  have hX14 : reg st1.data .r14 = reg m0 .rcx := hm1.regs .r14 _ hx14
  simp only [PcOk] at hpc1
  sym_simp_at hpc1
  rw [hcnt] at hpc1
  have hlt4 : (BitVec.ult sp.pending.size.toUInt64.toBitVec (BitVec.ofNat 64 4)) =
      decide (sp.pending.size < 4) := by
    simp only [BitVec.ult, toNat_toBitVec_toUInt64 (show sp.pending.size < 2 ^ 64 by omega),
      BitVec.toNat_ofNat]
  rw [hlt4] at hpc1
  by_cases h4 : sp.pending.size < 4
  · -- Below `4`: the push.
    simp only [h4, decide_true, ite_true] at hpc1
    have := tail hp hst hmap hnw hapF (hpc1.trans (hp.label NativeRustcVmX64.Vm.SpongeWAbsorb.label_2_at)) hf1 h4 hX0 hX14 hX3
      hX15 hX12 hsp1 hso1
    refine Eventually.mono this fun st' ⟨hpc', hrsp', hsp', hso', hsv'⟩ ↦
      ⟨hpc', hrsp', ?_, hso', hsv'⟩
    rw [absorb_lt (by unfold rateScalars; omega)]
    exact hsp'
  · -- At `4`: `duplex`, then the push.
    simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have h4' : sp.pending.size = 4 := by omega
    -- `b1`: `call duplex`.
    have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 48) (rest := []) (vars := fun _ ↦ 0)
      (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SpongeWAbsorb.b1Offset + b1.length)).toBitVec)
      ⟨Mapped.keeps (frame_mapped hst (by decide)) hf1.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1 (fun _ _ ↦ rfl)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWAbsorb.b0_next))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st2 hm2 hpc2 => ?_
    obtain ⟨hmid2, hw2, hx7', hx3', hx12', hx14', hx15'⟩ := after_eq run_b1 ▸ ok_b1
    have hf2 : Frame m0 48 slots 0 st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
    have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 48) 8) :=
      sameOutside_low hwf1 hm2 (r := 0) rfl (by decide) hw2
    have hX7' : reg st2.data .rdi = p := (hm2.regs .rdi _ hx7').trans hX3
    have hsp2r : rspOf st2.data = stackBelow m0 48 := by rw [hf2.sp, off_zero]
    -- `duplex`.
    have hrc2 : ∀ i < 192, st2.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
        m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
      intro i hi
      have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
        inRange_off_self hi (by have := hrc.2.1; unfold NativeRustcVm.NoWrap at this; omega)
      have hnF : ∀ {c : Nat}, c ≤ 48 + 8 → ¬ NativeRustcVm.InRange (stackBelow m0 48) c
          (rcAddr + BitVec.ofNat 64 i) := fun hc h ↦
        not_inRange_of_apart (apart_frame hrc.2.2 hn (by decide)) hrc.2.1 hfnw hq
          (inRange_mono h hc)
      exact (hs2 _ (hnF (by decide))).trans (hs1 _ (hnF (by decide)))
    have hsp2 : SpongeAt st2.data.dmem p sp :=
      hsp1.frame hnw (fun q hq h ↦ hpF q h (inRange_mono hq (by decide))) hs2
    have hgot2 := got_keep hgot hst (writes := [(p, spongeBytes)])
      (by simp [p]) (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact hnw)
      (d := st2.data) (by
        intro q hq
        have hs : ¬ NativeRustcVm.InRange (stackBelow m0 absorbStack) absorbStack q :=
          fun h => hq (Or.inr h)
        exact (hs2 q fun h => hs (inRange_frame_stack h8 hn (by decide)
          (inRange_mono h (by decide)))).trans
          (hs1 q fun h => hs (inRange_frame_stack h8 hn (by decide) h)))
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
        NativeRustcVm.InRange (stackBelow m0 absorbStack) absorbStack q ∧
          ¬ NativeRustcVm.InRange (stackBelow m0 48) (48 + 8) q :=
      fun q hq ↦ inRange_callee hsp2r h8 hn (by decide) hq
    have hf3 : Frame m0 48 slots 8 st3.data := by
      refine Frame.call hf2 hsv3 hrsp3 hs3 (fun q hq ↦ ?_) hfnw slots_le
      rcases hq with hq | hq
      · exact hpF q hq
      · exact (hcal q hq).2
    -- `b2`: the count reloaded.
    have hreg3 : ∀ r, calleeSaved r = true → (after b1 callS).reg r = some (.reg r) →
        reg st3.data r = reg st1.data r :=
      fun r hr h ↦ (hsv3.1 r hr).trans (hm2.regs r _ h)
    have hX3'' : reg st3.data .rbx = p := (hreg3 .rbx rfl hx3').trans hX3
    have hwf3 := frame_wf (m0 := m0) (d := st3.data) (F := 48) (rest := [(p, 328)])
      (vars := fun _ ↦ 0) (ret := 0)
      ⟨Mapped.keeps (frame_mapped hst (by decide)) hf3.kept, hfnw⟩
      (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps hmap hf3.kept, hnw⟩)
      (List.pairwise_pair.mpr (Apart.symm' hapF))
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
      (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SpongeWAbsorb.b1_next))
      (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.rsp_eval, known_ptr rfl hX3'', trivial⟩ trivial
        trivial trivial) fun st4 hm4 hpc4 => ?_
    obtain ⟨hmid4, hmem4, hx0'', hx3''', hx12'', hx14'', hx15''⟩ := after_eq run_b2 ▸ ok_b2
    have hf4 : Frame m0 48 slots 8 st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
    have hcnt3 : (frameEnv m0 st3.data 48 [(p, 328)] (fun _ ↦ 0) 0).load 1 296 8 =
        (sp.duplex.pending.size).toUInt64.toBitVec :=
      load_ofMachine (o := 296) rfl hsp3.n_pending
    have hdz : sp.duplex.pending.size = 0 := rfl
    simp only [PcOk] at hpc4
    sym_simp_at hpc4
    rw [hcnt3, hdz] at hpc4
    simp only [show (Nat.toUInt64 0).toBitVec = 0#64 from rfl] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    rw [NativeRustcVmX64.Vm.SpongeWAbsorb.b2_length] at hpc4
    have hreg4 : ∀ r, calleeSaved r = true → (after b1 callS).reg r = some (.reg r) →
        (after b2 reloadS).reg r = some (.reg r) → reg st4.data r = reg st1.data r :=
      fun r hr h1 h2 ↦ (hm4.regs r _ h2).trans (hreg3 r hr h1)
    have hX0'' : reg st4.data .rax = BitVec.ofNat 64 sp.duplex.pending.size :=
      (hm4.regs .rax _ hx0'').trans hcnt3
    have hX34 : reg st4.data .rbx = p := (hm4.regs .rbx _ hx3''').trans (eval_ptr rfl)
    have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦ by
      simp only [not_or] at hq
      rw [hd4, hs3 q (fun h ↦ by
          rcases h with h | h
          · exact hq.1 h
          · exact hq.2 (hcal q h).1)]
      refine (hs2 q fun h ↦ hq.2 (inRange_frame_stack h8 hn (by decide)
        (inRange_mono h (by decide)))).trans ?_
      exact hso1 q (by simp only [not_or]; exact hq)
    have := tail hp hst hmap hnw hapF (hpc4.trans (by rfl)) hf4 (by rw [hdz]; omega) hX0''
      ((hreg4 .r14 rfl hx14' hx14'').trans hX14) hX34
      ((hreg4 .r15 rfl hx15' hx15'').trans hX15) ((hreg4 .r12 rfl hx12' hx12'').trans hX12)
      (hd4 ▸ hsp3) hso4
    refine Eventually.mono this fun st' ⟨hpc', hrsp', hsp', hso', hsv'⟩ ↦
      ⟨hpc', hrsp', ?_, hso', hsv'⟩
    rw [absorb_eq (by unfold rateScalars; omega)]
    exact hsp'

end

end NativeRustcVmX64.Transcript.Absorb
