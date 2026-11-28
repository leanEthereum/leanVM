module

public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Transcript.ReadScalar.Exec
public import NativeVm.Equiv.Transcript

/-!
# `TState::read_scalar` on AArch64

**`readScalar_spec`**: the `Option<EW>` at X0 becomes `readScalar`'s element and the `TState` at X1
its state, given the contracts of `next_scalar` and `absorb`. `b0` saves X30, X22 to X19 and calls
`next_scalar` with its output in the frame; `b1` tests its tag: `0`, `b4` stores it; `1`, `b2`
absorbs the element with the tag `1` (`dsObserve`) and `b3` copies it to the output.
-/

namespace NativeRustcVmArm.Transcript.ReadScalar

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadScalar
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem run_none {s : TState} (h : nextScalar.run s = none) : readScalar.run s = none := by
  rw [NativeVm.Equiv.readScalar_run, h]; rfl

theorem run_some {s s1 : TState} {x : EW} (h : nextScalar.run s = some (x, s1)) :
    readScalar.run s = some (x, { s1 with sponge := s1.sponge.absorb x 1 }) := by
  rw [NativeVm.Equiv.readScalar_run, h]; rfl

variable [Host] {k : Nat}

/-- **`TState::read_scalar` meets its contract.** -/
theorem readScalar_spec (hp : Placed code k)
    (hns : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s))
    (habs : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, -⟩⟩
  set t := m0.regs.X1.toBitVec with htdef
  set o := m0.regs.X0.toBitVec with hodef
  set fb := frameBase m0 80 with hfb
  have hN : readScalarStack = 544 := rfl
  have hn : readScalarStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 80 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 80) (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hTF : NativeRustcVm.Apart t 760 fb 80 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 80 := apart_frame htok.2.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o 24 fb 80 := apart_frame hoS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb 80 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hslot : ∀ p ∈ slots, ∀ i < 8, NativeRustcVm.InRange fb 80 (off fb (p.1 + i)) :=
    fun p hp i hi ↦ inRange_off_self (by have := slots_le p hp; omega) (by omega)
  -- The stack apart from the `TState` and the area.
  have hRS : ∀ q, NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    have hsnw : NativeRustcVm.NoWrap (stackBelow m0 readScalarStack) readScalarStack := by
      show _ + readScalarStack ≤ _
      rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
    exact fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h hq,
      fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h hq⟩
  -- `b0`: the prologue, `bl next_scalar`.
  have hwf0 : (frameEnv m0 m0 80 []).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 80) hst (by decide), hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 80 []) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      frameBase_add.symm trivial trivial trivial trivial
  unfold NativeRustcVmArm.Vm.TStateReadScalar.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateReadScalar.entryOffset) NativeRustcVmArm.Vm.TStateReadScalar.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx0, hx1, hx19, hx20⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 80 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
    sameOutside_region hwf0 hm1 rfl hws1
  have hX0 : st1.data.regs.X0.toBitVec = off fb 8 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ hx0]; rfl
  have hX1 : st1.data.regs.X1.toBitVec = t := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [hm1.regs .X1 _ hx1]; rfl
  have hX19 : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX20 : st1.data.regs.X20 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ hx20)
  have hts1 : TStateAt st1.data.dmem t a s := hts.frame hf1.kept hRF hs1
  -- `next_scalar`, its output at `fb + 8`.
  have hpre1 : NextScalarPre a s st1.data := by
    unfold NextScalarPre
    rw [hX1, hX0]
    exact ⟨stackOk_callee hst hf1.kept hf1.sp (by decide) (by decide) (by decide), hts1,
      TStateOk.callee htok hf1.sp hn (by decide) (by decide),
      OutOk.frame hst (by decide) (by decide) hf1.sp hf1.kept (by decide) htok hrc⟩
  refine call_then hpc1 (hns a s) hpre1 fun st2 hpc2 ⟨hout2, hnext2, hs2, hsv2⟩ => ?_
  rw [hX0] at hout2
  rw [hX0, hX1] at hs2
  rw [hX1] at hnext2
  have hcal2 : ∀ q, NativeRustcVm.InRange (stackBelow st1.data nextScalarStack) nextScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q ∧
        ¬ NativeRustcVm.InRange fb 80 q :=
    fun q hq ↦ inRange_callee hf1.sp hn (by decide) (by decide) hq
  have hf2 : Frame m0 80 slots st2.data := by
    refine Frame.call_slots hf1 hsv2 hs2 fun p hp i hi h ↦ ?_
    rcases h with h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p hp i hi h
    · exact not_inRange_of_apart hTF hTn hfnw h (hslot p hp i hi)
    · exact (hcal2 _ h).2 (hslot p hp i hi)
  have hso2 : SameOutside m0.dmem st2.data.dmem (fun q ↦ NativeRustcVm.InRange t 760 q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    have hqf : ¬ NativeRustcVm.InRange fb 80 q :=
      fun h ↦ hq.2 (inRange_frame_stack hn (by decide) h)
    rw [hs2 q (by
      rintro (h | h | h)
      · exact hqf (inRange_of_off hfnw (by decide) h)
      · exact hq.1 h
      · exact hq.2 (hcal2 q h).1)]
    exact hs1 q hqf
  have hX19₂ : st2.data.regs.X19 = m0.regs.X0 := (hsv2.1 .X19 rfl).trans hX19
  have hX20₂ : st2.data.regs.X20 = m0.regs.X1 := (hsv2.1 .X20 rfl).trans hX20
  -- `b1`: the tag.
  have hwf2 : (frameEnv m0 st2.data 80 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf2.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st2.data 80 []) tagS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalar.b0Offset + NativeRustcVmArm.Vm.TStateReadScalar.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadScalar.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalar.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx19₃, hx20₃⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 80 slots st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hX19₃ : st3.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq (r := .X19) hm2 hm3 rfl hx19₃).trans hX19₂
  have hX20₃ : st3.data.regs.X20 = m0.regs.X1 :=
    (Match.reg_eq (r := .X20) hm2 hm3 rfl hx20₃).trans hX20₂
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  cases hns2 : nextScalar.run s with
  | none =>
    -- `None`: the tag `0` stored.
    rw [hns2] at hout2
    have h0 : NativeRustcVm.WordAt st2.data.dmem (off fb 8) 0 := hout2
    have ht0 : (frameEnv m0 st2.data 80 []).load 0 8 8 = (0 : UInt64).toBitVec :=
      load_ofMachine (o := 8) rfl h0
    rw [ht0] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    have hwf3 : (frameEnv m0 st3.data 80 [(o, 24)]).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf3.kept, hfnw⟩,
        ⟨Mapped.keeps hom hf3.kept, hon⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hoF))
    have hm3' : Match (frameEnv m0 st3.data 80 [(o, 24)]) noneS st3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
        (by rw [hf3.sp]; exact (eval_ptr rfl).symm)
        ⟨known_ptr rfl (by show st3.data.regs.X19.toBitVec = _; rw [hX19₃]), trivial⟩ trivial
        trivial trivial
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf3
      (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadScalar.b4Offset) NativeRustcVmArm.Vm.TStateReadScalar.label_2_at)) hm3' fun st4 hm4 hpc4 => ?_
    obtain ⟨hepi, hw0, hws4⟩ := after_eq run_b4 ▸ ok_b4
    obtain ⟨hsv4, hsl4⟩ := Frame.epilogue hf3 hwf3 hm4 hepi
    have hx30 : st4.data.regs.X30 = m0.regs.X30 := hsl4 (32, .X30) (List.mem_cons_self ..)
    have ht := wordAt_write hm4 (r := 1) (o := 0) (b := o) (sz := 24) rfl (by decide) hw0
    rw [off_zero, show UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 st3.data 80 [(o, 24)])) = 0
      from rfl] at ht
    have hs4 := sameOutside_region hwf3 hm4 (r := 1) rfl hws4
    refine .done _ ⟨by simp only [PcOk] at hpc4; rw [hpc4]; simp only [retOf, hx30], ?_, ?_, ?_,
      hsv4⟩
    · rw [run_none hns2]; exact ht
    · rw [run_none hns2]; intro x s' h; cases h
    · intro q hq
      simp only [not_or] at hq
      rw [hs4 q hq.1]
      show st3.data.dmem.get? q = _
      rw [hd3]
      exact hso2 q (by simp only [not_or]; exact hq.2)
  | some p =>
  obtain ⟨x, s1⟩ := p
  rw [hns2] at hout2
  obtain ⟨ht1, hel⟩ := (hout2 : OptEWAt st2.data.dmem (off fb 8) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts2 : TStateAt st2.data.dmem t a s1 := hnext2 x s1 hns2
  have ht1' : (frameEnv m0 st2.data 80 []).load 0 8 8 = (1 : UInt64).toBitVec :=
    load_ofMachine (o := 8) rfl ht1
  rw [ht1'] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: `bl absorb`.
  have hwf3 : (frameEnv m0 st3.data 80 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf3.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm3' : Match (frameEnv m0 st3.data 80 []) callS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
    (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalar.b1_next])) hm3' fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx0₄, hx1₄, hx2₄, hx3₄, hx19₄, hx20₄, hx21₄, hx22₄⟩ :=
    after_eq run_b2 ▸ ok_b2
  have hf4 : Frame m0 80 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hc0 : (frameEnv m0 st3.data 80 []).load 0 16 8 = x.c0.toBitVec :=
    load_ofMachine (o := 16) rfl (hd3 ▸ hel.1)
  have hc1 : (frameEnv m0 st3.data 80 []).load 0 24 8 = x.c1.toBitVec :=
    load_ofMachine (o := 24) rfl (hd3 ▸ hel.2)
  have hX0₄ : st4.data.regs.X0.toBitVec = t := by
    show (st4.data.regs.getXReg .X0).toBitVec = _
    rw [hm4.regs .X0 _ hx0₄]
    show st3.data.regs.X20.toBitVec = _
    rw [hX20₃]
  have hX1₄ : st4.data.regs.X1 = x.c0 := UInt64.toBitVec_inj.mp ((hm4.regs .X1 _ hx1₄).trans hc0)
  have hX2₄ : st4.data.regs.X2 = x.c1 := UInt64.toBitVec_inj.mp ((hm4.regs .X2 _ hx2₄).trans hc1)
  have hX3₄ : st4.data.regs.X3 = 1 := UInt64.toBitVec_inj.mp (hm4.regs .X3 _ hx3₄)
  have hX19₄ : st4.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq (r := .X19) hm3' hm4 rfl hx19₄).trans hX19₃
  have hX20₄ : st4.data.regs.X20 = 1 := UInt64.toBitVec_inj.mp (hm4.regs .X20 _ hx20₄)
  have hX21₄ : st4.data.regs.X21 = x.c0 := UInt64.toBitVec_inj.mp ((hm4.regs .X21 _ hx21₄).trans hc0)
  have hX22₄ : st4.data.regs.X22 = x.c1 := UInt64.toBitVec_inj.mp ((hm4.regs .X22 _ hx22₄).trans hc1)
  -- `absorb`.
  have h4sp : st4.data.regs.SP.toNat = m0.regs.SP.toNat - 80 := by
    rw [← UInt64.toNat_toBitVec, hf4.sp, frameBase_toNat hn (by decide)]
  have hrcOut : ∀ q, (NativeRustcVm.InRange t 760 q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    have hsnw : NativeRustcVm.NoWrap (stackBelow m0 readScalarStack) readScalarStack := by
      show _ + readScalarStack ≤ _
      rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hso4 : SameOutside m0.dmem st4.data.dmem (fun q ↦ NativeRustcVm.InRange t 760 q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := by
    rw [hd4, hd3]; exact hso2
  have hts4 : TStateAt st4.data.dmem t a s1 := by rw [hd4, hd3]; exact hts2
  have hpre4 : AbsorbPre s1.sponge st4.data := by
    unfold AbsorbPre
    rw [hX0₄]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 readScalarStack).toNat ∨
        (stackBelow m0 readScalarStack).toNat + readScalarStack ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf4.kept hf4.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso4 hrcOut) hn (by decide) h4sp (by decide),
      ⟨fun i hi ↦ hts4.footprint.1.1 i (by simp only [spongeBytes] at hi; show i < 760; omega), ?_,
        apart_callee (n := readScalarStack) (F := 80) ?_ hf4.sp hn (by decide) (by decide), ?_⟩,
      hts4.sponge⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
  refine call_then hpc4 (habs s1.sponge) hpre4 fun st5 hpc5 ⟨hsp5, hs5, hsv5⟩ => ?_
  rw [hX0₄, hX1₄, hX2₄, hX3₄] at hsp5
  rw [hX0₄] at hs5
  have hcal5 : ∀ q, NativeRustcVm.InRange (stackBelow st4.data absorbStack) absorbStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q ∧
        ¬ NativeRustcVm.InRange fb 80 q :=
    fun q hq ↦ inRange_callee hf4.sp hn (by decide) (by decide) hq
  have hf5 : Frame m0 80 slots st5.data := by
    refine Frame.call hf4 hsv5 hs5 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw
        (inRange_sub hTn (le_refl _) (by simp only [spongeBytes]; omega) hq)
    · exact (hcal5 q hq).2
  have hts5 : TStateAt st5.data.dmem t a { s1 with sponge := s1.sponge.absorb x 1 } := by
    refine hts4.with_sponge hsv5.2.2 (fun q hq ↦ hRS q (hcal5 q hq).1) (fun q hq ↦ hs5 q ?_) hsp5
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hso5 : SameOutside m0.dmem st5.data.dmem (fun q ↦ NativeRustcVm.InRange t 760 q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs5 q (by
      rintro (h | h)
      · exact hq.1 (inRange_sub hTn (le_refl _) (by simp only [spongeBytes]; omega) h)
      · exact hq.2 (hcal5 q h).1)]
    exact hso4 q (by simp only [not_or]; exact hq)
  -- `b3`: the element and the tag stored, the epilogue.
  have hX19₅ : st5.data.regs.X19 = m0.regs.X0 := (hsv5.1 .X19 rfl).trans hX19₄
  have hwf5 : (frameEnv m0 st5.data 80 [(o, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf5.kept, hfnw⟩,
      ⟨Mapped.keeps hom hf5.kept, hon⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hoF))
  have hm5 : Match (frameEnv m0 st5.data 80 [(o, 24)]) storeS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf5.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st5.data.regs.X19.toBitVec = _; rw [hX19₅]), trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf5
    (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadScalar.b2_next])) hm5 fun st6 hm6 hpc6 => ?_
  obtain ⟨hepi, hw0, hw1, hw2, hws6⟩ := after_eq run_b3 ▸ ok_b3
  obtain ⟨hsv6, hsl6⟩ := Frame.epilogue hf5 hwf5 hm6 hepi
  have hx30 : st6.data.regs.X30 = m0.regs.X30 := hsl6 (32, .X30) (List.mem_cons_self ..)
  have hs6 := sameOutside_region hwf5 hm6 (r := 1) rfl hws6
  have h20 : st5.data.regs.X20 = 1 := (hsv5.1 .X20 rfl).trans hX20₄
  have h21 : st5.data.regs.X21 = x.c0 := (hsv5.1 .X21 rfl).trans hX21₄
  have h22 : st5.data.regs.X22 = x.c1 := (hsv5.1 .X22 rfl).trans hX22₄
  have ht := wordAt_write hm6 (r := 1) (o := 0) (b := o) (sz := 24) rfl (by decide) hw0
  rw [off_zero, show UInt64.ofBitVec ((Sym.reg .X20).eval (frameEnv m0 st5.data 80 [(o, 24)])) = 1
    from by show UInt64.ofBitVec st5.data.regs.X20.toBitVec = 1; rw [h20]]
    at ht
  have hw0' := wordAt_write hm6 (r := 1) (o := 8) (b := o) (sz := 24) rfl (by decide) hw1
  rw [show UInt64.ofBitVec ((Sym.reg .X21).eval (frameEnv m0 st5.data 80 [(o, 24)])) = x.c0
    from by show UInt64.ofBitVec st5.data.regs.X21.toBitVec = _; rw [h21]]
    at hw0'
  have hw1' := wordAt_write hm6 (r := 1) (o := 16) (b := o) (sz := 24) rfl (by decide) hw2
  rw [show UInt64.ofBitVec ((Sym.reg .X22).eval (frameEnv m0 st5.data 80 [(o, 24)])) = x.c1
    from by show UInt64.ofBitVec st5.data.regs.X22.toBitVec = _; rw [h22]]
    at hw1'
  refine .done _ ⟨by simp only [PcOk] at hpc6; rw [hpc6]; simp only [retOf, hx30], ?_, ?_, ?_,
    hsv6⟩
  · rw [run_some hns2]
    exact ⟨ht, ewAt_iff.mpr ⟨hw0', by rw [off_off]; exact hw1'⟩⟩
  · rw [run_some hns2]
    intro x' s' h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts5.frame (hm6.kept hwf5) (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq h,
      fun h ↦ not_inRange_of_apart hoA hon hAn hq h⟩) hs6
  · intro q hq
    simp only [not_or] at hq
    rw [hs6 q hq.1]
    exact hso5 q (by simp only [not_or]; exact hq.2)

end

end NativeRustcVmArm.Transcript.ReadScalar
