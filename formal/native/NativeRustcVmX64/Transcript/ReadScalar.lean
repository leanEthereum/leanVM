module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Transcript.ReadScalar.Exec
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `TState::read_scalar` on x86-64

**`readScalar_spec`**: the `Option<EW>` at RDI becomes `readScalar`'s element and the `TState` at
RSI its state, given the contracts of `next_scalar` and `absorb`. `b0` pushes R15 to RBX and calls
`next_scalar` with its output in the frame; `b1` tests its tag: `0`, `b4`, `b5` store it; `1`,
`b2` absorbs the element with the tag `1` (`dsObserve`) and `b3`, `b5` copy it to the output.
-/

namespace NativeRustcVmX64.Transcript.ReadScalar

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadScalar
open NativeRustcVm.Transcript NativeVm.Model

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
    (hns : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s))
    (habs : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, -⟩, hgot⟩
  set t := reg m0 .rsi with htdef
  set o := reg m0 .rdi with hodef
  set fb := stackBelow m0 80 with hfb
  have hn : readScalarStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (80 + 8) := frame_noWrap hst (by decide)
  have hfnw80 : NativeRustcVm.NoWrap fb 80 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hTF : NativeRustcVm.Apart t 760 fb (80 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (80 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o 24 fb (80 + 8) := apart_frame hoS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (80 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 readScalarStack) readScalarStack :=
    stack_noWrap hst
  -- The stack apart from the `TState` and the area.
  have hRS : ∀ q, NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn (noWrap_stackBelow hst) h
        (inRange_mono hq (by omega)),
      fun h ↦ not_inRange_of_apart htok.2.1 hAn (noWrap_stackBelow hst) h
        (inRange_mono hq (by omega))⟩
  have hfS : ∀ q, NativeRustcVm.InRange fb 80 q →
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q :=
    fun q h ↦ inRange_frame_stack h8 hn (by decide) h
  -- `b0`: the prologue, `call next_scalar`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  unfold NativeRustcVmX64.Vm.TStateReadScalar.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateReadScalar.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx7, hx6, hx14, hx3⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 80 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hsp1 : rspOf st1.data = fb := by rw [hf1.sp, off_zero]
  have hX7 : reg st1.data .rdi = off fb 16 := (hm1.regs .rdi _ hx7).trans (eval_ptr0 16)
  have hX6 : reg st1.data .rsi = t := hm1.regs .rsi _ hx6
  have hX14 : reg st1.data .r14 = t := hm1.regs .r14 _ hx14
  have hX3 : reg st1.data .rbx = o := hm1.regs .rbx _ hx3
  have hts1 : TStateAt st1.data.dmem t a s :=
    hts.frame hf1.kept (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs1
  -- `next_scalar`, its output at `fb + 16`.
  have hpre1 : NextScalarPre a s st1.data := by
    unfold NextScalarPre
    rw [hX6, hX7]
    exact ⟨stackOk_callee hst hf1.kept hsp1 (by decide), hts1,
      TStateOk.callee htok hsp1 hn (by decide),
      OutOk.frame hst (by decide) hsp1 hf1.kept (by decide) (by decide) htok hrc⟩
  refine call_then hpc1 (hns a s) hpre1 fun st2 hpc2 hrsp2 ⟨hout2, hnext2, hs2, hsv2⟩ => ?_
  rw [hX7] at hout2
  rw [hX7, hX6] at hs2
  rw [hX6] at hnext2
  have hcal2 : ∀ q, NativeRustcVm.InRange (stackBelow st1.data nextScalarStack) nextScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q ∧
        ¬ NativeRustcVm.InRange fb (80 + 8) q :=
    fun q hq ↦ inRange_callee hsp1 h8 hn (by decide) hq
  have hslot : ∀ j, 16 + 24 ≤ j → j < 80 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 16) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data nextScalarStack) nextScalarStack q) := by
    rintro j hj1 hj2 q rfl (h | h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact not_inRange_of_apart hTF hTn hfnw h (inRange_off_self hj2 (by omega))
    · exact (hcal2 _ h).2 (inRange_off_self hj2 (by omega))
  have hf2 : Frame m0 80 slots 8 st2.data :=
    Frame.call_slots hf1 hsv2 hrsp2 hs2
      (fun p hp i hi ↦ hslot _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hslot _ (by omega) (by omega) _ rfl)
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange t 760 q ∨
        NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    have hqf : ¬ NativeRustcVm.InRange fb 80 q := fun h ↦ hq.2 (hfS q h)
    rw [hs2 q (by
      rintro (h | h | h)
      · exact hqf (inRange_of_off hfnw80 (by decide) h)
      · exact hq.1 h
      · exact hq.2 (hcal2 q h).1)]
    exact hs1 q hqf
  have h3₂ : reg st2.data .rbx = o := (hsv2.1 .rbx rfl).trans hX3
  have h14₂ : reg st2.data .r14 = t := (hsv2.1 .r14 rfl).trans hX14
  -- `b1`: the tag.
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 80) (rest := [(o, 24)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf2.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hom hf2.kept, hon⟩)
    (List.pairwise_pair.mpr (Apart.symm' hoF))
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalar.b0_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl h3₂, trivial⟩ trivial
      trivial trivial) fun st3 hm3 hpc3 => ?_
  simp only [PcOk] at hpc3
  sym_simp_at hpc3
  cases hns2 : nextScalar.run s with
  | none =>
    -- `None`: the tag `0` stored.
    rw [hns2] at hout2
    have h0 : NativeRustcVm.WordAt st2.data.dmem (off fb 16) 0 := hout2
    have ht0 : (frameEnv m0 st2.data 80 [(o, 24)] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec).load 0 16 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (Or.inl rfl) h0
    simp only [ht0] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf2 nofun
      (hpc3.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalar.label_2_at)) hm3 fun st4 hm4 hpc4 => ?_
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b4 run_b5n) hwf2 nofun
      (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalar.b4_next)) hm4 fun st5 hm5 hpc5 => ?_
    obtain ⟨hepi, hw0, hws5⟩ := after_eq run_b5n ▸ ok_none
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf2 hwf2 hm5 hepi
    have ht := wordAt_write hm5 (r := 1) (o := 0) (b := o) (sz := 24) rfl (by decide)
      (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
    rw [off_zero, show UInt64.ofBitVec ((Sym.lit 0).eval (frameEnv m0 st2.data 80 [(o, 24)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec)) = 0 from rfl] at ht
    have hs5 := sameOutside_region hwf2 hm5 (r := 1) rfl hws5
    simp only [PcOk] at hpc5
    refine .done _ ⟨by rw [hpc5]; exact hf2.load_ret hst (by decide), hrsp5, ?_, ?_, ?_, hsv5⟩
    · rw [run_none hns2]; exact ht
    · rw [run_none hns2]; intro x s' h; cases h
    · intro q hq
      simp only [not_or] at hq
      rw [hs5 q hq.1]
      exact hso2 q (by simp only [not_or]; exact hq.2)
  | some p =>
  obtain ⟨x, s1⟩ := p
  rw [hns2] at hout2
  obtain ⟨ht1, hel⟩ := (hout2 : OptEWAt st2.data.dmem (off fb 16) (some x))
  rw [ewAt_iff, off_off, off_off] at hel
  have hts2 : TStateAt st2.data.dmem t a s1 := hnext2 x s1 hns2
  have ht1' : (frameEnv m0 st2.data 80 [(o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec).load 0 16 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (Or.inr rfl) ht1
  simp only [ht1'] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: `call absorb`.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalar.b1_next)) hm3 fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hws4, hx7₄, hx6₄, hx2₄, hx1₄, hx13₄, hx15₄, hx12₄, hx3₄, hx14₄⟩ :=
    after_eq run_b2 ▸ ok_b2
  have hf4 : Frame m0 80 slots 0 st4.data := Frame.of_block hf2 hwf2 hm4 hmid4 slots_le
  have hs4 : NativeRustcVm.SameOutside st2.data.dmem st4.data.dmem
      (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf2 hm4 (r := 0) rfl (by decide) hws4
  have hsp4 : rspOf st4.data = fb := by rw [hf4.sp, off_zero]
  have hc0 : (frameEnv m0 st2.data 80 [(o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec).load 0 24 8 = x.c0.toBitVec :=
    load_ofMachine (o := 24) rfl hel.1
  have hc1 : (frameEnv m0 st2.data 80 [(o, 24)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateReadScalar.b2Offset + b2.length)).toBitVec).load 0 32 8 = x.c1.toBitVec :=
    load_ofMachine (o := 32) rfl hel.2
  have hX7₄ : reg st4.data .rdi = t := (hm4.regs .rdi _ hx7₄).trans h14₂
  have hX6₄ : reg st4.data .rsi = x.c0.toBitVec := (hm4.regs .rsi _ hx6₄).trans hc0
  have hX2₄ : reg st4.data .rdx = x.c1.toBitVec := (hm4.regs .rdx _ hx2₄).trans hc1
  have hX1₄ : reg st4.data .rcx = (1 : UInt64).toBitVec := hm4.regs .rcx _ hx1₄
  have hX13₄ : reg st4.data .r13 = (1 : UInt64).toBitVec := hm4.regs .r13 _ hx13₄
  have hX15₄ : reg st4.data .r15 = x.c0.toBitVec := (hm4.regs .r15 _ hx15₄).trans hc0
  have hX12₄ : reg st4.data .r12 = x.c1.toBitVec := (hm4.regs .r12 _ hx12₄).trans hc1
  have hX3₄ : reg st4.data .rbx = o := (hm4.regs .rbx _ hx3₄).trans (eval_ptr rfl)
  -- `absorb`.
  have hfb8 : ∀ q, NativeRustcVm.InRange fb 8 q → NativeRustcVm.InRange fb 80 q :=
    fun q h ↦ inRange_mono h (by decide)
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange t 760 q ∨
        NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := fun q hq ↦ by
    rw [hs4 q fun h ↦ hq (Or.inr (hfS q (hfb8 q h)))]
    exact hso2 q hq
  have hrcOut : ∀ q, (NativeRustcVm.InRange t 760 q ∨
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 (noWrap_stackBelow hst) h
        (inRange_mono hq (by omega))
  have hts4 : TStateAt st4.data.dmem t a s1 :=
    hts2.frame (hm4.kept hwf2) (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs4
  have hpre4 : AbsorbPre s1.sponge st4.data := by
    unfold AbsorbPre
    rw [hX7₄]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 readScalarStack).toNat ∨
        (stackBelow m0 readScalarStack).toNat + (readScalarStack + 8) ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf4.kept hsp4 (by decide),
      RcAt.callee hrc (rc_keep hso4 hrcOut) hsp4 hn (by decide),
      ⟨fun i hi ↦ hts4.footprint.1.1 i (by simp only [spongeBytes] at hi; show i < 760; omega), ?_,
        apart_callee (n := readScalarStack) (F := 80) ?_ hsp4 hn (by decide), ?_⟩,
      hts4.sponge, ?_⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · refine got_callee hgot (got_keep hgot hst (writes := [(t, tstateBytes)])
        (by simp [t]) (by simpa using hTn) (by simpa [tstateBytes] using hso4))
        hsp4 hn (by decide) ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Apart.sub ((hgot.1 l hl).2.2.2 (t, tstateBytes) (by simp [t]))
          (Nat.le_refl _) (by simp only [spongeBytes, tstateBytes]; omega)
      · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine call_then hpc4 (habs s1.sponge) hpre4 fun st5 hpc5 hrsp5 ⟨hsp5, hs5, hsv5⟩ => ?_
  rw [hX7₄, hX6₄, hX2₄, hX1₄] at hsp5
  rw [hX7₄] at hs5
  have hcal5 : ∀ q, NativeRustcVm.InRange (stackBelow st4.data absorbStack) absorbStack q →
      NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q ∧
        ¬ NativeRustcVm.InRange fb (80 + 8) q :=
    fun q hq ↦ inRange_callee hsp4 h8 hn (by decide) hq
  have hT328 : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t 760 q :=
    fun q h ↦ inRange_mono h (by simp only [spongeBytes]; omega)
  have hf5 : Frame m0 80 slots 8 st5.data := by
    refine Frame.call hf4 hsv5 hrsp5 hs5 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw (hT328 q hq)
    · exact (hcal5 q hq).2
  have hts5 : TStateAt st5.data.dmem t a { s1 with sponge := s1.sponge.absorb x 1 } := by
    refine hts4.with_sponge hsv5.2 (fun q hq ↦ hRS q (hcal5 q hq).1) (fun q hq ↦ hs5 q ?_) hsp5
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hso5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem (fun q ↦
      NativeRustcVm.InRange t 760 q ∨
        NativeRustcVm.InRange (stackBelow m0 readScalarStack) readScalarStack q) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs5 q (by
      rintro (h | h)
      · exact hq.1 (hT328 q h)
      · exact hq.2 (hcal5 q h).1)]
    exact hso4 q (by simp only [not_or]; exact hq)
  -- `b3`, `b5`: the element and the tag stored, the epilogue.
  have hwf5 := frame_wf (m0 := m0) (d := st5.data) (F := 80) (rest := [(o, 24)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf5.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hom hf5.kept, hon⟩)
    (List.pairwise_pair.mpr (Apart.symm' hoF))
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf5 nofun
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateReadScalar.b2_next))
    (match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf5.rsp_eval, known_ptr rfl ((hsv5.1 .rbx rfl).trans hX3₄), trivial⟩ trivial trivial
      trivial) fun st6 hm6 hpc6 => ?_
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b3 run_b5s) hwf5 nofun
    (hpc6.trans (hp.label NativeRustcVmX64.Vm.TStateReadScalar.label_3_at)) hm6 fun st7 hm7 hpc7 => ?_
  obtain ⟨hepi, hw0, hw1, hw2, hws7⟩ := after_eq run_b5s ▸ ok_some
  obtain ⟨hsv7, hrsp7⟩ := Frame.epilogue hf5 hwf5 hm7 hepi
  have hs7 := sameOutside_region hwf5 hm7 (r := 1) rfl hws7
  have h13 : reg st5.data .r13 = (1 : UInt64).toBitVec := (hsv5.1 .r13 rfl).trans hX13₄
  have h15 : reg st5.data .r15 = x.c0.toBitVec := (hsv5.1 .r15 rfl).trans hX15₄
  have h12 : reg st5.data .r12 = x.c1.toBitVec := (hsv5.1 .r12 rfl).trans hX12₄
  have ht := wordAt_write hm7 (r := 1) (o := 0) (b := o) (sz := 24) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
  rw [off_zero, show UInt64.ofBitVec ((Sym.reg .r13).eval
    (frameEnv m0 st5.data 80 [(o, 24)] (fun _ ↦ 0) 0)) = 1 from by
      show UInt64.ofBitVec (reg st5.data .r13) = 1; rw [h13]] at ht
  have hw0' := wordAt_write hm7 (r := 1) (o := 8) (b := o) (sz := 24) rfl (by decide) hw1
  rw [show UInt64.ofBitVec ((Sym.reg .r15).eval
    (frameEnv m0 st5.data 80 [(o, 24)] (fun _ ↦ 0) 0)) = x.c0 from by
      show UInt64.ofBitVec (reg st5.data .r15) = _; rw [h15]] at hw0'
  have hw1' := wordAt_write hm7 (r := 1) (o := 16) (b := o) (sz := 24) rfl (by decide) hw2
  rw [show UInt64.ofBitVec ((Sym.reg .r12).eval
    (frameEnv m0 st5.data 80 [(o, 24)] (fun _ ↦ 0) 0)) = x.c1 from by
      show UInt64.ofBitVec (reg st5.data .r12) = _; rw [h12]] at hw1'
  simp only [PcOk] at hpc7
  refine .done _ ⟨by rw [hpc7]; exact hf5.load_ret hst (by decide), hrsp7, ?_, ?_, ?_, hsv7⟩
  · rw [run_some hns2]
    exact ⟨ht, ewAt_iff.mpr ⟨hw0', by rw [off_off]; exact hw1'⟩⟩
  · rw [run_some hns2]
    intro x' s' h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts5.frame (hm7.kept hwf5) (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq h,
      fun h ↦ not_inRange_of_apart hoA hon hAn hq h⟩) hs7
  · intro q hq
    simp only [not_or] at hq
    rw [hs7 q hq.1]
    exact hso5 q (by simp only [not_or]; exact hq.2)

end

end NativeRustcVmX64.Transcript.ReadScalar
