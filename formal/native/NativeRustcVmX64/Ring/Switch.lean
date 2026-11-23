module

public import NativeRustcVmX64.Ring.Switch.Basic
public import NativeRustcVmX64.Got
public import NativeRustcVmX64.Code.Vm.RingCoefficients.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.RingTarget.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `ring_switch` on x86-64

**`ringSwitch_spec`**: rustc's `ring_switch(t, s, out)`, placed anywhere in the program, given the
contracts of `grind`, `sample_challenges`, `ring_coefficients` and `ring_target`, returns
`ringSwitch`'s `Option<()>` in AL and, on `Some`, the target and the coefficients in the `RingW`
at `out`, the next state in the `TState`. `b0` (the prologue, `call grind(13)`), `b1` (AL's test):
`None`, `b6` (the epilogue); `Some`, `b2` (the challenges zeroed, `call sample_challenges(16)`),
`b3` (`g` copied, `call ring_coefficients(f, g, out.coefficients)`), `b4` (`call
ring_target(s, f, g)`), `b5`, `b6` (the target stored, AL the grind's, the epilogue).
-/

namespace NativeRustcVmX64.Ring.Switch

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RingSwitch NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Ring

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 432 := by decide

/-- The slots' bytes and the return address are at or above offset `392`. -/
theorem slot_bytes : ∀ p ∈ slots, ∀ i < 8, 392 ≤ p.1 + i ∧ p.1 + i < 440 := by
  intro p hp i hi
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega

variable [Host] {k : Nat}

/-- **`ring_switch` meets its contract.** -/
theorem ringSwitch_spec (hp : Placed code k)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrc : Spec (Labels.label NativeRustcVmX64.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost)
    (hrt : Spec (Labels.label NativeRustcVmX64.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost)
    (a : DecArea) (s : TState) (point : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s) (RingSwitchPost a s point) := by
  intro m0 hpre
  have h := P.intro hpre
  have hst := h.st
  set t := reg m0 .rdi with htdef
  set sA := reg m0 .rsi with hsAdef
  set o := reg m0 .rdx with hodef
  set fb := stackBelow m0 432 with hfb
  have hn : 3008 ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfbN : fb.toNat = (rspOf m0).toNat - 432 := stackBelow_toNat (by omega)
  have hSN : (stackBelow m0 ringSwitchStack).toNat = (rspOf m0).toNat - 3008 :=
    stackBelow_toNat hst.1
  have hfnw : NativeRustcVm.NoWrap fb (432 + 8) := frame_noWrap hst (by decide)
  obtain ⟨hom, hon, hoT, hoA, hoS, hoR⟩ := h.out
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, hTA⟩ := h.ts.footprint
  obtain ⟨hTS, hAS, hTR⟩ := h.tok
  have hoF : NativeRustcVm.Apart o 1040 fb (432 + 8) := apart_frame hoS hst.1 (by decide)
  have hpw : [(fb, 432 + 8), (o, 1040)].Pairwise
      fun x y : BitVec 64 × Nat ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2 :=
    List.pairwise_pair.mpr (Apart.symm' hoF)
  have hwfE : ∀ (d : MachineData) (ret : BitVec 64), Kept m0.dmem d.dmem →
      (frameEnv m0 d 432 [(o, 1040)] (fun _ ↦ 0) ret).WF := fun d ret hk ↦
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hk, hfnw⟩
      (fun x hx ↦ by
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps hom hk, hon⟩) hpw
  -- What may change, and what it misses.
  have hframe : ∀ q, NativeRustcVm.InRange fb 432 q → Ch m0 q :=
    fun q hq ↦ .inr (.inr (frame_in hst (by decide) hq))
  have hcallee : ∀ (d : MachineData) n', rspOf d = fb → 432 + n' ≤ ringSwitchStack →
      ∀ q, NativeRustcVm.InRange (stackBelow d n') n' q → Ch m0 q :=
    fun d n' hsp hle q hq ↦ .inr (.inr (callee_in hst hsp hle hq))
  have hChR : ∀ q, Ch m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
    have hrw := h.rc.2.1
    rintro q (hq | hq | hq) hr
    · exact NativeRustcVm.Apart.not_inRange hoR hon hrw hq hr
    · exact NativeRustcVm.Apart.not_inRange hTR hTn hrw hq hr
    · exact NativeRustcVm.Apart.not_inRange (Apart.symm' h.rc.2.2) (noWrap_stackBelow hst) hrw
        (inRange_le hq (by omega)) hr
  have hOS_T : ∀ q, (NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    rintro q (hq | hq)
    · exact ⟨NativeRustcVm.Apart.not_inRange hoT hon hTn hq,
        NativeRustcVm.Apart.not_inRange hoA hon hAn hq⟩
    · have hq' := inRange_le hq (show ringSwitchStack ≤ ringSwitchStack + 8 by omega)
      exact ⟨fun h' ↦ NativeRustcVm.Apart.not_inRange hTS hTn (noWrap_stackBelow hst) h' hq',
        fun h' ↦ NativeRustcVm.Apart.not_inRange hAS hAn (noWrap_stackBelow hst) h' hq'⟩
  have hFT : ∀ q, NativeRustcVm.InRange fb 432 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ hOS_T q (.inr (frame_in hst (by decide) hq))
  have hsl := h.sl
  have hgot := hpre.2.2.2.2.2.2.2.2
  have hgotCall {d : MachineData} {n' : Nat} {areas' : List (BitVec 64 × Nat)}
      (hsame : SameOutside m0.dmem d.dmem (Ch m0)) (hsp : rspOf d = fb)
      (hle : 432 + n' ≤ ringSwitchStack)
      (hcover : ∀ ar ∈ areas', ∃ b ∈ (stackBelow m0 ringSwitchStack, ringSwitchStack + 8) ::
        [(t, tstateBytes), (a.words, 8 * a.len), (o, ringWBytes), (sA, 16 * coeffCount), (rcAddr, 192)],
        b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
      GotAt d n' areas' ["memcpy"] := by
    have hb := hgot.unchanged hst
      (by
        intro ar har
        simp only [List.mem_cons, List.not_mem_nil, or_false] at har
        rcases har with rfl | rfl | rfl | rfl | rfl
        · exact hTn
        · exact hAn
        · exact hon
        · exact hsl.1.2
        · exact h.rc.2.1)
      (fun q hq => hsame q (fun hc => hq (by
        rcases hc with hc | hc | hc
        · exact Or.inr ⟨(o, ringWBytes), by simp [o], hc⟩
        · exact Or.inr ⟨(t, tstateBytes), by simp [t], hc⟩
        · exact Or.inl hc)))
    have hd : (stackBelow d n').toNat = (rspOf m0).toNat - 432 - n' := by
      rw [stackBelow_toNat (by rw [hsp, hfbN]; change 432 + n' ≤ 3008 at hle; omega),
        hsp, hfbN]
    apply NativeRustcVmX64.GotAt.callee hgot hb _ _ hcover
    · rw [hSN, hd]
      change 432 + n' ≤ 3008 at hle
      omega
    · rw [hSN, hd]
      change _ + (n' + 8) ≤ _ + (3008 + 8)
      change 432 + n' ≤ 3008 at hle
      omega
  have hsl_keep : ∀ d : MachineData, SameOutside m0.dmem d.dmem (Ch m0) →
      arr d sA coeffCount = arr m0 sA coeffCount := by
    intro d hs
    unfold arr
    refine congrArg List.toArray (NativeRustcVm.ewsOf_congr fun i hi ↦ hs _ ?_)
    have hw := hsl.1.2
    rintro (hq | hq | hq)
    · exact NativeRustcVm.Apart.not_inRange_add h.slO hw hon hi hq
    · exact NativeRustcVm.Apart.not_inRange_add h.slT hw hTn hi hq
    · exact NativeRustcVm.Apart.not_inRange_add hsl.2 hw (noWrap_stackBelow hst) hi
        (inRange_le hq (by omega))
  have hoNot : ∀ q, NativeRustcVm.InRange o 1040 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q := fun q hq h' ↦
    NativeRustcVm.Apart.not_inRange hoS hon (noWrap_stackBelow hst) hq (inRange_le h' (by omega))
  have not_low : ∀ j, 8 ≤ j → j < 440 → ¬ NativeRustcVm.InRange fb 8 (off fb j) := by
    intro j h1 h2 h'
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega), toNat_off (by omega)] at h'
    omega
  have hfr : ∀ j, j < 440 → NativeRustcVm.InRange fb 440 (off fb j) :=
    fun j hj ↦ inRange_off_self hj (by unfold NativeRustcVm.NoWrap at hfnw; omega)
  have hoFr : ∀ j, j < 440 → ¬ NativeRustcVm.InRange o 1040 (off fb j) := fun j hj h' ↦
    NativeRustcVm.Apart.not_inRange hoF hon hfnw h' (hfr j hj)
  have hstk : ∀ q, NativeRustcVm.InRange fb 432 q →
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q :=
    fun q hq ↦ frame_in hst (by decide) hq
  -- `b0`: the prologue, `call grind(13)`.
  have hwf0 := hwfE m0 (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b0Offset + b0.length)).toBitVec fun _ h ↦ h
  have hm0 : Match (frameEnv m0 m0 432 [(o, 1040)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b0Offset + b0.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  unfold NativeRustcVmX64.Vm.RingSwitch.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.RingSwitch.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hrsi, hrbx, hr12, hr14, hrdi⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 432 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 432) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hs1' : SameOutside m0.dmem st1.data.dmem (Ch m0) := fun q hq ↦ hs1 q fun h' ↦ hq (hframe q h')
  have hsp1 : rspOf st1.data = fb := by rw [hf1.sp, off_zero]
  have e1di : reg st1.data .rdi = t := hm1.regs .rdi _ hrdi
  have e1si : reg st1.data .rsi = BitVec.ofNat 64 13 := hm1.regs .rsi _ hrsi
  have e1bx : reg st1.data .rbx = o := (hm1.regs .rbx _ hrbx).trans (eval_ptr rfl)
  have e1r12 : reg st1.data .r12 = t := hm1.regs .r12 _ hr12
  have e1r14 : reg st1.data .r14 = sA := hm1.regs .r14 _ hr14
  have hts1 : TStateAt st1.data.dmem t a s := h.ts.frame hf1.kept hFT hs1
  have hgb : grindBits st1.data = LeanVM.Parameters.Whir.batchGrindingBits := by
    unfold grindBits
    rw [e1si]
    rfl
  have hpre1 : GrindPre a s st1.data := by
    unfold GrindPre
    rw [e1di, hgb]
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by decide),
      RcAt.callee h.rc (rc_keep hs1' hChR) hsp1 hst.1 (by decide), hts1,
      TStateOk.callee h.tok hsp1 hst.1 (by decide), by decide, ?_⟩
    apply hgotCall hs1' hsp1 (by decide)
    intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl
    · exact ⟨(t, tstateBytes), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  refine call_then hpc1 (hgr a s) hpre1 fun st2 hpc2 hrsp2 hQ2 ↦ ?_
  obtain ⟨hok2, hnext2, hs2, hsv2⟩ := hQ2
  rw [e1di, hgb] at hnext2
  rw [e1di] at hs2
  rw [hgb] at hok2
  have hR2 : ∀ j, j < 432 + 8 → ¬ (NativeRustcVm.InRange t tstateBytes (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st1.data grindStack) grindStack (off fb j)) := by
    rintro j hj (h' | h')
    · exact not_frame hst hTS hTn hj h'
    · exact not_callee hst hsp1 (by decide) hj h'
  have hf2 : Frame m0 432 slots 8 st2.data :=
    Frame.call_slots hf1 hsv2 hrsp2 hs2
      (fun p hp i hi ↦ hR2 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR2 _ (by omega))
  have hs2' : SameOutside m0.dmem st2.data.dmem (Ch m0) := fun q hq ↦
    (hs2 q fun h' ↦ hq (h'.elim (fun h' ↦ .inr (.inl h'))
      (fun h' ↦ hcallee st1.data _ hsp1 (by decide) q h'))).trans (hs1' q hq)
  have e2bx : reg st2.data .rbx = o := (hsv2.1 .rbx rfl).trans e1bx
  -- `b1`: AL's test.
  have hwf2 := hwfE st2.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b2Offset + b2.length)).toBitVec hf2.kept
  have hm2 : Match (frameEnv m0 st2.data 432 [(o, 1040)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b2Offset + b2.length)).toBitVec) gS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl e2bx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b0_next)) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hc3 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st2.data 432 [(o, 1040)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b2Offset + b2.length)).toBitVec) =
      decide ((reg st2.data .rax).toNat % 256 = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    exact al_test _
  simp only [PcOk, hc3] at hpc3
  have hal2 : (reg st2.data .rax).toNat % 256 =
      (okWord ((grind LeanVM.Parameters.Whir.batchGrindingBits).run s).isSome).toNat := hok2
  cases hg : (grind LeanVM.Parameters.Whir.batchGrindingBits).run s with
  | none =>
    -- `None`: the epilogue.
    rw [hg] at hal2
    have hz : (reg st2.data .rax).toNat % 256 = 0 := hal2
    simp (config := { decide := true }) only [hz,
      ↓reduceIte] at hpc3
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6n hwf2 nofun
      (hpc3.trans (hp.label NativeRustcVmX64.Vm.RingSwitch.label_2_at)) hm3 fun st4 hm4 hpc4 ↦ ?_
    obtain ⟨hepi, hmem4, hrax4⟩ := after_eq run_b6n ▸ ok_n
    obtain ⟨hsv4, hrsp4⟩ := Frame.epilogue hf2 hwf2 hm4 hepi
    have hs4 : SameOutside m0.dmem st4.data.dmem (Ch m0) := fun q hq ↦
      (hm4.get?_mem0 hwf2 fun ⟨w, hw, _⟩ ↦ by rw [hmem4] at hw; cases hw).trans (hs2' q hq)
    simp only [PcOk] at hpc4
    refine .done _ ⟨by rw [hpc4]; exact hf2.load_ret hst (by decide), hrsp4, ?_, ?_, hs4, hsv4⟩
    · show boolRet st4.data = _
      rw [ringSwitch_none hg]
      unfold boolRet
      rw [show reg st4.data .rax = reg st2.data .rax from hm4.regs .rax _ hrax4, hz]
      rfl
    · intro x s' hr
      rw [ringSwitch_none hg] at hr
      cases hr
  | some p =>
  obtain ⟨⟨⟩, t1⟩ := p
  rw [hg] at hal2
  have hone : (reg st2.data .rax).toNat % 256 = 1 := hal2
  simp (config := { decide := true }) only [hone,
    ↓reduceIte] at hpc3
  -- `b2`: the challenges zeroed, `call sample_challenges(16)`.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf2 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b1_next)) hm3 fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hws5, h5di, h5si, h5dx, h5bx, h5bp, h5r14, h5r15⟩ := after_eq run_b2 ▸ ok_b2
  have hf5 : Frame m0 432 slots 0 st5.data := Frame.of_block hf2 hwf2 hm5 hmid5 slots_le
  have hsp5 : rspOf st5.data = fb := by rw [hf5.sp, off_zero]
  have hs5 : SameOutside st2.data.dmem st5.data.dmem (NativeRustcVm.InRange fb 264) :=
    sameOutside_low hwf2 hm5 (r := 0) rfl (by decide) hws5
  have hs5' : SameOutside m0.dmem st5.data.dmem (Ch m0) := fun q hq ↦
    (hs5 q fun h' ↦ hq (hframe q (inRange_le h' (by decide)))).trans (hs2' q hq)
  have f5di : reg st5.data .rdi = t := (hm5.regs .rdi _ h5di).trans ((hsv2.1 .r12 rfl).trans e1r12)
  have f5si : reg st5.data .rsi = off fb 8 := (hm5.regs .rsi _ h5si).trans (eval_ptr0 8)
  have f5dx : reg st5.data .rdx = BitVec.ofNat 64 16 := hm5.regs .rdx _ h5dx
  have f5bx : reg st5.data .rbx = o := (hm5.regs .rbx _ h5bx).trans (eval_ptr rfl)
  have f5bp : reg st5.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) := hm5.regs .rbp _ h5bp
  have f5r14 : reg st5.data .r14 = sA :=
    (hm5.regs .r14 _ h5r14).trans ((hsv2.1 .r14 rfl).trans e1r14)
  have f5r15 : reg st5.data .r15 = off fb 8 := (hm5.regs .r15 _ h5r15).trans (eval_ptr0 8)
  have hts5 : TStateAt st5.data.dmem t a t1 :=
    (hnext2 () t1 hg).frame (hm5.kept hwf2) (fun q hq ↦ hFT q (inRange_le hq (by decide))) hs5
  have hpre5 : SampleChallengesPre a t1 st5.data := by
    unfold SampleChallengesPre
    rw [f5di, f5si, f5dx]
    refine ⟨stackOk_callee hst hf5.kept hsp5 (by decide),
      RcAt.callee h.rc (rc_keep hs5' hChR) hsp5 hst.1 (by decide), hts5,
      TStateOk.callee h.tok hsp5 hst.1 (by decide),
      OutOk.frame hst (by decide) hsp5 hf5.kept (by decide) (by decide) h.tok h.rc, ?_⟩
    apply hgotCall hs5' hsp5 (by decide)
    intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl | rfl
    · exact ⟨(t, tstateBytes), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 ringSwitchStack, ringSwitchStack + 8), by simp, ?_, ?_⟩ <;>
        dsimp only [Prod.fst, Prod.snd] <;>
        rw [hSN, toNat_off (by unfold NativeRustcVm.NoWrap at hfnw; omega), hfbN]
      · omega
      · change _ + 16 * 16 ≤ _ + (3008 + 8)
        omega
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  refine call_then hpc5 (hsc a t1) hpre5 fun st6 hpc6 hrsp6 hQ6 ↦ ?_
  obtain ⟨⟨xs, t2, hrun, hxs6, hts6⟩, hs6, hsv6⟩ := hQ6
  rw [f5dx, show (BitVec.ofNat 64 16).toNat = 16 from rfl] at hrun
  rw [f5si] at hxs6
  rw [f5di] at hts6
  rw [f5di, f5si, f5dx, show (BitVec.ofNat 64 16).toNat = 16 from rfl] at hs6
  have hxsz : xs.size = 16 := sample_size hrun
  have hR6 : ∀ j, (j < 8 ∨ 264 ≤ j) → j < 432 + 8 →
      ¬ (NativeRustcVm.InRange (off fb 8) (16 * 16) (off fb j) ∨
        NativeRustcVm.InRange t tstateBytes (off fb j) ∨
        NativeRustcVm.InRange (stackBelow st5.data sampleChallengesStack) sampleChallengesStack
          (off fb j)) := by
    rintro j hj hj' (h' | h' | h')
    · rw [inRange_off_iff (by omega) (by omega)] at h'
      omega
    · exact not_frame hst hTS hTn hj' h'
    · exact not_callee hst hsp5 (by decide) hj' h'
  have hf6 : Frame m0 432 slots 8 st6.data :=
    Frame.call_slots hf5 hsv6 hrsp6 hs6
      (fun p hp i hi ↦ hR6 _ (by have := slot_bytes p hp i hi; omega)
        (by have := slot_bytes p hp i hi; omega)) (fun j hj ↦ hR6 _ (by omega) (by omega))
  have hs6' : SameOutside m0.dmem st6.data.dmem (Ch m0) := fun q hq ↦
    (hs6 q fun h' ↦ hq (by
      rcases h' with h' | h' | h'
      · exact hframe q (inRange_of_off (N := 432) (by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega)
          (by decide) h')
      · exact .inr (.inl h')
      · exact hcallee st5.data _ hsp5 (by decide) q h')).trans (hs5' q hq)
  have e6bx : reg st6.data .rbx = o := (hsv6.1 .rbx rfl).trans f5bx
  have e6r14 : reg st6.data .r14 = sA := (hsv6.1 .r14 rfl).trans f5r14
  have e6r15 : reg st6.data .r15 = off fb 8 := (hsv6.1 .r15 rfl).trans f5r15
  have e6bp : reg st6.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    (hsv6.1 .rbp rfl).trans f5bp
  -- `b3`: `g` copied, `call ring_coefficients`.
  have hwf6 := hwfE st6.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b3Offset + b3.length)).toBitVec hf6.kept
  have hm6 : Match (frameEnv m0 st6.data 432 [(o, 1040)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b3Offset + b3.length)).toBitVec) cS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf6.rsp_eval, known_ptr rfl e6bx, e6r15.trans (eval_ptr0 8).symm, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf6 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b2_next)) hm6 fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hws7, hcopy, h7di, h7si, h7dx, h7bx, h7r12, h7r15, h7r14, h7bp⟩ :=
    after_eq run_b3 ▸ ok_b3
  have hf7 : Frame m0 432 slots 0 st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hsp7 : rspOf st7.data = fb := by rw [hf7.sp, off_zero]
  have hs7 : SameOutside st6.data.dmem st7.data.dmem
      (fun q ↦ Touch fb (432 + 8) (fun j ↦ j < 8 ∨ (264 ≤ j ∧ j < 392)) q) :=
    sameOutside_W hwf6 hm7 (r := 0) rfl fun w hw ↦ by
      obtain ⟨hr, hw'⟩ := hws7 w hw
      refine ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩
  have hT7 : ∀ q, Touch fb (432 + 8) (fun j ↦ j < 8 ∨ (264 ≤ j ∧ j < 392)) q →
      NativeRustcVm.InRange fb 432 q := by
    rintro q ⟨j, hj, hW, rfl⟩
    exact inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega)
  have hT7' : ∀ j, 8 ≤ j → j < 264 →
      ¬ Touch fb (432 + 8) (fun j ↦ j < 8 ∨ (264 ≤ j ∧ j < 392)) (off fb j) := by
    rintro j h1 h2 ⟨j', hj', hW, he⟩
    have := off_inj hfnw (by omega) hj' he.symm
    omega
  have f7di : reg st7.data .rdi = off fb 8 := (hm7.regs .rdi _ h7di).trans (eval_ptr0 8)
  have f7si : reg st7.data .rsi = off fb 264 := (hm7.regs .rsi _ h7si).trans (eval_ptr0 264)
  have f7dx : reg st7.data .rdx = off o 16 := (hm7.regs .rdx _ h7dx).trans rfl
  have f7bx : reg st7.data .rbx = o := (hm7.regs .rbx _ h7bx).trans (eval_ptr rfl)
  have f7r12 : reg st7.data .r12 = off fb 264 := (hm7.regs .r12 _ h7r12).trans (eval_ptr0 264)
  have f7r15 : reg st7.data .r15 = off fb 8 := (hm7.regs .r15 _ h7r15).trans (eval_ptr0 8)
  have f7r14 : reg st7.data .r14 = sA := (hm7.regs .r14 _ h7r14).trans e6r14
  have f7bp : reg st7.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    (hm7.regs .rbp _ h7bp).trans e6bp
  -- `f` and `g` as the frame holds them.
  have hfA : NativeRustcVm.ewsOf st7.data.dmem (off fb 8) 8 = NativeRustcVm.ewsOf st6.data.dmem (off fb 8) 8 :=
    frame_keep hs7 fun j h1 h2 ↦ hT7' j h1 (by omega)
  have hgA : NativeRustcVm.ewsOf st7.data.dmem (off fb 264) 8 =
      NativeRustcVm.ewsOf st6.data.dmem (off fb 8 + BitVec.ofNat 64 128) 8 := by
    rw [off_add]
    refine ewsOf_of_words fun j hj ↦ ?_
    have hw := wordAt_write hm7 (r := 0) (o := 264 + 8 * j) (b := fb) (sz := 432 + 8) rfl
      (by omega) (v := .load 0 (136 + 8 * j) 8) fun i hi ↦ hcopy j hj i hi
    rw [off_add, off_add, NativeRustcVm.wordOf_of_wordAt hw]
    simp only [Sym.eval]
    rw [load_eq_wordOf]
    rfl
  have hfx : arr st7.data (off fb 8) ringWidth = xs.extract 0 8 := by
    unfold arr ringWidth
    rw [hfA, take_of hxsz hxs6]
  have hgx : arr st7.data (off fb 264) ringWidth = xs.extract 8 xs.size := by
    unfold arr ringWidth
    rw [hgA, drop_of hxsz hxs6]
  have hframeOk : ∀ (d : MachineData) (n' ob l : Nat), Kept m0.dmem d.dmem →
      rspOf d = fb → 432 + n' ≤ ringSwitchStack → 8 ≤ ob → ob + l ≤ 432 →
      Readable d (off fb ob) l ∧ OffStack d (off fb ob) l n' := by
    intro d n' ob l hk hsp hn' hob hl
    rw [stack_eq] at hn'
    have hsb := stackBelow_callee (n' := n') hsp (by omega)
    have hsbN := stackBelow_toNat (m := m0) (n := 432 + n') (by omega)
    refine ⟨⟨Mapped.keeps (mapped_off (frame_mapped (F := 432) hst (by decide)) (by omega)) hk, ?_⟩,
      ?_⟩
    · show (off fb ob).toNat + l ≤ 2 ^ 64
      rw [toNat_off (by omega)]
      omega
    · unfold OffStack Apart
      rw [hsb, hsbN, toNat_off (by omega)]
      omega
  have hoOk : ∀ (d : MachineData) (n'' : Nat), Kept m0.dmem d.dmem → rspOf d = fb →
      432 + n'' ≤ ringSwitchStack → ArrOk d (off o 16) coeffCount n'' := fun d n'' hk hsp hn'' ↦
    ⟨⟨Mapped.keeps (mapped_off (o := 16) (k := 1024) hom (by decide)) hk,
      by
        have hon2 : o.toNat + 1040 ≤ 2 ^ 64 := hon
        show (off o 16).toNat + 16 * 64 ≤ 2 ^ 64
        rw [toNat_off (by omega)]
        omega⟩,
      apart_part_callee hoS hon (by decide) (by decide) hsp hst.1 hn''⟩
  have hpre7 : RingCoefficientsPre st7.data := by
    unfold RingCoefficientsPre ArrOk
    rw [f7di, f7si, f7dx]
    exact ⟨stackOk_callee hst hf7.kept hsp7 (by decide),
      hframeOk st7.data _ 8 128 hf7.kept hsp7 (by decide) (by decide) (by decide),
      hframeOk st7.data _ 264 128 hf7.kept hsp7 (by decide) (by decide) (by decide),
      hoOk st7.data _ hf7.kept hsp7 (by decide),
      apart_parts hoF hon hfnw (by decide) (by decide) (by decide) (by decide),
      apart_parts hoF hon hfnw (by decide) (by decide) (by decide) (by decide)⟩
  refine call_then hpc7 hrc hpre7 fun st8 hpc8 hrsp8 ⟨hc8, hs8, hsv8⟩ ↦ ?_
  rw [f7di, f7si, f7dx, hfx, hgx] at hc8
  rw [f7dx] at hs8
  have hR8 : ∀ j, j < 432 + 8 → ¬ (NativeRustcVm.InRange (off o 16) (16 * coeffCount) (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st7.data ringCoefficientsStack) ringCoefficientsStack
        (off fb j)) := by
    rintro j hj (h' | h')
    · exact hoFr j hj (inRange_of_off hon (by decide) h')
    · exact not_callee hst hsp7 (by decide) hj h'
  have hf8 : Frame m0 432 slots 8 st8.data :=
    Frame.call_slots hf7 hsv8 hrsp8 hs8
      (fun p hp i hi ↦ hR8 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR8 _ (by omega))
  have e8bx : reg st8.data .rbx = o := (hsv8.1 .rbx rfl).trans f7bx
  have e8r12 : reg st8.data .r12 = off fb 264 := (hsv8.1 .r12 rfl).trans f7r12
  have e8r15 : reg st8.data .r15 = off fb 8 := (hsv8.1 .r15 rfl).trans f7r15
  have e8r14 : reg st8.data .r14 = sA := (hsv8.1 .r14 rfl).trans f7r14
  have e8bp : reg st8.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    (hsv8.1 .rbp rfl).trans f7bp
  -- `b4`: `call ring_target(s, f, g)`.
  have hwf8 := hwfE st8.data (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b4Offset + b4.length)).toBitVec hf8.kept
  have hm8 : Match (frameEnv m0 st8.data 432 [(o, 1040)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.RingSwitch.b4Offset + b4.length)).toBitVec) tS st8.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf8.rsp_eval, known_ptr rfl e8bx, e8r15.trans (eval_ptr0 8).symm,
        e8r12.trans (eval_ptr0 264).symm, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf8 (fun _ _ ↦ rfl)
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b3_next)) hm8 fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hws9, h9di, h9si, h9dx, h9bx, h9bp⟩ := after_eq run_b4 ▸ ok_b4
  have hf9 : Frame m0 432 slots 0 st9.data := Frame.of_block hf8 hwf8 hm9 hmid9 slots_le
  have hsp9 : rspOf st9.data = fb := by rw [hf9.sp, off_zero]
  have hs9 : SameOutside st8.data.dmem st9.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf8 hm9 (r := 0) rfl (by decide) hws9
  have f9di : reg st9.data .rdi = sA := (hm9.regs .rdi _ h9di).trans e8r14
  have f9si : reg st9.data .rsi = off fb 8 := (hm9.regs .rsi _ h9si).trans (eval_ptr0 8)
  have f9dx : reg st9.data .rdx = off fb 264 := (hm9.regs .rdx _ h9dx).trans (eval_ptr0 264)
  have f9bx : reg st9.data .rbx = o := (hm9.regs .rbx _ h9bx).trans (eval_ptr rfl)
  have f9bp : reg st9.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    (hm9.regs .rbp _ h9bp).trans e8bp
  -- What changed from `st6` on: the `RingW` and the stack.
  have hS7 : SameOutside st6.data.dmem st7.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) :=
    fun q hq ↦ hs7 q fun h' ↦ hq (.inr (hstk q (hT7 q h')))
  have hS8 : SameOutside st7.data.dmem st8.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) :=
    fun q hq ↦ hs8 q fun h' ↦ hq (h'.elim (fun h' ↦ .inl (inRange_of_off hon (by decide) h'))
      (fun h' ↦ .inr (callee_in hst hsp7 (by decide) h')))
  have hS9 : SameOutside st8.data.dmem st9.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) :=
    fun q hq ↦ hs9 q fun h' ↦ hq (.inr (hstk q (inRange_le h' (by decide))))
  have hS : ∀ q, (NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) → Ch m0 q :=
    fun q h' ↦ h'.elim .inl (fun h' ↦ .inr (.inr h'))
  have hs9' : SameOutside m0.dmem st9.data.dmem (Ch m0) := fun q hq ↦ by
    rw [hS9 q fun h' ↦ hq (hS q h'), hS8 q fun h' ↦ hq (hS q h'), hS7 q fun h' ↦ hq (hS q h')]
    exact hs6' q hq
  have hk79 : ∀ ob, 8 ≤ ob → ob + 128 ≤ 432 →
      arr st9.data (off fb ob) ringWidth = arr st7.data (off fb ob) ringWidth := by
    intro ob h1 h2
    unfold arr ringWidth
    exact congrArg List.toArray (frame_keep (SameOutside.trans hs8 hs9) fun j hj1 hj2 h' ↦
      h'.elim (fun h' ↦ hR8 j (by omega) h') (fun h' ↦ not_low j (by omega) (by omega) h'))
  have hgotBytes := hgot.unchanged hst
    (by
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl | rfl
      · exact hTn
      · exact hAn
      · exact hon
      · exact hsl.1.2
      · exact h.rc.2.1)
    (fun q hq => hs9' q (fun hc => hq (by
      rcases hc with hc | hc | hc
      · exact Or.inr ⟨(o, ringWBytes), by simp [o], hc⟩
      · exact Or.inr ⟨(t, tstateBytes), by simp [t], hc⟩
      · exact Or.inl hc)))
  have hgot9 : GotAt st9.data ringTargetStack
      [(sA, 16 * coeffCount), (off fb 8, 16 * ringWidth),
        (off fb 264, 16 * ringWidth)] ["memcpy"] := by
    have hs9N : (stackBelow st9.data ringTargetStack).toNat =
        (rspOf m0).toNat - 3008 := by
      rw [stackBelow_toNat (by
        rw [hsp9, hfbN]
        change 2576 ≤ (rspOf m0).toNat - 432
        have hN : 3008 ≤ (rspOf m0).toNat := hst.1
        omega), hsp9, hfbN]
      change (rspOf m0).toNat - 432 - 2576 = _
      omega
    apply NativeRustcVmX64.GotAt.callee hgot hgotBytes
    · rw [hSN, hs9N]
    · rw [hSN, hs9N]
      change _ + (2576 + 8) ≤ _ + (3008 + 8)
      omega
    · intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact ⟨(sA, 16 * coeffCount), by simp [sA], le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 ringSwitchStack, ringSwitchStack + 8),
          List.mem_cons_self, ?_, ?_⟩ <;>
          dsimp only [Prod.fst, Prod.snd] <;>
          rw [hSN, toNat_off (by unfold NativeRustcVm.NoWrap at hfnw; omega), hfbN]
        · omega
        · change _ + 16 * 8 ≤ _ + (3008 + 8)
          omega
      · refine ⟨(stackBelow m0 ringSwitchStack, ringSwitchStack + 8),
          List.mem_cons_self, ?_, ?_⟩ <;>
          dsimp only [Prod.fst, Prod.snd] <;>
          rw [hSN, toNat_off (by unfold NativeRustcVm.NoWrap at hfnw; omega), hfbN]
        · omega
        · change _ + 16 * 8 ≤ _ + (3008 + 8)
          omega
  have hpre9 : RingTargetPre st9.data := by
    unfold RingTargetPre ArrOk
    rw [f9di, f9si, f9dx]
    exact ⟨stackOk_callee hst hf9.kept hsp9 (by decide),
      ⟨⟨Mapped.keeps hsl.1.1 hf9.kept, hsl.1.2⟩, apart_callee hsl.2 hsp9 hst.1 (by decide)⟩,
      hframeOk st9.data _ 8 128 hf9.kept hsp9 (by decide) (by decide) (by decide),
      hframeOk st9.data _ 264 128 hf9.kept hsp9 (by decide) (by decide) (by decide), hgot9⟩
  refine call_then hpc9 hrt hpre9 fun st10 hpc10 hrsp10 ⟨hv10, hs10, hsv10⟩ ↦ ?_
  rw [f9di, f9si, f9dx, hk79 8 (by decide) (by decide), hk79 264 (by decide) (by decide), hfx, hgx,
    hsl_keep st9.data hs9'] at hv10
  have hR10 : ∀ j, j < 432 + 8 → ¬ (NativeRustcVm.InRange 0 0 (off fb j) ∨
      NativeRustcVm.InRange (stackBelow st9.data ringTargetStack) ringTargetStack (off fb j)) := by
    rintro j hj (h' | h')
    · unfold NativeRustcVm.InRange at h'; omega
    · exact not_callee hst hsp9 (by decide) hj h'
  have hf10 : Frame m0 432 slots 8 st10.data :=
    Frame.call_slots hf9 hsv10 hrsp10 hs10
      (fun p hp i hi ↦ hR10 _ (by have := slots_le p hp; omega)) (fun j hj ↦ hR10 _ (by omega))
  have hS10 : SameOutside st9.data.dmem st10.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) :=
    fun q hq ↦ hs10 q fun h' ↦ hq (h'.elim (fun h' ↦ by unfold NativeRustcX64.InRange at h'; omega)
      (fun h' ↦ .inr (callee_in hst hsp9 (by decide) h')))
  have e10bx : reg st10.data .rbx = o := (hsv10.1 .rbx rfl).trans f9bx
  have e10bp : reg st10.data .rbp = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    (hsv10.1 .rbp rfl).trans f9bp
  -- `b5`, `b6`: the target stored, AL the grind's, the epilogue.
  have hwf10 := hwfE st10.data 0 hf10.kept
  have hm10 : Match (frameEnv m0 st10.data 432 [(o, 1040)] (fun _ ↦ 0) 0) gS st10.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf10.rsp_eval, known_ptr rfl e10bx, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf10 nofun
    (hpc10.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b4_next)) hm10 fun st11 hm11 hpc11 ↦ ?_
  simp only [PcOk] at hpc11
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b5 run_b6s) hwf10 nofun
    (hpc11.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.RingSwitch.b5_next)) hm11 fun st12 hm12 hpc12 ↦ ?_
  obtain ⟨hepi, hw0, hw1, hws12, hrax12⟩ := after_eq run_b6s ▸ ok_s
  obtain ⟨hsv12, hrsp12⟩ := Frame.epilogue hf10 hwf10 hm12 hepi
  have hs12 : SameOutside st10.data.dmem st12.data.dmem (NativeRustcVm.InRange o 16) :=
    sameOutside_low hwf10 hm12 (r := 1) rfl (by decide) fun w hw ↦
      ⟨(hws12 w hw).1, (hws12 w hw).2.2⟩
  have hS12 : SameOutside st10.data.dmem st12.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) :=
    fun q hq ↦ hs12 q fun h' ↦ hq (.inl (inRange_le h' (by decide)))
  have hsAll : SameOutside st6.data.dmem st12.data.dmem (fun q ↦ NativeRustcVm.InRange o 1040 q ∨
      NativeRustcVm.InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q) := fun q hq ↦ by
    rw [hS12 q hq, hS10 q hq, hS9 q hq, hS8 q hq, hS7 q hq]
  have hk612 : Kept st6.data.dmem st12.data.dmem :=
    kept_trans (hm7.kept hwf6) (kept_trans hsv8.2 (kept_trans (hm9.kept hwf8)
      (kept_trans hsv10.2 (hm12.kept hwf10))))
  have ht0 := wordAt_write hm12 (r := 1) (o := 0) rfl (by decide)
    (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
  have ht1 := wordAt_write hm12 (r := 1) (o := 8) rfl (by decide) hw1
  rw [off_zero] at ht0
  simp only [Sym.eval, Env.ofMachine_regs] at ht0 ht1
  have hr := ringSwitch_some (point := point) (s := arr m0 sA coeffCount) hg hrun
  simp only [PcOk] at hpc12
  refine .done _ ⟨by rw [hpc12]; exact hf10.load_ret hst (by decide), hrsp12, ?_, ?_, ?_, hsv12⟩
  · show boolRet st12.data = _
    rw [hr]
    unfold boolRet
    rw [show reg st12.data .rax = _ from hm12.regs .rax _ hrax12]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [show st10.data.regs.get64 .rbp = _ from e10bp, boolRet_trunc, hone]
    rfl
  · intro x s' hx
    rw [hr] at hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hx)
    refine ⟨⟨ewAt_iff.mpr ⟨?_, ?_⟩, ?_, ?_⟩, hts6.frame hk612 hOS_T hsAll⟩
    · rw [← hv10]; exact ht0
    · rw [← hv10]; exact ht1
    · rw [← hfx, ← hgx]
      unfold arr
      rw [ringCoefficients_size]
      simp [ringWidth, coeffCount]
    · have hCsz : (ringCoefficients (xs.extract 0 8) (xs.extract 8 xs.size)).size = 64 := by
        rw [← hfx, ← hgx]
        unfold arr
        rw [ringCoefficients_size]
        simp [ringWidth]
      refine NativeRustcVm.BytesAt.of_sameOutside hc8
        (SameOutside.trans (SameOutside.trans hs9 hs10) hs12) fun i hi h' ↦ ?_
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hCsz] at hi
      rw [off_add] at h'
      have hon' : o.toNat + 1040 ≤ 2 ^ 64 := hon
      have hin : NativeRustcVm.InRange o 1040 (off o (16 + i)) :=
        inRange_off_self (by omega) (by omega)
      rcases h' with (h' | h' | h') | h'
      · exact hoNot _ hin (hstk _ (inRange_le h' (by decide)))
      · unfold NativeRustcX64.InRange at h'; omega
      · exact hoNot _ hin (callee_in hst hsp9 (by decide) h')
      · rw [inRange_iff' (show NativeRustcVm.NoWrap o 16 by unfold NativeRustcVm.NoWrap; omega),
          toNat_off (b := o) (j := 16 + i) (by omega)] at h'
        omega
  · intro q hq
    rw [hS12 q fun h' ↦ hq (hS q h'), hS10 q fun h' ↦ hq (hS q h')]
    exact hs9' q hq

end

end NativeRustcVmX64.Ring.Switch
