module

public import NativeRustcVmArm.Code.Vm.ReadOod.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Layout.ReadOod.Exec
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVmArm.Bus.GkrModel
public import NativeRustcVm.Transcript.Update
public import NativeRustcVmArm.Layout.Common

/-!
# `read_ood`

`b0` saves X30, X21 to X19 and grinds `15` bits; `b1` returns `0` (`b6`) unless the grind passed
(`stack_log ≤ 30`); `b2` stores `stack_log` as the output's length and samples the challenges into
its buffer; `b3` reads a scalar into the frame; `b4` tests its tag (`b6` on `None`); `b5` stores the
value at `488` and returns `1`.
-/

namespace NativeRustcVmArm.Layout.ReadOod

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadOod
open NativeRustcVmArm.Transcript NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Layout

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem stack_eq : readOodStack = 608 := rfl

/-- `readOod` step by step. -/
theorem run_eq (n : Nat) (s : TState) :
    (readOod n).run s = ((grind 15).run s).bind fun p ↦
      ((sampleChallenges n).run p.2).bind fun q ↦
        (readScalar.run q.2).bind fun r ↦ some (⟨.eq q.1, r.1⟩, r.2) := by
  simp only [readOod, StateT.run_bind, Option.bind_eq_bind]
  rfl

/-- What `read_ood` may change: the output, the `TState`, its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange m0.regs.X2.toBitVec eqClaimBytes q ∨
    NativeRustcVm.InRange m0.regs.X0.toBitVec tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 readOodStack) readOodStack q

variable [Host] {k : Nat}

/-- `b6`: `0`, the epilogue. -/
theorem finish_fail (hp : Placed code k) {m0 d : MachineData}
    {rest : List (BitVec 64 × Nat)} {S S6 : SState} (hrun : exec b6 S = some (S6, .ret))
    (hok : EpiOk 64 slots S6 = true ∧ S6.mem = [] ∧ S6.reg .X0 = some (.lit 0))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadOod.b6Offset)) (hf : Frame m0 64 slots d)
    (hwf : (frameEnv m0 d 64 rest).WF) (hm : Match (frameEnv m0 d 64 rest) S st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 0 ∧
      st'.data.dmem = d.dmem ∧ Saved m0 st'.data) st := by
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) hrun hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hmem, hx0⟩ := hok
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30],
    UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0), hm1.dmem_eq hwf hmem, hsv⟩

/-- **`read_ood`'s contract.** -/
theorem readOod_spec (hp : Placed code k)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hlog, hout⟩
  set t := m0.regs.X0.toBitVec with htdef
  set o := m0.regs.X2.toBitVec with hodef
  set L := m0.regs.X1.toNat with hLdef
  set fb := frameBase m0 64 with hfb
  have hL : L ≤ 30 := hlog
  have hn : readOodStack ≤ m0.regs.SP.toNat := hst.2.1
  rw [stack_eq] at hn
  have hlt := m0.regs.SP.toNat_lt
  have hfnw : fb.toNat + 64 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 64) (by omega)
  have hfbN : fb.toNat = m0.regs.SP.toNat - 64 := frameBase_toNat (n := 608) hn (by decide)
  have hsbN : (stackBelow m0 608).toNat = m0.regs.SP.toNat - 608 := toNat_stackBelow hn
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 608) 608 := by
    unfold NativeRustcVm.NoWrap; omega
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  obtain ⟨hOm, hOn, hOT, hOA, hOS, hOR⟩ := hout
  rw [show eqClaimBytes = 504 from rfl] at hOm hOn hOT hOA hOS hOR
  have hON : o.toNat + 504 ≤ 2 ^ 64 := hOn
  have hTF : NativeRustcVm.Apart t 760 fb 64 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 64 := apart_frame htok.2.1 hn (by decide)
  have hOF : NativeRustcVm.Apart o 504 fb 64 := apart_frame hOS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb 64 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hRO : ∀ q, NativeRustcVm.InRange o 504 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hOT hOn hTn hq h,
      fun h ↦ not_inRange_of_apart hOA hOn hAn hq h⟩
  have hrcOut : ∀ q, Out m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart hOR hOn hrc.2.1 hq h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · rw [stack_eq] at hq; exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hframeOut : ∀ q, NativeRustcVm.InRange fb 64 q → Out m0 q := fun q hq ↦
    .inr (.inr (by rw [stack_eq]; exact inRange_frame_stack hn (by decide) hq))
  have hcalOut : ∀ {d : MachineData} {n' : Nat}, d.regs.SP.toBitVec = fb → n' ≤ 608 - 64 →
      ∀ q, NativeRustcVm.InRange (stackBelow d n') n' q →
        Out m0 q ∧ ¬ NativeRustcVm.InRange fb 64 q := fun hsp hn' q hq ↦ by
    obtain ⟨h1, h2⟩ := inRange_callee hsp hn (by decide) hn' hq
    exact ⟨.inr (.inr (by rw [stack_eq]; exact h1)), h2⟩
  have hfr : ∀ {d : MachineData}, Frame m0 64 slots d → (frameEnv m0 d 64 []).WF := fun hf ↦
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hfrO : ∀ {d : MachineData}, Frame m0 64 slots d → (frameEnv m0 d 64 [(o, 504)]).WF :=
    fun hf ↦ Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst (by decide)) hf.kept, hfnw⟩,
      ⟨Mapped.keeps hOm hf.kept, hOn⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hOF))
  have hsp' : ∀ {d : MachineData}, Frame m0 64 slots d →
      d.regs.SP.toNat = m0.regs.SP.toNat - 64 := fun hf ↦ by
    rw [← UInt64.toNat_toBitVec, hf.sp, hfbN]
  -- `b0`: the prologue, `bl grind`.
  have hm0 : Match (frameEnv m0 m0 64 []) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      frameBase_add.symm trivial trivial trivial trivial
  unfold NativeRustcVmArm.Vm.ReadOod.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.ReadOod.entryOffset) NativeRustcVmArm.Vm.ReadOod.entry_at]
  have hwf0 : (frameEnv m0 m0 64 []).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 64) hst (by decide), hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx0, hx1, hx19, hx20, hx21⟩ := Transcript.after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 64 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 64) :=
    sameOutside_region hwf0 hm1 rfl fun w hw ↦ ⟨(hws1 w hw).1, Nat.zero_le _, (hws1 w hw).2.2⟩
  have hso1 : SameOutside m0.dmem st1.data.dmem (Out m0) :=
    SameOutside.mono hs1 fun q hq ↦ hframeOut q hq
  have hX19 : st1.data.regs.X19 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX20 : st1.data.regs.X20 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ hx20)
  have hX21 : st1.data.regs.X21 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ hx21)
  have hX0₁ : st1.data.regs.X0.toBitVec = t := hm1.regs .X0 _ hx0
  have hX1₁ : st1.data.regs.X1 = 15 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ hx1)
  -- `grind`.
  have hpg : GrindPre a s st1.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ st1.data.regs.X0.toBitVec a s ∧
      TStateOk _ st1.data.regs.X0.toBitVec a _ ∧ _
    rw [hX0₁]
    refine ⟨stackOk_callee hst hf1.kept hf1.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso1 hrcOut) hn (by decide) (hsp' hf1) (by decide),
      hts.frame hf1.kept hRF hs1, TStateOk.callee htok hf1.sp hn (by decide) (by decide), ?_⟩
    show st1.data.regs.X1.toNat % 2 ^ 32 < 64
    rw [hX1₁]; decide
  have hgb : grindBits st1.data = 15 := by
    show st1.data.regs.X1.toNat % 2 ^ 32 = 15; rw [hX1₁]; rfl
  refine call_then hpc1 (hgr a s) hpg fun st2 hpc2 ⟨hok2, hnext2, hs2, hsv2⟩ => ?_
  rw [hgb] at hok2 hnext2
  rw [hX0₁] at hnext2 hs2
  have hf2 : Frame m0 64 slots st2.data := by
    refine Frame.call hf1 hsv2 hs2 (fun q hq h ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw hq h
    · exact (hcalOut hf1.sp (by decide) q hq).2 h
  have hso2 : SameOutside m0.dmem st2.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs2 q fun h ↦ h.elim (fun h' ↦ hq (.inr (.inl h'))) fun h' ↦
      hq (hcalOut hf1.sp (by decide) q h').1]
    exact hso1 q hq
  have h19₂ : st2.data.regs.X19 = m0.regs.X2 := (hsv2.1 .X19 rfl).trans hX19
  have h20₂ : st2.data.regs.X20 = m0.regs.X0 := (hsv2.1 .X20 rfl).trans hX20
  have h21₂ : st2.data.regs.X21 = m0.regs.X1 := (hsv2.1 .X21 rfl).trans hX21
  -- `b1`: `stack_log < 31` and the grind's result.
  have hm2 : Match (frameEnv m0 st2.data 64 [(o, 504)]) retS st2.data :=
    match_ofMachine (m := st2.data) (regions := [(fb, 64), (o, 504)])
      (sregions := [(64, true), (504, false)])
      ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st2.data.regs.X19.toBitVec = _; rw [h19₂]), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 (hfrO hf2)
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.ReadOod.b0Offset + NativeRustcVmArm.Vm.ReadOod.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.ReadOod.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadOod.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3⟩ := Transcript.after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 64 slots st3.data := Frame.of_block hf2 (hfrO hf2) hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hfrO hf2) hmem3
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have h21v : (st2.data.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 L := by
    show st2.data.regs.X21.toBitVec = _
    rw [h21₂]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt m0.regs.X1.toNat_lt]; rfl
  have h0v : (st2.data.regs.getXReg .X0).toBitVec = (okWord ((grind 15).run s).isSome).toBitVec := by
    show st2.data.regs.X0.toBitVec = _; rw [hok2]
  have hlt : (BitVec.ofNat 64 L).ult (BitVec.ofNat 64 31) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]; omega
  simp only [Env.ofMachine_regs, h21v, h0v, hlt] at hpc3
  cases hr1 : (grind 15).run s with
  | none =>
    simp (config := { decide := true }) only [hr1, Option.isSome_none, okWord,
      Bool.false_eq_true, ↓reduceIte] at hpc3
    have hnone : (readOod L).run s = none := by rw [run_eq, hr1]; rfl
    refine Eventually.mono (finish_fail hp (Transcript.exec_after run_b1 run_b6a)
      (Transcript.after_eq run_b6a ▸
      ok_b6a) (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.ReadOod.b6Offset) NativeRustcVmArm.Vm.ReadOod.label_3_at)) hf2 (hfrO hf2) hm3)
      fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv'⟩
    · rw [hnone, hx0']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso2 q hq
  | some p =>
  obtain ⟨u1, s1⟩ := p
  simp (config := { decide := true }) only [hr1, Option.isSome_some, okWord, ↓reduceIte] at hpc3
  have hts1 : TStateAt st2.data.dmem t a s1 := hnext2 u1 s1 hr1
  -- `b2`: the length, `bl sample_challenges`.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (Transcript.exec_after run_b1 run_b2)
    (hfrO hf2)
    (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadOod.b1_next])) hm3
    fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hx0₄, hx1₄, hx2₄, hw4, hws4⟩ :=
    Transcript.after_eq (Transcript.exec_after run_b1 run_b2) ▸ ok_b2
  have hf4 : Frame m0 64 slots st4.data := Frame.of_block hf2 (hfrO hf2) hm4 hmid4 slots_le
  have hs4 : SameOutside st2.data.dmem st4.data.dmem (NativeRustcVm.InRange o 504) :=
    sameOutside_region (hfrO hf2) hm4 (r := 1) rfl fun w hw ↦ by
      obtain ⟨h1, h2, h3⟩ := hws4 w hw; exact ⟨h1, by omega, by omega⟩
  have hso4 : SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs4 q fun h ↦ hq (.inl h)]; exact hso2 q hq
  have hlen4 : NativeRustcVm.WordAt st4.data.dmem (off o 0) m0.regs.X1 := by
    have := wordAt_write hm4 (r := 1) (o := 0) rfl (by decide) hw4
    rw [show UInt64.ofBitVec ((Sym.reg .X21).eval (frameEnv m0 st2.data 64 [(o, 504)])) =
      m0.regs.X1 from h21₂] at this
    exact this
  have hX0₄ : st4.data.regs.X0.toBitVec = t := by
    show (st4.data.regs.getXReg .X0).toBitVec = _; rw [hm4.regs .X0 _ hx0₄]
    show st2.data.regs.X20.toBitVec = _; rw [h20₂]
  have hX1₄ : st4.data.regs.X1.toBitVec = off o 8 := by
    show (st4.data.regs.getXReg .X1).toBitVec = _; rw [hm4.regs .X1 _ hx1₄]; rfl
  have hX2₄ : st4.data.regs.X2.toNat = L := by
    show (st4.data.regs.getXReg .X2).toBitVec.toNat = _; rw [hm4.regs .X2 _ hx2₄]
    show st2.data.regs.X21.toNat = _; rw [h21₂]
  have hts4 : TStateAt st4.data.dmem t a s1 := hts1.frame (hm4.kept (hfrO hf2)) hRO hs4
  have hoff8 : (off o 8).toNat = o.toNat + 8 := toNat_off (by omega)
  have hpsc : SampleChallengesPre a s1 st4.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ st4.data.regs.X0.toBitVec a s1 ∧
      TStateOk _ st4.data.regs.X0.toBitVec a _ ∧
      OutOk _ st4.data.regs.X0.toBitVec a st4.data.regs.X1.toBitVec (16 * st4.data.regs.X2.toNat) _
    rw [hX0₄, hX1₄, hX2₄]
    have hOS4 := apart_callee hOS hf4.sp hn (by decide) (n' := sampleChallengesStack) (by decide)
    refine ⟨stackOk_callee hst hf4.kept hf4.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso4 hrcOut) hn (by decide) (hsp' hf4) (by decide), hts4,
      TStateOk.callee htok hf4.sp hn (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [off, NativeRustcVm.addr_add_add]
      exact hf4.kept _ (hOm _ (by omega))
    · show (off o 8).toNat + _ ≤ _; rw [hoff8]; omega
    · exact NativeRustcVm.Apart.mono hOT (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOA (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOS4 (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOR (by omega) (by omega) le_rfl le_rfl
  refine call_then hpc4 (hsc a s1) hpsc fun st5 hpc5 ⟨⟨xs, s2, hr2, hxs, hts5⟩, hs5, hsv5⟩ => ?_
  rw [hX0₄, hX1₄, hX2₄] at hs5
  rw [hX0₄] at hts5
  rw [hX1₄] at hxs
  rw [hX2₄] at hr2
  have hxsz : xs.size = L := Bus.Gkr.sampleChallenges_size hr2
  have hin8 : ∀ q, NativeRustcVm.InRange (off o 8) (16 * L) q → NativeRustcVm.InRange o 504 q :=
    fun q h ↦ inRange_of_off hOn (by omega) h
  have hf5 : Frame m0 64 slots st5.data := by
    refine Frame.call hf4 hsv5 hs5 (fun q hq h ↦ ?_) hfnw slots_le
    rcases hq with hq | hq | hq
    · exact not_inRange_of_apart hOF hOn hfnw (hin8 q hq) h
    · exact not_inRange_of_apart hTF hTn hfnw hq h
    · exact (hcalOut hf4.sp (by decide) q hq).2 h
  have hso5 : SameOutside m0.dmem st5.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs5 q fun h ↦ h.elim (fun h' ↦ hq (.inl (hin8 q h'))) fun h' ↦ h'.elim
      (fun h'' ↦ hq (.inr (.inl h''))) fun h'' ↦ hq (hcalOut hf4.sp (by decide) q h'').1]
    exact hso4 q hq
  -- The length word survives `sample_challenges`.
  have hlen5 : NativeRustcVm.WordAt st5.data.dmem (off o 0) m0.regs.X1 := by
    refine bytesAt_congr hlen4 fun i hi ↦ hs5 _ ?_
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    have hq : NativeRustcVm.InRange o 504 (off o 0 + BitVec.ofNat 64 i) := by
      rw [off_zero]; exact inRange_off_self (by omega) (by omega)
    rintro (h | h | h)
    · have hA8 : NativeRustcVm.Apart o 8 (off o 8) (16 * L) := by
        unfold NativeRustcVm.Apart; rw [hoff8]; omega
      rw [off_zero] at hq h
      exact not_inRange_of_apart hA8 (by unfold NativeRustcVm.NoWrap; omega)
        (by unfold NativeRustcVm.NoWrap; rw [hoff8]; omega) (inRange_off_self hi8 (by omega)) h
    · exact not_inRange_of_apart hOT hOn hTn hq h
    · exact not_inRange_of_apart hOS hOn hsnw hq
        (inRange_callee hf4.sp hn (by decide) (n' := sampleChallengesStack) (by decide) h).1
  -- Registers kept: X19 the output, X20 the `TState`.
  have h19₄ : st4.data.regs.X19 = m0.regs.X2 :=
    UInt64.toBitVec_inj.mp ((hm4.regs .X19 _ rfl).trans (eval_ptr rfl))
  have h20₄ : st4.data.regs.X20 = m0.regs.X0 :=
    (UInt64.toBitVec_inj.mp (hm4.regs .X20 _ rfl)).trans h20₂
  have h19₅ : st5.data.regs.X19 = m0.regs.X2 := (hsv5.1 .X19 rfl).trans h19₄
  have h20₅ : st5.data.regs.X20 = m0.regs.X0 := (hsv5.1 .X20 rfl).trans h20₄
  -- Bytes of the output kept by a change elsewhere.
  have hkeepO : ∀ {d d' : Mem 64} {R : BitVec 64 → Prop}, SameOutside d d' R →
      (∀ q, R q → ¬ NativeRustcVm.InRange o 504 q) →
      ∀ q, NativeRustcVm.InRange o 504 q → d'.get? q = d.get? q :=
    fun hs hR q hq ↦ hs q fun h ↦ hR q h hq
  have hxsz' : xs.toList.length = L := by simp [hxsz]
  have hewsLen : (xs.toList.flatMap NativeRustcVm.ewBytes).length = 16 * L := by
    rw [NativeRustcVm.length_ewsBytes, hxsz']
  have hews5 : NativeRustcVm.EWsAt st5.data.dmem (off o 8) xs.toList := hxs
  -- `b3`: `bl read_scalar` into the frame.
  have hm5 : Match (frameEnv m0 st5.data 64 []) callS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf5.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (hfr hf5)
    (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadOod.b2_next])) hm5 fun st6 hm6 hpc6 => ?_
  obtain ⟨hmid6, hmem6, hx0₆, hx1₆⟩ := Transcript.after_eq run_b3 ▸ ok_b3
  have hf6 : Frame m0 64 slots st6.data := Frame.of_block hf5 (hfr hf5) hm6 hmid6 slots_le
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq (hfr hf5) hmem6
  have hso6 : SameOutside m0.dmem st6.data.dmem (Out m0) := by rw [hd6]; exact hso5
  have hX0₆ : st6.data.regs.X0.toBitVec = off fb 8 := by
    show (st6.data.regs.getXReg .X0).toBitVec = _; rw [hm6.regs .X0 _ hx0₆]; rfl
  have hX1₆ : st6.data.regs.X1.toBitVec = t := by
    show (st6.data.regs.getXReg .X1).toBitVec = _; rw [hm6.regs .X1 _ hx1₆]
    show st5.data.regs.X20.toBitVec = _; rw [h20₅]
  have h19₆ : st6.data.regs.X19 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm6.regs .X19 _ rfl)).trans h19₅
  have hprs : ReadScalarPre a s2 st6.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ st6.data.regs.X1.toBitVec a s2 ∧
      TStateOk _ st6.data.regs.X1.toBitVec a _ ∧
      OutOk _ st6.data.regs.X1.toBitVec a st6.data.regs.X0.toBitVec 24 _
    rw [hX0₆, hX1₆]
    exact ⟨stackOk_callee hst hf6.kept hf6.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso6 hrcOut) hn (by decide) (hsp' hf6) (by decide),
      by rw [hd6]; exact hts5, TStateOk.callee htok hf6.sp hn (by decide) (by decide),
      OutOk.frame hst (by decide) (by decide) hf6.sp hf6.kept (by decide) htok hrc⟩
  refine call_then hpc6 (hrs a s2) hprs fun st7 hpc7 ⟨hopt, hnext7, hs7, hsv7⟩ => ?_
  rw [hX0₆] at hopt hs7
  rw [hX1₆] at hnext7 hs7
  have hslot : ∀ p ∈ slots, ∀ i < 8, NativeRustcVm.InRange fb 64 (off fb (p.1 + i)) :=
    fun p hp i hi ↦ inRange_off_self (by have := slots_le p hp; omega) (by omega)
  have hf7 : Frame m0 64 slots st7.data := by
    refine Frame.call_slots hf6 hsv7 hs7 fun p hp i hi h ↦ ?_
    rcases h with h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p hp i hi h
    · exact not_inRange_of_apart hTF hTn hfnw h (hslot p hp i hi)
    · exact (hcalOut hf6.sp (by decide) _ h).2 (hslot p hp i hi)
  have hR7 : ∀ q, (NativeRustcVm.InRange (off fb 8) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st6.data readScalarStack) readScalarStack q) →
      Out m0 q ∧ ¬ NativeRustcVm.InRange o 504 q := by
    rintro q (h | h | h)
    · have hf := inRange_of_off hfnw (by decide) h
      exact ⟨hframeOut q hf, fun ho ↦ not_inRange_of_apart hOF hOn hfnw ho hf⟩
    · exact ⟨.inr (.inl h), fun ho ↦ not_inRange_of_apart hOT hOn hTn ho h⟩
    · obtain ⟨h1, -⟩ := inRange_callee hf6.sp hn (by decide) (n' := readScalarStack) (by decide) h
      exact ⟨.inr (.inr (by rw [stack_eq]; exact h1)),
        fun ho ↦ not_inRange_of_apart hOS hOn hsnw ho h1⟩
  have hso7 : SameOutside m0.dmem st7.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs7 q fun h ↦ hq (hR7 q h).1]; exact hso6 q hq
  have hk7 := hkeepO hs7 fun q h ↦ (hR7 q h).2
  have hlen7 : NativeRustcVm.WordAt st7.data.dmem o m0.regs.X1 := by
    rw [off_zero] at hlen5
    refine bytesAt_congr (hd6 ▸ hlen5) fun i hi ↦ hk7 _ (inRange_off_self (b := o) (j := i)
      (by simp [NativeRustcVm.length_wordBytes] at hi; omega) (by omega))
  have hews7 : NativeRustcVm.EWsAt st7.data.dmem (off o 8) xs.toList := by
    refine bytesAt_congr (hd6 ▸ hews5) fun i hi ↦ hk7 _ ?_
    rw [hewsLen] at hi
    rw [show off o 8 + BitVec.ofNat 64 i = off o (8 + i) from off_off o 8 i]
    exact inRange_off_self (by omega) (by omega)
  have h19₇ : st7.data.regs.X19 = m0.regs.X2 := (hsv7.1 .X19 rfl).trans h19₆
  -- `b4`: the tag.
  have hm7 : Match (frameEnv m0 st7.data 64 [(o, 504)]) retS st7.data :=
    match_ofMachine (m := st7.data) (regions := [(fb, 64), (o, 504)])
      (sregions := [(64, true), (504, false)])
      ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf7.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st7.data.regs.X19.toBitVec = _; rw [h19₇]), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 (hfrO hf7)
    (hpc7.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadOod.b3_next])) hm7 fun st8 hm8 hpc8 => ?_
  simp only [PcOk] at hpc8
  sym_simp at hpc8
  cases hr3 : readScalar.run s2 with
  | none =>
    rw [hr3] at hopt
    have h0 : NativeRustcVm.WordAt st7.data.dmem (off fb 8) 0 := hopt
    rw [load_ofMachine (o := 8) rfl h0] at hpc8
    simp (config := { decide := true }) only [↓reduceIte] at hpc8
    have hnone : (readOod L).run s = none := by
      rw [run_eq, hr1]; show ((sampleChallenges L).run s1).bind _ = none
      rw [hr2]; show (readScalar.run s2).bind _ = none
      rw [hr3]; rfl
    refine Eventually.mono (finish_fail hp (Transcript.exec_after run_b4 run_b6b)
      (Transcript.after_eq run_b6b ▸
      ok_b6b) (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.ReadOod.b6Offset) NativeRustcVmArm.Vm.ReadOod.label_3_at)) hf7 (hfrO hf7) hm8)
      fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv'⟩
    · rw [hnone, hx0']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso7 q hq
  | some p =>
  obtain ⟨v, s3⟩ := p
  rw [hr3] at hopt
  obtain ⟨ht3, hel3⟩ := (hopt : OptEWAt st7.data.dmem (off fb 8) (some v))
  rw [ewAt_iff, off_off, off_off] at hel3
  rw [load_ofMachine (o := 8) rfl ht3] at hpc8
  simp (config := { decide := true }) only [↓reduceIte] at hpc8
  have hsome : (readOod L).run s = some (⟨.eq xs, v⟩, s3) := by
    rw [run_eq, hr1]; show ((sampleChallenges L).run s1).bind _ = _
    rw [hr2]; show (readScalar.run s2).bind _ = _
    rw [hr3]; rfl
  -- `b5`: the value stored, `1`.
  obtain ⟨hmid8, hmem8⟩ := Transcript.after_eq run_b4 ▸ ok_b4
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (Transcript.exec_after run_b4 run_b5)
    (hfrO hf7)
    (hpc8.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ReadOod.b4_next])) hm8 fun st9 hm9 hpc9 => ?_
  obtain ⟨oke, hx0₉, hw488, hw496, hws9⟩ :=
    Transcript.after_eq (Transcript.exec_after run_b4 run_b5) ▸ ok_b5
  obtain ⟨hs9v, hsl9⟩ := Frame.epilogue hf7 (hfrO hf7) hm9 oke
  have hx30 : st9.data.regs.X30 = m0.regs.X30 := hsl9 (32, .X30) (List.mem_cons_self ..)
  have hs9 : SameOutside st7.data.dmem st9.data.dmem (NativeRustcVm.InRange o 504) :=
    sameOutside_region (hfrO hf7) hm9 (r := 1) rfl fun w hw ↦ by
      obtain ⟨h1, h2, h3⟩ := hws9 w hw; exact ⟨h1, by omega, h3⟩
  have hsame9 := Layout.Match.same_untouched hm9 (r := 1) (o := 0) (len := 488) rfl (by decide)
    (by decide)
  rw [NativeRustcVm.addr_add_zero] at hsame9
  have w488 := wordAt_write hm9 (r := 1) (o := 488) rfl (by decide) hw488
  have w496 := wordAt_write hm9 (r := 1) (o := 496) rfl (by decide) hw496
  rw [show UInt64.ofBitVec ((Sym.load 0 16 8).eval (frameEnv m0 st7.data 64 [(o, 504)])) = v.c0
    from UInt64.toBitVec_inj.mp (load_ofMachine (o := 16) rfl hel3.1)] at w488
  rw [show UInt64.ofBitVec ((Sym.load 0 24 8).eval (frameEnv m0 st7.data 64 [(o, 504)])) = v.c1
    from UInt64.toBitVec_inj.mp (load_ofMachine (o := 24) rfl hel3.2)] at w496
  simp only [PcOk] at hpc9
  refine .done _ ⟨by rw [hpc9]; simp only [retOf, hx30], ?_, ?_, ?_, hs9v⟩
  · rw [hsome]; exact UInt64.toBitVec_inj.mp (hm9.regs .X0 _ hx0₉)
  · intro c s' h
    rw [hsome] at h
    cases h
    refine ⟨⟨xs, rfl, ⟨by rw [hxsz']; exact hL, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hxsz']
      refine NativeRustcVm.Layout.WordAt.of_same ?_ hsame9 (by decide)
      rw [hLdef, show m0.regs.X1.toNat.toUInt64 = m0.regs.X1 from UInt64.toNat.inj (by simp)]
      exact hlen7
    · exact NativeRustcVm.Layout.BytesAt.of_same hews7 (hsame9.sub (o := 8) (k := 480) (by decide))
        (by rw [hewsLen]; omega)
    · exact ewAt_iff.mpr ⟨w488, by rw [off_off]; exact w496⟩
    · exact (hnext7 v s3 hr3).frame (hm9.kept (hfrO hf7)) hRO hs9
  · intro q hq
    rw [hs9 q fun h ↦ hq (.inl h)]
    exact hso7 q hq

end

end NativeRustcVmArm.Layout.ReadOod
