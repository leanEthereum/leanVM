module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Transcript.SampleChallenges.Exec
public import NativeRustcVm.Transcript.Loop
public import NativeVm.Equiv.Transcript

/-!
# `TState::sample_challenges` on AArch64

**`sampleChallenges_spec`**: the `n` elements at X1 become `sampleChallenges n`'s challenges and the
`TState` at X0 its state, given `squeeze`'s contract. `n = 0` returns at once (`b0`, `b5`).
Otherwise `b1` saves X30, X21, X20, X19 and sets the output's cursor and end; the loop (`b2`, `b3`,
`step`, invariant `Inv`) squeezes a challenge and stores it at the cursor until the end; `b4`, `b5`
return (`finish`).
-/

namespace NativeRustcVmArm.Transcript.SampleChallenges

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSampleChallenges
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

@[expose] public section

/-- At the loop's head, `i` challenges stored: the frame, the `TState` (X20), the output's end
(X21) and cursor (X19), the first `i` challenges and the state after them, nothing changed but the
output, the `TState` and the stack. -/
structure Inv (m0 : MachineData) (a : DecArea) (s : TState) (i : Nat) (d : MachineData) : Prop where
  frame : Frame m0 32 slots d
  x20 : d.regs.X20.toBitVec = m0.regs.X0.toBitVec
  x21 : d.regs.X21.toBitVec = off m0.regs.X1.toBitVec (16 * m0.regs.X2.toNat)
  x19 : d.regs.X19.toBitVec = off m0.regs.X1.toBitVec (16 * i)
  run : ∃ xs s', (pushes sampleChallenge i).run s = some (xs, s') ∧
    NativeRustcVm.EWsAt d.dmem m0.regs.X1.toBitVec xs.toList ∧
    TStateAt d.dmem m0.regs.X0.toBitVec a s'
  same : SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange m0.regs.X1.toBitVec (16 * m0.regs.X2.toNat) q ∨
      NativeRustcVm.InRange m0.regs.X0.toBitVec tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

variable [Host] {k : Nat}

/-- The epilogue (`b4`) and the return (`b5`). -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 sampleChallengesStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b4Offset)) (hf : Frame m0 32 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.dmem = st.data.dmem ∧
      Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 32) (by
    have := hst.2.1; have : sampleChallengesStack = 464 := rfl; omega)
  have hwf : (frameEnv m0 st.data 32 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 32 []) epiS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hmem⟩ := after_eq run_b4 ▸ ok_b4
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (0, .X30) (List.mem_cons_self ..)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _)
    (hpc1.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateSampleChallenges.b4_next])) (match_nil _) fun st2 hm2 hpc2 => ?_
  obtain ⟨hmem2, hk2, h30⟩ := after_eq run_b5 ▸ ok_b5
  have hx30' : st2.data.regs.X30 = st1.data.regs.X30 := Match.reg_eq (match_nil _) hm2 rfl h30
  exact .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, hx30', hx30],
    (hm2.dmem_eq (Env.wf_nil _) hmem2).trans hd1,
    hsv.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk2)⟩

/-- **One round of the loop**: a challenge squeezed and stored; the loop goes on or returns. -/
theorem step (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : SampleChallengesPre a s m0) {i : Nat}
    (hi : i < m0.regs.X2.toNat) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b2Offset))
    (hI : Inv m0 a s i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = retOf m0 ∧ SampleChallengesPost a s m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b2Offset) ∧ i + 1 < m0.regs.X2.toNat ∧ Inv m0 a s (i + 1) st'.data))
      st := by
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩⟩ := hpre
  set t := m0.regs.X0.toBitVec with htdef
  set o := m0.regs.X1.toBitVec with hodef
  set n := m0.regs.X2.toNat with hndef
  set fb := frameBase m0 32 with hfb
  have hS : sampleChallengesStack = 464 := rfl
  have hn : sampleChallengesStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 32 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 32) (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 16 * n ≤ 2 ^ 64 := hon
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 sampleChallengesStack) sampleChallengesStack := by
    show _ + sampleChallengesStack ≤ _
    rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
  have hTF : NativeRustcVm.Apart t 760 fb 32 := apart_frame htok.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o (16 * n) fb 32 := apart_frame hoS hn (by decide)
  obtain ⟨hf, hx20, hx21, hx19, ⟨xs, s', hrun, hews, hts'⟩, hsame⟩ := hI
  have hxs : xs.size = i := pushes_size hrun
  -- `b2`: `bl squeeze`.
  have hwf : (frameEnv m0 st.data 32 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 32 []) callS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hx0₃, hx19₃, hx20₃, hx21₃⟩ := after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 32 slots st3.data := Frame.of_block hf hwf hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st.data.dmem := hm3.dmem_eq hwf hmem3
  have hX0₃ : st3.data.regs.X0.toBitVec = t := by
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hm3.regs .X0 _ hx0₃]; exact hx20
  have hX19₃ : st3.data.regs.X19 = st.data.regs.X19 := Match.reg_eq hm hm3 rfl hx19₃
  have hX20₃ : st3.data.regs.X20 = st.data.regs.X20 := Match.reg_eq hm hm3 rfl hx20₃
  have hX21₃ : st3.data.regs.X21 = st.data.regs.X21 := Match.reg_eq hm hm3 rfl hx21₃
  -- `squeeze`.
  have h3sp : st3.data.regs.SP.toNat = m0.regs.SP.toNat - 32 := by
    rw [← UInt64.toNat_toBitVec, hf3.sp, frameBase_toNat hn (by decide)]
  have hrcOut : ∀ q, (NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' hoR) hrc.2.1 hon h hq
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hso3 : SameOutside m0.dmem st3.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) := by
    rw [hd3]; exact hsame
  have hts3 : TStateAt st3.data.dmem t a s' := by rw [hd3]; exact hts'
  have hpre3 : SqueezePre s'.sponge st3.data := by
    unfold SqueezePre
    rw [hX0₃]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 sampleChallengesStack).toNat ∨
        (stackBelow m0 sampleChallengesStack).toNat + sampleChallengesStack ≤ t.toNat := htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf3.kept hf3.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hn (by decide) h3sp (by decide),
      ⟨fun j hj ↦ hts3.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_,
        apart_callee (n := sampleChallengesStack) (F := 32) ?_ hf3.sp hn (by decide) (by decide),
        ?_⟩, hts3.sponge⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
  refine call_then hpc3 (hsq s'.sponge) hpre3 fun st4 hpc4 ⟨hc0, hc1, hsp4, hs4, hsv4⟩ => ?_
  rw [hX0₃] at hsp4 hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data squeezeStack) squeezeStack q →
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q ∧
        ¬ NativeRustcVm.InRange fb 32 q :=
    fun q hq ↦ inRange_callee hf3.sp hn (by decide) (by decide) hq
  have hT328 : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t 760 q :=
    fun q h ↦ inRange_sub hTn (le_refl _) (by simp only [spongeBytes]; omega) h
  have hf4 : Frame m0 32 slots st4.data := by
    refine Frame.call hf3 hsv4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw (hT328 q hq)
    · exact (hcal4 q hq).2
  have hts4 : TStateAt st4.data.dmem t a { s' with sponge := s'.sponge.squeeze.2 } := by
    refine hts3.with_sponge hsv4.2.2 (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h
      (hcal4 q hq).1, fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h (hcal4 q hq).1⟩)
      (fun q hq ↦ hs4 q ?_) hsp4
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hlen : 16 * xs.toList.length ≤ 16 * n := by
    rw [Array.length_toList, hxs]; omega
  have hews4 : NativeRustcVm.EWsAt st4.data.dmem o xs.toList := by
    refine ewsAt_keep hs4 (by omega) (fun q hq hr ↦ ?_) (hd3 ▸ hews)
    have hq' : NativeRustcVm.InRange o (16 * n) q := inRange_mono hq hlen
    rcases hr with hr | hr
    · exact not_inRange_of_apart hoT hon hTn hq' (hT328 q hr)
    · exact not_inRange_of_apart hoS hon hsnw hq' (hcal4 q hr).1
  have hso4 : SameOutside m0.dmem st4.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      rw [hs4 q (by
        rintro (h | h)
        · exact hq.2.1 (hT328 q h)
        · exact hq.2.2 (hcal4 q h).1)]
      exact hso3 q (by simp only [not_or]; exact hq)
  have hX19₄ : st4.data.regs.X19.toBitVec = off o (16 * i) := by
    rw [show st4.data.regs.X19 = st.data.regs.X19 from (hsv4.1 .X19 rfl).trans hX19₃]
    exact hx19
  have hX20₄ : st4.data.regs.X20.toBitVec = t := by
    rw [show st4.data.regs.X20 = st.data.regs.X20 from (hsv4.1 .X20 rfl).trans hX20₃]
    exact hx20
  have hX21₄ : st4.data.regs.X21.toBitVec = off o (16 * n) := by
    rw [show st4.data.regs.X21 = st.data.regs.X21 from (hsv4.1 .X21 rfl).trans hX21₃]
    exact hx21
  -- `b3`: the challenge stored at the cursor, the cursor advanced.
  set w := off o (16 * i) with hw
  have hwn : w.toNat = o.toNat + 16 * i := toNat_off (by omega)
  have hwF : NativeRustcVm.Apart fb 32 w 16 := by
    have h : o.toNat + 16 * n ≤ fb.toNat ∨ fb.toNat + 32 ≤ o.toNat := hoF
    show fb.toNat + 32 ≤ w.toNat ∨ w.toNat + 16 ≤ fb.toNat
    omega
  have hwf4 : (frameEnv m0 st4.data 32 [(w, 16)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst (by decide)) hf4.kept, hfnw⟩,
      ⟨Mapped.keeps (mapped_off hom (by omega)) hf4.kept, by show w.toNat + 16 ≤ 2 ^ 64; omega⟩,
      trivial⟩ (List.pairwise_pair.mpr hwF)
  have hm4 : Match (frameEnv m0 st4.data 32 [(w, 16)]) storeS st4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX19₄, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateSampleChallenges.b2_next])) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hw0, hw1, hws5, hx19₅, hx20₅, hx21₅⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 32 slots st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hs5 : SameOutside st4.data.dmem st5.data.dmem (NativeRustcVm.InRange w 16) :=
    sameOutside_region hwf4 hm5 (r := 1) rfl hws5
  set c := s'.sponge.squeeze.1 with hcdef
  have hel : NativeRustcVm.EWAt st5.data.dmem w c := by
    refine ewAt_iff.mpr ⟨?_, ?_⟩
    · have := wordAt_write hm5 (r := 1) (o := 0) (b := w) (sz := 16) rfl (by decide) hw0
      rwa [off_zero, show UInt64.ofBitVec ((Sym.reg .X0).eval (frameEnv m0 st4.data 32 [(w, 16)]))
        = c.c0 from by show UInt64.ofBitVec st4.data.regs.X0.toBitVec = _; rw [hc0]] at this
    · have := wordAt_write hm5 (r := 1) (o := 8) (b := w) (sz := 16) rfl (by decide) hw1
      rwa [show UInt64.ofBitVec ((Sym.reg .X1).eval (frameEnv m0 st4.data 32 [(w, 16)]))
        = c.c1 from by show UInt64.ofBitVec st4.data.regs.X1.toBitVec = _; rw [hc1]] at this
  have hews5 : NativeRustcVm.EWsAt st5.data.dmem o (xs.push c).toList := by
    refine ewsAt_push.mpr ⟨ewsAt_keep hs5 (by omega) (fun q hq hr ↦ ?_) hews4, ?_⟩
    · rw [Array.length_toList, hxs] at hq
      have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
      have hon16 : NativeRustcVm.NoWrap o (16 * i) := by show o.toNat + 16 * i ≤ 2 ^ 64; omega
      rw [inRange_iff' hon16] at hq
      rw [inRange_iff' hwnw] at hr
      omega
    · rw [hxs]; exact hel
  have hR5 : ∀ q, NativeRustcVm.InRange w 16 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    intro q hq
    have hq' : NativeRustcVm.InRange o (16 * n) q := by
      refine inRange_sub hon (by omega) (by omega) hq
    exact ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq' h,
      fun h ↦ not_inRange_of_apart hoA hon hAn hq' h⟩
  have hts5 : TStateAt st5.data.dmem t a { s' with sponge := s'.sponge.squeeze.2 } :=
    hts4.frame (hm5.kept hwf4) hR5 hs5
  have hso5 : SameOutside m0.dmem st5.data.dmem (fun q ↦ NativeRustcVm.InRange o (16 * n) q ∨
      NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) :=
    fun q hq ↦ by
      rw [hs5 q fun h ↦ hq (Or.inl (inRange_sub hon (by omega) (by omega) h))]
      exact hso4 q hq
  have hrun' : (pushes sampleChallenge (i + 1)).run s =
      some (xs.push c, { s' with sponge := s'.sponge.squeeze.2 }) := by
    rw [pushes_succ, hrun]; rfl
  have hX19₅ : st5.data.regs.X19.toBitVec = off o (16 * (i + 1)) := by
    show (st5.data.regs.getXReg .X19).toBitVec = _
    rw [hm5.regs .X19 _ hx19₅]
    show w + BitVec.ofInt 64 16 = _
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega]
  have hX20₅ : st5.data.regs.X20.toBitVec = t := by
    rw [← hX20₄]; exact congrArg UInt64.toBitVec (Match.reg_eq hm4 hm5 rfl hx20₅)
  have hX21₅ : st5.data.regs.X21.toBitVec = off o (16 * n) := by
    rw [← hX21₄]; exact congrArg UInt64.toBitVec (Match.reg_eq hm4 hm5 rfl hx21₅)
  -- The cursor against the end.
  have hcond : (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .X21)).not.eval
      (frameEnv m0 st4.data 32 [(w, 16)]) = decide (i + 1 ≠ n) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs]
    rw [show (frameEnv m0 st4.data 32 [(w, 16)]).base 1 = w from rfl,
      show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega, show (st4.data.regs.getXReg .X21).toBitVec =
        off o (16 * n) from hX21₄,
      show (off o (16 * (i + 1)) == off o (16 * n)) = decide (i + 1 = n) from by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact off_eq_iff hon' hi]
    by_cases h : i + 1 = n <;> simp [h]
  simp only [PcOk] at hpc5
  rw [hcond] at hpc5
  by_cases hlast : i + 1 = n
  · -- The end: the epilogue.
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc5
    refine Eventually.mono (finish hp hst (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateSampleChallenges.b3_next])) hf5)
      fun st' ⟨hpc', hd', hsv'⟩ ↦ Or.inl ⟨hpc', ⟨⟨xs.push c, _, ?_, hd' ▸ hews5, hd' ▸ hts5⟩,
        fun q hq ↦ by rw [hd']; exact hso5 q hq, hsv'⟩⟩
    rw [sampleChallenges_eq, show m0.regs.X2.toNat = i + 1 from hlast.symm]; exact hrun'
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc5
    exact .done _ (Or.inr ⟨hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.TStateSampleChallenges.b2Offset) NativeRustcVmArm.Vm.TStateSampleChallenges.label_2_at), by omega,
      ⟨hf5, hX20₅, hX21₅, hX19₅, ⟨_, _, hrun', hews5, hts5⟩, hso5⟩⟩)

/-- **`TState::sample_challenges` meets its contract.** -/
theorem sampleChallenges_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s) := by
  intro m0 hpre
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩⟩ := id hpre
  set t := m0.regs.X0.toBitVec with htdef
  set o := m0.regs.X1.toBitVec with hodef
  set n := m0.regs.X2.toNat with hndef
  set fb := frameBase m0 32 with hfb
  have hn : sampleChallengesStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 32 ≤ 2 ^ 64 :=
    frame_noWrap (m := m0) (F := 32) (by have : sampleChallengesStack = 464 := rfl; omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTF : NativeRustcVm.Apart t 760 fb 32 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 32 := apart_frame htok.2.1 hn (by decide)
  -- `b0`: `n = 0`?
  unfold NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateSampleChallenges.entryOffset) NativeRustcVmArm.Vm.TStateSampleChallenges.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 (Env.wf_nil m0) (match_nil m0)
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hmem1, hk1⟩ := after_eq run_b0 ▸ ok_b0
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq (Env.wf_nil _) hmem1
  have hsv1 : Saved m0 st1.data := Match.saved (match_nil m0) hm1 (Env.wf_nil _) rfl hk1
  have hX0 : st1.data.regs.X0 = m0.regs.X0 := Match.reg_eq (r := .X0) (match_nil m0) hm1 rfl rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X1 := Match.reg_eq (r := .X1) (match_nil m0) hm1 rfl rfl
  have hX2 : st1.data.regs.X2 = m0.regs.X2 := Match.reg_eq (r := .X2) (match_nil m0) hm1 rfl rfl
  have hX30 : st1.data.regs.X30 = m0.regs.X30 :=
    Match.reg_eq (r := .X30) (match_nil m0) hm1 rfl rfl
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `n = 0`: nothing to sample.
    rename_i hc
    have hn0 : n = 0 := by
      sym_simp at hc
      simp only [Env.ofMachine_regs, beq_iff_eq] at hc
      show m0.regs.X2.toBitVec.toNat = 0
      exact (congrArg BitVec.toNat hc).trans rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _)
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.TStateSampleChallenges.b5Offset) NativeRustcVmArm.Vm.TStateSampleChallenges.label_4_at)) (match_nil _) fun st2 hm2 hpc2 => ?_
    obtain ⟨hmem2, hk2, h30⟩ := after_eq run_b5 ▸ ok_b5
    have hd2 : st2.data.dmem = m0.dmem := (hm2.dmem_eq (Env.wf_nil _) hmem2).trans hd1
    have hx30 : st2.data.regs.X30 = m0.regs.X30 :=
      (Match.reg_eq (match_nil _) hm2 rfl h30).trans hX30
    refine .done _ ⟨by simp only [PcOk] at hpc2; rw [hpc2]; simp only [retOf, hx30],
      ⟨⟨#[], s, by rw [show m0.regs.X2.toNat = 0 from hn0]; rfl, ewsAt_nil _ _, hd2 ▸ hts⟩, fun q _ ↦ by rw [hd2],
        hsv1.trans (Match.saved (match_nil _) hm2 (Env.wf_nil _) rfl hk2)⟩⟩
  rename_i hc
  have hn0 : n ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    exact h0
  -- `b1`: the prologue, the output's cursor and end.
  have hwf1 : (frameEnv m0 st1.data 32 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 32) hst (by decide)) hsv1.2.2, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm1' : Match (frameEnv m0 st1.data 32 []) proS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [show st1.data.regs.SP = m0.regs.SP from hsv1.2.1]; exact frameBase_add.symm)
      trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
    (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b0Offset + NativeRustcVmArm.Vm.TStateSampleChallenges.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateSampleChallenges.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx19, hx20, hx21⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 32 slots st2.data :=
    Frame.of_prologue_from hsv1 (fun p hp ↦ by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hX30
      all_goals exact hsv1.1 _ rfl) hwf1 hm2 hpro slots_le
  have hs2 : SameOutside st1.data.dmem st2.data.dmem (NativeRustcVm.InRange fb 32) :=
    sameOutside_region hwf1 hm2 rfl hws2
  have hr0 : (st1.data.regs.getXReg .X0).toBitVec = t := by
    show st1.data.regs.X0.toBitVec = _; rw [hX0]
  have hr1 : (st1.data.regs.getXReg .X1).toBitVec = o := by
    show st1.data.regs.X1.toBitVec = _; rw [hX1]
  have hr2 : (st1.data.regs.getXReg .X2).toBitVec.toNat = n := by
    show st1.data.regs.X2.toBitVec.toNat = _; rw [hX2]; rfl
  have hX19 : st2.data.regs.X19.toBitVec = off o (16 * 0) := by
    show (st2.data.regs.getXReg .X19).toBitVec = _
    rw [hm2.regs .X19 _ hx19, Nat.mul_zero, off_zero]
    exact hr1
  have hX20 : st2.data.regs.X20.toBitVec = t := by
    show (st2.data.regs.getXReg .X20).toBitVec = _
    rw [hm2.regs .X20 _ hx20]
    exact hr0
  have hX21 : st2.data.regs.X21.toBitVec = off o (16 * n) := by
    show (st2.data.regs.getXReg .X21).toBitVec = _
    rw [hm2.regs .X21 _ hx21]
    simp only [endSym]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, hr1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hr2, MemWidth.bits]
    omega
  have hsame2 : SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 32) := fun q hq ↦ by
    rw [hs2 q hq, hd1]
  have hInv : Inv m0 a s 0 st2.data := by
    refine ⟨hf2, hX20, hX21, hX19, ⟨#[], s, pushes_zero _ _, ewsAt_nil _ _, ?_⟩, fun q hq ↦ ?_⟩
    · exact hts.frame hf2.kept (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
        fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩) hsame2
    · exact hsame2 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack hn (by decide) h)))
  refine loop (I := fun j st ↦ ∃ i, j = n - i ∧ i < n ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSampleChallenges.b2Offset) ∧
      Inv m0 a s i st.data)
    (fun j st ⟨i, hj, hi, hpc, hI⟩ ↦ Eventually.mono (step hp hsq hpre hi hpc hI) fun st' h ↦ ?_)
    ⟨0, rfl, by omega, hpc2.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateSampleChallenges.b1_next]), hInv⟩
  rcases h with h | ⟨hpc', hlt, hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩

end


end NativeRustcVmArm.Transcript.SampleChallenges
