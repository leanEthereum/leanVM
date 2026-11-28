module

public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVmX64.Transcript.SampleChallenges.Exec
public import NativeRustcVm.Transcript.Loop
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `TState::sample_challenges` on x86-64

**`sampleChallenges_spec`**: the `n` elements at RSI become `sampleChallenges n`'s challenges and
the `TState` at RDI its state, given `squeeze`'s contract. `n = 0` returns at once (`b0`, `b5`).
Otherwise `b1` pushes R15, R14, RBX and sets the output's cursor and end; the loop (`b2`, `b3`,
`step`, invariant `Inv`) squeezes a challenge and stores it at the cursor until the end; `b4`, `b5`
return.
-/

namespace NativeRustcVmX64.Transcript.SampleChallenges

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSampleChallenges
open NativeRustcVm.Transcript NativeVm.Model

@[expose] public section

/-- At the loop's head, `i` challenges stored: the frame, the `TState` (R15), the output's end
(RBX) and cursor (R14), the first `i` challenges and the state after them, nothing changed but the
output, the `TState` and the stack. -/
structure Inv (m0 : MachineData) (a : DecArea) (s : TState) (i : Nat) (d : MachineData) : Prop where
  frame : Frame m0 32 slots 8 d
  r15 : reg d .r15 = reg m0 .rdi
  rbx : reg d .rbx = off (reg m0 .rsi) (16 * (reg m0 .rdx).toNat)
  r14 : reg d .r14 = off (reg m0 .rsi) (16 * i)
  run : ∃ xs s', (pushes sampleChallenge i).run s = some (xs, s') ∧
    NativeRustcVm.EWsAt d.dmem (reg m0 .rsi) xs.toList ∧ TStateAt d.dmem (reg m0 .rdi) a s'
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦
    NativeRustcVm.InRange (reg m0 .rsi) (16 * (reg m0 .rdx).toNat) q ∨
      NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q)

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

variable [Host] {k : Nat}

/-- **One round of the loop**: a challenge squeezed and stored; the loop goes on or returns. -/
theorem step (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {a : DecArea} {s : TState} {m0 : MachineData} (hpre : SampleChallengesPre a s m0) {i : Nat}
    (hi : i < (reg m0 .rdx).toNat) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSampleChallenges.b2Offset))
    (hI : Inv m0 a s i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        SampleChallengesPost a s m0 st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSampleChallenges.b2Offset) ∧ i + 1 < (reg m0 .rdx).toNat ∧
        Inv m0 a s (i + 1) st'.data)) st := by
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩, hgot⟩ := hpre
  set t := reg m0 .rdi with htdef
  set o := reg m0 .rsi with hodef
  set n := (reg m0 .rdx).toNat with hndef
  set fb := stackBelow m0 32 with hfb
  have hn : sampleChallengesStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (32 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hon' : o.toNat + 16 * n ≤ 2 ^ 64 := hon
  have hsnw := noWrap_stackBelow hst
  have hTF : NativeRustcVm.Apart t 760 fb (32 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (32 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hoF : NativeRustcVm.Apart o (16 * n) fb (32 + 8) := apart_frame hoS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (32 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hfS : ∀ q, NativeRustcVm.InRange fb 32 q →
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q :=
    fun q h ↦ inRange_frame_stack h8 hn (by decide) h
  obtain ⟨hf, hx15, hx3, hx14, ⟨xs, s', hrun, hews, hts'⟩, hsame⟩ := hI
  have hxs : xs.size = i := pushes_size hrun
  -- `b2`: `call squeeze`.
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 32) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateSampleChallenges.b2Offset + b2.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf (fun _ _ ↦ rfl) hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hws3, hx7₃, hx15₃, hx14₃, hx3₃⟩ := after_eq run_b2 ▸ ok_b2
  have hf3 : Frame m0 32 slots 0 st3.data := Frame.of_block hf hwf hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside st.data.dmem st3.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low hwf hm3 (r := 0) rfl (by decide) hws3
  have hsp3 : rspOf st3.data = fb := by rw [hf3.sp, off_zero]
  have hX7₃ : reg st3.data .rdi = t := (hm3.regs .rdi _ hx7₃).trans hx15
  -- `squeeze`.
  have hrcOut : ∀ q, (NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) →
      ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' hoR) hrc.2.1 hon h hq
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) :=
    fun q hq ↦ by
      rw [hs3 q fun h ↦ hq (Or.inr (Or.inr (hfS q (inRange_mono h (by decide)))))]
      exact hsame q hq
  have hts3 : TStateAt st3.data.dmem t a s' :=
    hts'.frame (hm3.kept hwf) (fun q hq ↦ hRF q (inRange_mono hq (by decide))) hs3
  have hpre3 : SqueezePre s'.sponge st3.data := by
    unfold SqueezePre
    rw [hX7₃]
    have h1 : t.toNat + 760 ≤ (stackBelow m0 sampleChallengesStack).toNat ∨
        (stackBelow m0 sampleChallengesStack).toNat + (sampleChallengesStack + 8) ≤ t.toNat :=
      htok.1
    have h2 : t.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ t.toNat := htok.2.2
    refine ⟨stackOk_callee hst hf3.kept hsp3 (by decide),
      RcAt.callee hrc (rc_keep hso3 hrcOut) hsp3 hn (by decide),
      ⟨fun j hj ↦ hts3.footprint.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega), ?_,
        apart_callee (n := sampleChallengesStack) (F := 32) ?_ hsp3 hn (by decide), ?_⟩,
      hts3.sponge, ?_⟩
    · show t.toNat + 328 ≤ 2 ^ 64; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · show t.toNat + 328 ≤ _ ∨ _ ≤ t.toNat; omega
    · refine got_callee hgot (got_keep hgot hst (writes := [(o, 16 * n), (t, tstateBytes)])
        (by
          intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl <;> simp [o, n, t])
        (by
          intro b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact hon
          · exact hTn)
        (by simpa [or_assoc] using hso3))
        hsp3 hn (by decide) ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Apart.sub ((hgot.1 l hl).2.2.2 (t, tstateBytes) (by simp [t]))
          (Nat.le_refl _) (by simp only [spongeBytes, tstateBytes]; omega)
      · exact (hgot.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine call_then hpc3 (hsq s'.sponge) hpre3
    fun st4 hpc4 hrsp4 ⟨hc0, hc1, hsp4, hs4, hsv4⟩ => ?_
  rw [hX7₃] at hsp4 hs4
  have hcal4 : ∀ q, NativeRustcVm.InRange (stackBelow st3.data squeezeStack) squeezeStack q →
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q ∧
        ¬ NativeRustcVm.InRange fb (32 + 8) q :=
    fun q hq ↦ inRange_callee hsp3 h8 hn (by decide) hq
  have hT328 : ∀ q, NativeRustcVm.InRange t spongeBytes q → NativeRustcVm.InRange t 760 q :=
    fun q h ↦ inRange_mono h (by simp only [spongeBytes]; omega)
  have hf4 : Frame m0 32 slots 8 st4.data := by
    refine Frame.call hf3 hsv4 hrsp4 hs4 (fun q hq ↦ ?_) hfnw slots_le
    rcases hq with hq | hq
    · exact not_inRange_of_apart hTF hTn hfnw (hT328 q hq)
    · exact (hcal4 q hq).2
  have hts4 : TStateAt st4.data.dmem t a { s' with sponge := s'.sponge.squeeze.2 } := by
    refine hts3.with_sponge hsv4.2 (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h
      (inRange_mono (hcal4 q hq).1 (by omega)), fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h
      (inRange_mono (hcal4 q hq).1 (by omega))⟩)
      (fun q hq ↦ hs4 q ?_) hsp4
    rintro (h | h)
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn' : NativeRustcVm.NoWrap t 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw.2, hq'⟩)
    · exact hq (Or.inr h)
  have hlen : 16 * xs.toList.length ≤ 16 * n := by
    rw [Array.length_toList, hxs]; omega
  have hews3 : NativeRustcVm.EWsAt st3.data.dmem o xs.toList :=
    ewsAt_keep hs3 (by omega) (fun q hq hr ↦ not_inRange_of_apart hoF hon hfnw
      (inRange_mono hq hlen) (inRange_mono hr (by decide))) hews
  have hews4 : NativeRustcVm.EWsAt st4.data.dmem o xs.toList := by
    refine ewsAt_keep hs4 (by omega) (fun q hq hr ↦ ?_) hews3
    have hq' : NativeRustcVm.InRange o (16 * n) q := inRange_mono hq hlen
    rcases hr with hr | hr
    · exact not_inRange_of_apart hoT hon hTn hq' (hT328 q hr)
    · exact not_inRange_of_apart hoS hon hsnw hq' (inRange_mono (hcal4 q hr).1 (by omega))
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) :=
    fun q hq ↦ by
      simp only [not_or] at hq
      rw [hs4 q (by
        rintro (h | h)
        · exact hq.2.1 (hT328 q h)
        · exact hq.2.2 (hcal4 q h).1)]
      exact hso3 q (by simp only [not_or]; exact hq)
  have hX14₄ : reg st4.data .r14 = off o (16 * i) :=
    (hsv4.1 .r14 rfl).trans ((hm3.regs .r14 _ hx14₃).trans hx14)
  have hX15₄ : reg st4.data .r15 = t := (hsv4.1 .r15 rfl).trans ((hm3.regs .r15 _ hx15₃).trans hx15)
  have hX3₄ : reg st4.data .rbx = off o (16 * n) :=
    (hsv4.1 .rbx rfl).trans ((hm3.regs .rbx _ hx3₃).trans hx3)
  -- `b3`: the challenge stored at the cursor, the cursor advanced.
  set w := off o (16 * i) with hw
  have hwn : w.toNat = o.toNat + 16 * i := toNat_off (by omega)
  have hwF : NativeRustcVm.Apart fb (32 + 8) w 16 := by
    have h : o.toNat + 16 * n ≤ fb.toNat ∨ fb.toNat + (32 + 8) ≤ o.toNat := hoF
    show fb.toNat + (32 + 8) ≤ w.toNat ∨ w.toNat + 16 ≤ fb.toNat
    omega
  have hwf4 := frame_wf (m0 := m0) (d := st4.data) (F := 32) (rest := [(w, 16)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf4.kept, hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps (mapped_off hom (by omega)) hf4.kept,
        by show w.toNat + 16 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr hwF)
  have hm4 : Match (frameEnv m0 st4.data 32 [(w, 16)] (fun _ ↦ 0) 0) storeS st4.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf4.rsp_eval, known_ptr rfl hX14₄, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf4 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSampleChallenges.b2_next)) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hw0, hw1, hws5, hx14₅, hx15₅, hx3₅⟩ := after_eq run_b3 ▸ ok_b3
  have hf5 : Frame m0 32 slots 8 st5.data := Frame.of_block hf4 hwf4 hm5 hmid5 slots_le
  have hs5 : NativeRustcVm.SameOutside st4.data.dmem st5.data.dmem (NativeRustcVm.InRange w 16) :=
    sameOutside_region hwf4 hm5 (r := 1) rfl hws5
  set c := s'.sponge.squeeze.1 with hcdef
  have hel : NativeRustcVm.EWAt st5.data.dmem w c := by
    refine ewAt_iff.mpr ⟨?_, ?_⟩
    · have := wordAt_write hm5 (r := 1) (o := 0) (b := w) (sz := 16) rfl (by decide)
        (fun i hi ↦ by rw [Nat.zero_add]; exact hw0 i hi)
      rwa [off_zero, show UInt64.ofBitVec ((Sym.reg .rax).eval
        (frameEnv m0 st4.data 32 [(w, 16)] (fun _ ↦ 0) 0)) = c.c0 from by
          show UInt64.ofBitVec (reg st4.data .rax) = _; rw [hc0]] at this
    · have := wordAt_write hm5 (r := 1) (o := 8) (b := w) (sz := 16) rfl (by decide) hw1
      rwa [show UInt64.ofBitVec ((Sym.reg .rdx).eval
        (frameEnv m0 st4.data 32 [(w, 16)] (fun _ ↦ 0) 0)) = c.c1 from by
          show UInt64.ofBitVec (reg st4.data .rdx) = _; rw [hc1]] at this
  have hews5 : NativeRustcVm.EWsAt st5.data.dmem o (xs.push c).toList := by
    refine ewsAt_push.mpr ⟨ewsAt_keep hs5 (by omega) (fun q hq hr ↦ ?_) hews4, ?_⟩
    · rw [Array.length_toList, hxs] at hq
      have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
      have hon16 : NativeRustcVm.NoWrap o (16 * i) := by show o.toNat + 16 * i ≤ 2 ^ 64; omega
      rw [inRange_iff' hon16] at hq
      rw [inRange_iff' hwnw] at hr
      omega
    · rw [hxs]; exact hel
  have hwo : ∀ q, NativeRustcVm.InRange w 16 q → NativeRustcVm.InRange o (16 * n) q := by
    intro q hq
    have hwnw : NativeRustcVm.NoWrap w 16 := by show w.toNat + 16 ≤ 2 ^ 64; omega
    rw [inRange_iff' hwnw] at hq
    rw [inRange_iff' hon]
    omega
  have hts5 : TStateAt st5.data.dmem t a { s' with sponge := s'.sponge.squeeze.2 } :=
    hts4.frame (hm5.kept hwf4) (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hoT hon hTn (hwo q hq) h,
      fun h ↦ not_inRange_of_apart hoA hon hAn (hwo q hq) h⟩) hs5
  have hso5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem (fun q ↦
      NativeRustcVm.InRange o (16 * n) q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow m0 sampleChallengesStack) sampleChallengesStack q) :=
    fun q hq ↦ by
      rw [hs5 q fun h ↦ hq (Or.inl (hwo q h))]
      exact hso4 q hq
  have hrun' : (pushes sampleChallenge (i + 1)).run s =
      some (xs.push c, { s' with sponge := s'.sponge.squeeze.2 }) := by
    rw [pushes_succ, hrun]; rfl
  have hX14₅ : reg st5.data .r14 = off o (16 * (i + 1)) := by
    rw [show reg st5.data .r14 = _ from hm5.regs .r14 _ hx14₅]
    show w + BitVec.ofInt 64 16 = _
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega]
  have hX15₅ : reg st5.data .r15 = t := (hm5.regs .r15 _ hx15₅).trans hX15₄
  have hX3₅ : reg st5.data .rbx = off o (16 * n) := (hm5.regs .rbx _ hx3₅).trans hX3₄
  -- The cursor against the end.
  have hcond : (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .rbx)).not.eval
      (frameEnv m0 st4.data 32 [(w, 16)] (fun _ ↦ 0) 0) = decide (i + 1 ≠ n) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, Sym.eval, Env.ofMachine_regs]
    rw [show (frameEnv m0 st4.data 32 [(w, 16)] (fun _ ↦ 0) 0).base 1 = w from rfl,
      show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, hw, off_add,
      show 16 * i + 16 = 16 * (i + 1) by omega,
      show st4.data.regs.get64 .rbx = off o (16 * n) from hX3₄,
      show (off o (16 * (i + 1)) == off o (16 * n)) = decide (i + 1 = n) from by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact off_eq_iff hon' hi]
    by_cases h : i + 1 = n <;> simp [h]
  simp only [PcOk] at hpc5
  rw [hcond] at hpc5
  by_cases hlast : i + 1 = n
  · -- The end: the epilogue.
    simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc5
    have hwf5 := frame_wf (m0 := m0) (d := st5.data) (F := 32) (rest := []) (vars := fun _ ↦ 0)
      (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf5.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf5 nofun
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSampleChallenges.b3_next))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨hf5.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st6 hm6 hpc6 => ?_
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b4 exit_end) hwf5 nofun
      (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSampleChallenges.b4_next)) hm6 fun st7 hm7 hpc7 => ?_
    obtain ⟨hepi, hmem7⟩ := ok_end
    obtain ⟨hsv7, hrsp7⟩ := Frame.epilogue hf5 hwf5 hm7 hepi
    have hd7 : st7.data.dmem = st5.data.dmem := hm7.dmem_eq hwf5 hmem7
    simp only [PcOk] at hpc7
    refine .done _ (Or.inl ⟨by rw [hpc7]; exact hf5.load_ret hst (by decide), hrsp7,
      ⟨xs.push c, _, ?_, hd7 ▸ hews5, hd7 ▸ hts5⟩, fun q hq ↦ by rw [hd7]; exact hso5 q hq,
      hsv7⟩)
    rw [sampleChallenges_eq, show (reg m0 .rdx).toNat = i + 1 from hlast.symm]; exact hrun'
  · simp only [hlast, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hpc5
    exact .done _ (Or.inr ⟨hpc5.trans (hp.label NativeRustcVmX64.Vm.TStateSampleChallenges.label_2_at), by omega,
      ⟨hf5, hX15₅, hX3₅, hX14₅, ⟨_, _, hrun', hews5, hts5⟩, hso5⟩⟩)

/-- **`TState::sample_challenges` meets its contract.** -/
theorem sampleChallenges_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s) := by
  intro m0 hpre
  obtain ⟨hst, hrc, hts, htok, ⟨hom, hon, hoT, hoA, hoS, hoR⟩, -⟩ := id hpre
  set t := reg m0 .rdi with htdef
  set o := reg m0 .rsi with hodef
  set n := (reg m0 .rdx).toNat with hndef
  set fb := stackBelow m0 32 with hfb
  have hn : sampleChallengesStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (32 + 8) := frame_noWrap hst (by decide)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTF : NativeRustcVm.Apart t 760 fb (32 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (32 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  -- `b0`: `n = 0`?
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 32) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped hst (by decide), hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 32 [] (fun _ ↦ 0) 0) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateSampleChallenges.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  simp only [PcOk] at hpc1
  split at hpc1
  · -- `n = 0`: nothing to sample.
    rename_i hc
    have hn0 : n = 0 := by
      sym_simp_at hc
      simp only [Env.ofMachine_regs, BitVec.and_self, beq_iff_eq] at hc
      show (m0.regs.get64 .rdx).toNat = 0
      rw [hc]; rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5a hwf0 nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateSampleChallenges.label_4_at)) hm1 fun st2 hm2 hpc2 => ?_
    obtain ⟨hk2, hmem2, hrsp2⟩ := ok_b5a
    have hd2 : st2.data.dmem = m0.dmem := hm2.dmem_eq hwf0 hmem2
    simp only [PcOk] at hpc2
    refine .done _ ⟨by rw [hpc2]; exact Frame.entry.load_ret hst (by decide),
      (hm2.regs .rsp _ hrsp2).trans ((eval_ptr0 (o := 40)).trans (frame_add 32 8)),
      ⟨#[], s, by rw [show (reg m0 .rdx).toNat = 0 from hn0]; rfl, ewsAt_nil _ _, hd2 ▸ hts⟩,
      fun q _ ↦ by rw [hd2], Match.saved hm0 hm2 hwf0 rfl hk2⟩
  rename_i hc
  have hn0 : n ≠ 0 := by
    intro h0
    apply hc
    sym_simp
    simp only [Env.ofMachine_regs, BitVec.and_self, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    exact h0
  -- `b1`: the prologue, the output's cursor and end.
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf0 nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSampleChallenges.b0_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro, hws2, hx3, hx14, hx15⟩ := after_eq run_b1 ▸ ok_b1
  have hf2 : Frame m0 32 slots 8 st2.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro slots_le (by decide)
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (NativeRustcVm.InRange fb 32) :=
    sameOutside_low hwf0 hm2 (r := 0) rfl (by decide) hws2
  have hX3 : reg st2.data .rbx = off o (16 * n) := by
    rw [show reg st2.data .rbx = _ from hm2.regs .rbx _ hx3]
    simp only [endSym, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    apply BitVec.eq_of_toNat_eq
    have e1 : (m0.regs.get64 .rsi).toNat = o.toNat := rfl
    have e2 : (m0.regs.get64 .rdx).toNat = n := rfl
    simp only [off, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl, Nat.shiftLeft_eq,
      show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl, e1, e2]
    omega
  have hInv : Inv m0 a s 0 st2.data := by
    refine ⟨hf2, hm2.regs .r15 _ hx15, hX3,
      (hm2.regs .r14 _ hx14).trans (by rw [Nat.mul_zero, off_zero]; rfl),
      ⟨#[], s, pushes_zero _ _, ewsAt_nil _ _, ?_⟩, fun q hq ↦ ?_⟩
    · exact hts.frame hf2.kept (fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h
        (inRange_mono hq (by decide)), fun h ↦ not_inRange_of_apart hAF hAn hfnw h
        (inRange_mono hq (by decide))⟩) hs2
    · exact hs2 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack h8 hn (by decide) h)))
  refine loop (I := fun j st ↦ ∃ i, j = n - i ∧ i < n ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSampleChallenges.b2Offset) ∧
      Inv m0 a s i st.data)
    (fun j st ⟨i, hj, hi, hpc, hI⟩ ↦ Eventually.mono (step hp hsq hpre hi hpc hI) fun st' h ↦ ?_)
    ⟨0, rfl, by omega, hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateSampleChallenges.b1_next), hInv⟩
  rcases h with h | ⟨hpc', hlt, hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n - (i + 1), by omega, i + 1, rfl, hlt, hpc', hI'⟩

end

end NativeRustcVmX64.Transcript.SampleChallenges
