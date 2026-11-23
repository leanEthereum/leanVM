module

public import NativeRustcVmX64.Layout.ReadOod.Exec
public import NativeRustcVmX64.Layout.Stack.Common
public import NativeVm.Model.Stack
public import NativeRustcVmX64.Code.Vm.ReadOod.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `read_ood` on x86-64

`b0` pushes R15, R14, RBX and grinds `15` bits; `b1` (`stack_log > 30`, never: `stack_log ≤ 30`)
and `b2` (the grind failed) branch to `b8`, which returns AL = `0`; `b3` stores `stack_log` as the
output's length and samples the challenges into its buffer; `b4` reads a scalar into the frame;
`b5` tests its tag (`b7`, AL = `0`, on `None`); `b6` stores the value at `488`, AL = `1`; `b8`
restores the registers and returns.
-/

namespace NativeRustcVmX64.Layout.ReadOod

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadOod NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmX64.Layout.Stack (eval_ptr_off tag8_eval big_false sampleChallenges_size)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem stack_eq : readOodStack = 688 := rfl

/-- `readOod` step by step. -/
theorem run_eq (n : Nat) (s : TState) :
    (readOod n).run s = ((grind 15).run s).bind fun p ↦
      ((sampleChallenges n).run p.2).bind fun q ↦
        (readScalar.run q.2).bind fun r ↦ some (⟨.eq q.1, r.1⟩, r.2) := by
  simp only [readOod, StateT.run_bind, Option.bind_eq_bind]
  rfl

/-- What `read_ood` may change: the output, the `TState`, its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdx) eqClaimBytes q ∨
    NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 readOodStack) readOodStack q

variable [Host] {k : Nat}

/-- **`read_ood`'s contract.** -/
theorem readOod_spec (hp : Placed code k)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hlog, hout, hgot⟩
  rw [stack_eq] at hst hrc htok hout hgot
  set t := reg m0 .rdi with htdef
  set o := reg m0 .rdx with hodef
  set L := (reg m0 .rsi).toNat with hLdef
  set fb := stackBelow m0 64 with hfb
  have hL : L ≤ 30 := hlog
  have hn : 688 ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfnw : NativeRustcVm.NoWrap fb (64 + 8) := frame_noWrap hst (by decide)
  have hfnw64 : NativeRustcVm.NoWrap fb 64 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  have hsnw := noWrap_stackBelow hst
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  obtain ⟨hOm, hOn, hOT, hOA, hOS, hOR⟩ := hout
  rw [show eqClaimBytes = 504 from rfl] at hOm hOn hOT hOA hOS hOR
  have hON : o.toNat + 504 ≤ 2 ^ 64 := hOn
  have hTF : NativeRustcVm.Apart t 760 fb (64 + 8) := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb (64 + 8) :=
    apart_frame htok.2.1 hn (by decide)
  have hOF : NativeRustcVm.Apart o 504 fb (64 + 8) := apart_frame hOS hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb (64 + 8) q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hRO : ∀ q, NativeRustcVm.InRange o 504 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hOT hOn hTn hq h,
      fun h ↦ not_inRange_of_apart hOA hOn hAn hq h⟩
  have hOSt : ∀ q, NativeRustcVm.InRange o 504 q →
      ¬ NativeRustcVm.InRange (stackBelow m0 688) (688 + 8) q :=
    fun q hq h ↦ not_inRange_of_apart hOS hOn hsnw hq h
  have hOFr : ∀ q, NativeRustcVm.InRange o 504 q → ¬ NativeRustcVm.InRange fb (64 + 8) q :=
    fun q hq h ↦ not_inRange_of_apart hOF hOn hfnw hq h
  have hrcOut : ∀ q, Out m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq | hq) h
    · exact not_inRange_of_apart hOR hOn hrc.2.1 hq h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · rw [stack_eq] at hq
      exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  have hfS : ∀ q, NativeRustcVm.InRange fb 64 q → Out m0 q := fun q hq ↦
    .inr (.inr (by rw [stack_eq]; exact inRange_frame_stack h8 hn (by decide) hq))
  have hcalOut : ∀ {d : MachineData} {n' : Nat}, rspOf d = fb → 64 + n' ≤ 688 →
      ∀ q, NativeRustcVm.InRange (stackBelow d n') n' q →
        Out m0 q ∧ ¬ NativeRustcVm.InRange fb (64 + 8) q ∧ ¬ NativeRustcVm.InRange o 504 q :=
    fun hsp hn' q hq ↦ by
      obtain ⟨h1, h2⟩ := inRange_callee hsp h8 hn hn' hq
      exact ⟨.inr (.inr (by rw [stack_eq]; exact h1)), h2,
        fun ho ↦ hOSt q ho (inRange_mono h1 (by omega))⟩
  have hfr : ∀ {d : MachineData} {o' : Nat} {ret : BitVec 64}, Frame m0 64 slots o' d →
      (frameEnv m0 d 64 [] (fun _ ↦ 0) ret).WF := fun hf ↦
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩ (by simp)
      (List.pairwise_singleton _ _)
  have hfrO : ∀ {d : MachineData} {o' : Nat} {ret : BitVec 64}, Frame m0 64 slots o' d →
      (frameEnv m0 d 64 [(o, 504)] (fun _ ↦ 0) ret).WF := fun hf ↦
    frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.kept, hfnw⟩
      (fun x hx ↦ by
        obtain rfl := List.mem_singleton.mp hx
        exact ⟨Mapped.keeps hOm hf.kept, hOn⟩)
      (List.pairwise_pair.mpr (Apart.symm' hOF))
  have hsp_of : ∀ {d : MachineData}, Frame m0 64 slots 0 d → rspOf d = fb :=
    fun hf ↦ by rw [hf.sp, off_zero]
  have hgotBytes : ∀ {d : MachineData},
      NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0) →
      ∀ l ∈ ["memcpy"], ∀ i < 8,
        d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
          m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
    intro d hs
    exact got_keep hgot hst (writes := [(o, eqClaimBytes), (t, tstateBytes)])
      (by simp [hodef, htdef]) (by
        intro a' ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact hOn
        · exact hTn)
      (hs.mono (by intro q hq; simpa [Out, stack_eq, hodef, htdef, or_assoc] using hq))
  -- `b0`: the prologue, `call grind`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 64) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 64 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.ReadOod.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.ReadOod.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx7, hx6, hx3, hx14, hx15⟩ := ok_b0
  have hf1 : Frame m0 64 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 64) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) :=
    fun q hq ↦ hs1 q fun h ↦ hq (hfS q h)
  have hsp1 := hsp_of hf1
  have hX7 : reg st1.data .rdi = t := hm1.regs .rdi _ hx7
  have hX6 : reg st1.data .rsi = BitVec.ofNat 64 15 := hm1.regs .rsi _ hx6
  have hX3 : reg st1.data .rbx = o := hm1.regs .rbx _ hx3
  have hX14 : reg st1.data .r14 = t := hm1.regs .r14 _ hx14
  have hX15 : reg st1.data .r15 = reg m0 .rsi := hm1.regs .r15 _ hx15
  -- `grind`.
  have hpg : GrindPre a s st1.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ (reg st1.data .rdi) a s ∧
      TStateOk _ (reg st1.data .rdi) a _ ∧ (reg st1.data .rsi).toNat % 2 ^ 32 < 64 ∧ _
    rw [hX7, hX6]
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by decide),
      RcAt.callee hrc (rc_keep hso1 hrcOut) hsp1 hn (by decide),
      hts.frame hf1.kept (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs1,
      TStateOk.callee htok hsp1 hn (by decide), by decide, ?_⟩
    apply got_callee hgot (hgotBytes hso1) hsp1 hn (by decide)
    intro l hl a' ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;>
      exact (hgot.1 l hl).2.2.2 _ (by simp [htdef])
  have hgb : grindBits st1.data = 15 := by
    show (reg st1.data .rsi).toNat % 2 ^ 32 = 15; rw [hX6]; rfl
  refine call_then hpc1 (hgr a s) hpg fun st2 hpc2 hrsp2 ⟨hok2, hnext2, hs2, hsv2⟩ => ?_
  rw [hgb] at hok2 hnext2
  rw [hX7] at hnext2 hs2
  have hf2 : Frame m0 64 slots 8 st2.data :=
    Frame.call hf1 hsv2 hrsp2 hs2 (fun q hq h ↦ by
      rcases hq with hq | hq
      · exact not_inRange_of_apart hTF hTn hfnw hq h
      · exact (hcalOut hsp1 (by decide) q hq).2.1 h) hfnw slots_le
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs2 q fun h ↦ h.elim (fun h' ↦ hq (.inr (.inl h'))) fun h' ↦
      hq (hcalOut hsp1 (by decide) q h').1]
    exact hso1 q hq
  have hY3 : reg st2.data .rbx = o := (hsv2.1 .rbx rfl).trans hX3
  have hY14 : reg st2.data .r14 = t := (hsv2.1 .r14 rfl).trans hX14
  have hY15 : reg st2.data .r15 = reg m0 .rsi := (hsv2.1 .r15 rfl).trans hX15
  -- `b1`: `stack_log ≤ 30`.
  have hm2 : Match (frameEnv m0 st2.data 64 [(o, 504)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b3Offset + b3.length)).toBitVec) outS st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl hY3, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 (hfrO hf2) nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b0_next)) hm2 fun st3 hm3 hpc3 => ?_
  have hc1 : bigSym.eval (frameEnv m0 st2.data 64 [(o, 504)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b3Offset + b3.length)).toBitVec) = false := by
    simp only [bigSym, SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .r15 = reg m0 .rsi from hY15]
    exact big_false _ hL
  simp only [PcOk] at hpc3
  rw [hc1] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: the grind's result.
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 (hfrO hf2) nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b1_next)) hm3 fun st4 hm4 hpc4 => ?_
  have hc2 : failSym.eval (frameEnv m0 st2.data 64 [(o, 504)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b3Offset + b3.length)).toBitVec) = !((grind 15).run s).isSome := by
    simp only [failSym, SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [tag8_eval, show (st2.data.regs.get64 .rax).toNat % 256 = _ from hok2]
    cases ((grind 15).run s).isSome <;> rfl
  simp only [PcOk] at hpc4
  rw [hc2] at hpc4
  cases hr1 : (grind 15).run s with
  | none =>
    rw [hr1] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    have hnone : (readOod L).run s = none := by rw [run_eq, hr1]; rfl
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8b (hfrO hf2) nofun
      (hpc4.trans (hp.label NativeRustcVmX64.Vm.ReadOod.label_5_at)) hm4 fun st5 hm5 hpc5 => ?_
    obtain ⟨hepi, hmem5, hrax5⟩ := end_b8b
    obtain ⟨hsv5, hrsp5⟩ := Frame.epilogue hf2 (hfrO hf2) hm5 hepi
    have hd5 : st5.data.dmem = st2.data.dmem := hm5.dmem_eq (hfrO hf2) hmem5
    simp only [PcOk] at hpc5
    refine .done _ ⟨by rw [hpc5]; exact hf2.load_ret hst (by decide), hrsp5, ?_, ?_, ?_, hsv5⟩
    · show (reg st5.data .rax).toNat % 256 = (okWord ((readOod L).run s).isSome).toNat
      rw [hnone, show reg st5.data .rax = _ from hm5.regs .rax _ hrax5]; rfl
    · intro c s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd5]; exact hso2 q hq
  | some p =>
  obtain ⟨u1, s1⟩ := p
  rw [hr1] at hpc4
  simp (config := { decide := true }) only [Option.isSome_some, ↓reduceIte] at hpc4
  have hts2 : TStateAt st2.data.dmem t a s1 := hnext2 u1 s1 hr1
  -- `b3`: the length, `call sample_challenges`.
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 (hfrO hf2) (fun _ _ ↦ rfl)
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b2_next)) hm4 fun st5 hm5 hpc5 => ?_
  obtain ⟨hmid5, hws5, hw5, hx7₅, hx6₅, hx2₅, hx3₅, hx14₅⟩ := ok_b3
  have hf5 : Frame m0 64 slots 0 st5.data := Frame.of_block hf2 (hfrO hf2) hm5 hmid5 slots_le
  have hsp5 := hsp_of hf5
  have hs5 : NativeRustcVm.SameOutside st2.data.dmem st5.data.dmem
      (fun q ↦ NativeRustcVm.InRange fb 8 q ∨ NativeRustcVm.InRange o 8 q) := by
    have h := sameOutside_W2 (hfrO hf2) hm5 (r := 0) (r' := 1) rfl rfl
      (W := fun j ↦ j < 8) (W' := fun j ↦ j < 8) fun w hw ↦ by
        rcases hws5 w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, by omega, fun j _ hj ↦ by omega⟩
        · exact .inr ⟨h1, by omega, fun j _ hj ↦ by omega⟩
    refine NativeRustcVm.Transcript.SameOutside.mono h fun q hq ↦ ?_
    rcases hq with ⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩
    · exact .inl (inRange_off_self hj (by omega))
    · exact .inr (inRange_off_self hj (by omega))
  have h8F : ∀ q, NativeRustcVm.InRange fb 8 q → NativeRustcVm.InRange fb 64 q :=
    fun q h ↦ inRange_mono h (by omega)
  have h8O : ∀ q, NativeRustcVm.InRange o 8 q → NativeRustcVm.InRange o 504 q :=
    fun q h ↦ inRange_mono h (by omega)
  have hso5 : NativeRustcVm.SameOutside m0.dmem st5.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs5 q fun h ↦ h.elim (fun h' ↦ hq (hfS q (h8F q h'))) fun h' ↦ hq (.inl (h8O q h'))]
    exact hso2 q hq
  have hlen5 : NativeRustcVm.WordAt st5.data.dmem o L.toUInt64 := by
    have h := wordAt_write hm5 (r := 1) (o := 0) rfl (by decide) hw5
    rw [off_zero] at h
    refine (congrArg (NativeRustcVm.WordAt st5.data.dmem o) ?_).mp h
    apply UInt64.toBitVec_inj.mp
    show st2.data.regs.get64 .r15 = BitVec.ofNat 64 L
    rw [show st2.data.regs.get64 .r15 = reg m0 .rsi from hY15]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hX7₅ : reg st5.data .rdi = t := (hm5.regs .rdi _ hx7₅).trans hY14
  have hX6₅ : reg st5.data .rsi = off o 8 := (hm5.regs .rsi _ hx6₅).trans (eval_ptr_off rfl 8)
  have hX2₅ : (reg st5.data .rdx).toNat = L := by
    rw [show reg st5.data .rdx = _ from hm5.regs .rdx _ hx2₅]
    show (st2.data.regs.get64 .r15).toNat = L
    rw [show st2.data.regs.get64 .r15 = reg m0 .rsi from hY15]
  have hX3₅ : reg st5.data .rbx = o := (hm5.regs .rbx _ hx3₅).trans (eval_ptr rfl)
  have hX14₅ : reg st5.data .r14 = t := (hm5.regs .r14 _ hx14₅).trans hY14
  have hts5 : TStateAt st5.data.dmem t a s1 :=
    hts2.frame (hm5.kept (hfrO hf2)) (fun q hq ↦ hq.elim
      (fun h ↦ hRF q (inRange_mono h (by omega))) fun h ↦ hRO q (h8O q h)) hs5
  have hoff8 : (off o 8).toNat = o.toNat + 8 := toNat_off (by omega)
  have hpsc : SampleChallengesPre a s1 st5.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ (reg st5.data .rdi) a s1 ∧
      TStateOk _ (reg st5.data .rdi) a _ ∧
      OutOk _ (reg st5.data .rdi) a (reg st5.data .rsi) (16 * (reg st5.data .rdx).toNat) _ ∧ _
    rw [hX7₅, hX6₅, hX2₅]
    have hOS5 := apart_callee hOS hsp5 hn (n' := sampleChallengesStack) (by decide)
    refine ⟨stackOk_callee hst hf5.kept hsp5 (by decide),
      RcAt.callee hrc (rc_keep hso5 hrcOut) hsp5 hn (by decide), hts5,
      TStateOk.callee htok hsp5 hn (by decide), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      rw [off_add]
      exact hf5.kept _ (hOm _ (by omega))
    · show (off o 8).toNat + _ ≤ _; rw [hoff8]; omega
    · exact NativeRustcVm.Apart.mono hOT (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOA (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOS5 (by omega) (by omega) le_rfl le_rfl
    · exact NativeRustcVm.Apart.mono hOR (by omega) (by omega) le_rfl le_rfl
    · apply got_callee hgot (hgotBytes hso5) hsp5 hn (by decide)
      intro l hl a' ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact (hgot.1 l hl).2.2.2 _ (by simp [htdef])
      · exact (hgot.1 l hl).2.2.2 _ (by simp)
      · exact Transcript.Apart.sub ((hgot.1 l hl).2.2.2 (o, eqClaimBytes) (by simp [hodef]))
          (by dsimp only; rw [hoff8]; omega)
          (by rw [hoff8]; change _ ≤ o.toNat + 504; omega)
      · exact (hgot.1 l hl).2.2.2 _ (by simp)
  refine call_then hpc5 (hsc a s1) hpsc
    fun st6 hpc6 hrsp6 ⟨⟨xs, s2, hr2, hxs, hts6⟩, hs6, hsv6⟩ => ?_
  rw [hX7₅, hX6₅, hX2₅] at hs6
  rw [hX7₅] at hts6
  rw [hX6₅] at hxs
  rw [hX2₅] at hr2
  have hxsz : xs.size = L := sampleChallenges_size hr2
  have hin8 : ∀ q, NativeRustcVm.InRange (off o 8) (16 * L) q → NativeRustcVm.InRange o 504 q :=
    fun q h ↦ inRange_of_off hOn (by omega) h
  have hf6 : Frame m0 64 slots 8 st6.data := by
    refine Frame.call hf5 hsv6 hrsp6 hs6 (fun q hq h ↦ ?_) hfnw slots_le
    rcases hq with hq | hq | hq
    · exact hOFr q (hin8 q hq) h
    · exact not_inRange_of_apart hTF hTn hfnw hq h
    · exact (hcalOut hsp5 (by decide) q hq).2.1 h
  have hso6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs6 q fun h ↦ h.elim (fun h' ↦ hq (.inl (hin8 q h'))) fun h' ↦ h'.elim
      (fun h'' ↦ hq (.inr (.inl h''))) fun h'' ↦ hq (hcalOut hsp5 (by decide) q h'').1]
    exact hso5 q hq
  have hlen6 : NativeRustcVm.WordAt st6.data.dmem o L.toUInt64 := by
    refine NativeRustcVm.BytesAt.of_sameOutside hlen5 hs6 fun i hi ↦ ?_
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    have hq : NativeRustcVm.InRange o 504 (o + BitVec.ofNat 64 i) :=
      inRange_off_self (b := o) (j := i) (by omega) (by omega)
    rintro (h | h | h)
    · have h' : NativeRustcVm.InRange (off o 8) (16 * L) (o + BitVec.ofNat 64 i) := h
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hoff8]; omega), hoff8,
        show (o + BitVec.ofNat 64 i).toNat = o.toNat + i from toNat_off (b := o) (j := i)
          (by omega)] at h'
      omega
    · exact (hRO _ hq).1 h
    · exact (hcalOut hsp5 (by decide) _ h).2.2 hq
  have hY3₆ : reg st6.data .rbx = o := (hsv6.1 .rbx rfl).trans hX3₅
  have hY14₆ : reg st6.data .r14 = t := (hsv6.1 .r14 rfl).trans hX14₅
  -- `b4`: `call read_scalar` into the frame.
  have hm6 : Match (frameEnv m0 st6.data 64 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.ReadOod.b4Offset + b4.length)).toBitVec) callS st6.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf6.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 (hfr hf6) (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b3_next)) hm6 fun st7 hm7 hpc7 => ?_
  obtain ⟨hmid7, hws7, hx7₇, hx6₇, hx3₇, hx14₇⟩ := ok_b4
  have hf7 : Frame m0 64 slots 0 st7.data := Frame.of_block hf6 (hfr hf6) hm7 hmid7 slots_le
  have hsp7 := hsp_of hf7
  have hs7 : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem (NativeRustcVm.InRange fb 8) :=
    sameOutside_low (hfr hf6) hm7 (r := 0) rfl (by decide) hws7
  have hso7 : NativeRustcVm.SameOutside m0.dmem st7.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs7 q fun h ↦ hq (hfS q (h8F q h))]; exact hso6 q hq
  have hX7₇ : reg st7.data .rdi = off fb 16 := (hm7.regs .rdi _ hx7₇).trans (eval_ptr0 16)
  have hX6₇ : reg st7.data .rsi = t := (hm7.regs .rsi _ hx6₇).trans hY14₆
  have hX3₇ : reg st7.data .rbx = o := (hm7.regs .rbx _ hx3₇).trans hY3₆
  have hts7 : TStateAt st7.data.dmem t a s2 :=
    hts6.frame (hm7.kept (hfr hf6)) (fun q hq ↦ hRF q (inRange_mono hq (by omega))) hs7
  have hprs : ReadScalarPre a s2 st7.data := by
    show StackOk _ _ ∧ RcAt _ _ ∧ TStateAt _ (reg st7.data .rsi) a s2 ∧
      TStateOk _ (reg st7.data .rsi) a _ ∧ OutOk _ (reg st7.data .rsi) a (reg st7.data .rdi) 24 _ ∧ _
    rw [hX7₇, hX6₇]
    refine ⟨stackOk_callee hst hf7.kept hsp7 (by decide),
      RcAt.callee hrc (rc_keep hso7 hrcOut) hsp7 hn (by decide), hts7,
      TStateOk.callee htok hsp7 hn (by decide),
      OutOk.frame hst (by decide) hsp7 hf7.kept (by decide) (by decide) htok hrc, ?_⟩
    apply got_callee hgot (hgotBytes hso7) hsp7 hn (by decide)
    intro l hl a' ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact (hgot.1 l hl).2.2.2 _ (by simp [htdef])
    · exact (hgot.1 l hl).2.2.2 _ (by simp)
    · exact got_apart_frame hgot hst hl (by decide) (by dsimp only; decide)
    · exact (hgot.1 l hl).2.2.2 _ (by simp)
  refine call_then hpc7 (hrs a s2) hprs fun st8 hpc8 hrsp8 ⟨hopt, hnext8, hs8, hsv8⟩ => ?_
  rw [hX7₇] at hopt hs8
  rw [hX6₇] at hnext8 hs8
  have hslot : ∀ j, 40 ≤ j → j < 64 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 16) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow st7.data readScalarStack) readScalarStack q) := by
    rintro j hj1 hj2 q rfl (h | h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact not_inRange_of_apart hTF hTn hfnw h (inRange_off_self hj2 (by omega))
    · exact (hcalOut hsp7 (by decide) _ h).2.1 (inRange_off_self hj2 (by omega))
  have hf8 : Frame m0 64 slots 8 st8.data :=
    Frame.call_slots hf7 hsv8 hrsp8 hs8
      (fun p hp i hi ↦ hslot _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hslot _ (by omega) (by omega) _ rfl)
  have hR8 : ∀ q, (NativeRustcVm.InRange (off fb 16) 24 q ∨ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (stackBelow st7.data readScalarStack) readScalarStack q) →
      Out m0 q ∧ ¬ NativeRustcVm.InRange o 504 q := by
    rintro q (h | h | h)
    · have hf := inRange_of_off hfnw64 (by decide) h
      exact ⟨hfS q hf, fun ho ↦ hOFr q ho (inRange_mono hf (by omega))⟩
    · exact ⟨.inr (.inl h), fun ho ↦ (hRO q ho).1 h⟩
    · exact ⟨(hcalOut hsp7 (by decide) q h).1, (hcalOut hsp7 (by decide) q h).2.2⟩
  have hso8 : NativeRustcVm.SameOutside m0.dmem st8.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs8 q fun h ↦ hq (hR8 q h).1]; exact hso7 q hq
  have hkO8 : ∀ {p : BitVec 64} {bs : List UInt8}, NativeRustcVm.BytesAt st6.data.dmem p bs →
      (∀ i < bs.length, NativeRustcVm.InRange o 504 (p + BitVec.ofNat 64 i)) →
      NativeRustcVm.BytesAt st8.data.dmem p bs := fun h hin ↦
    NativeRustcVm.BytesAt.of_sameOutside
      (NativeRustcVm.BytesAt.of_sameOutside h hs7 fun i hi h' ↦
        hOFr _ (hin i hi) (inRange_mono h' (by omega)))
      hs8 fun i hi h' ↦ (hR8 _ h').2 (hin i hi)
  have hewsLen : (xs.toList.flatMap NativeRustcVm.ewBytes).length = 16 * L := by
    rw [NativeRustcVm.length_ewsBytes]; simp [hxsz]
  have hlen8 : NativeRustcVm.WordAt st8.data.dmem o L.toUInt64 :=
    hkO8 hlen6 fun i hi ↦ inRange_off_self (b := o) (j := i)
      (by simp [NativeRustcVm.length_wordBytes] at hi; omega) (by omega)
  have hews8 : NativeRustcVm.EWsAt st8.data.dmem (off o 8) xs.toList :=
    hkO8 hxs fun i hi ↦ by
      rw [hewsLen] at hi
      rw [off_add]
      exact inRange_off_self (by omega) (by omega)
  have hY3₈ : reg st8.data .rbx = o := (hsv8.1 .rbx rfl).trans hX3₇
  -- `b5`: the tag.
  have hm8 : Match (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0) outS st8.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf8.rsp_eval, known_ptr rfl hY3₈, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 (hfrO hf8) nofun
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b4_next)) hm8 fun st9 hm9 hpc9 => ?_
  simp only [PcOk] at hpc9
  cases hr3 : readScalar.run s2 with
  | none =>
    rw [hr3] at hopt
    have h0 : NativeRustcVm.WordAt st8.data.dmem (off fb 16) 0 := hopt
    have hl : (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0).load 0 16 4 =
        BitVec.ofNat 64 (0 : UInt64).toNat := load4_of_tag (Or.inl rfl) h0
    have hc : (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not.eval
        (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0) = true := by
      simp only [SBool.eval, Sym.eval, hl]; decide
    rw [hc] at hpc9
    simp (config := { decide := true }) only [↓reduceIte] at hpc9
    have hnone : (readOod L).run s = none := by
      rw [run_eq, hr1]; show ((sampleChallenges L).run s1).bind _ = none
      rw [hr2]; show (readScalar.run s2).bind _ = none
      rw [hr3]; rfl
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 (hfrO hf8) nofun
      (hpc9.trans (hp.label NativeRustcVmX64.Vm.ReadOod.label_4_at)) hm9 fun st10 hm10 hpc10 => ?_
    simp only [PcOk] at hpc10
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8c (hfrO hf8) nofun
      (hpc10.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b7_next)) hm10 fun st11 hm11 hpc11 => ?_
    obtain ⟨hepi, hmem11, hrax11⟩ := end_b8c
    obtain ⟨hsv11, hrsp11⟩ := Frame.epilogue hf8 (hfrO hf8) hm11 hepi
    have hd11 : st11.data.dmem = st8.data.dmem := hm11.dmem_eq (hfrO hf8) hmem11
    simp only [PcOk] at hpc11
    refine .done _ ⟨by rw [hpc11]; exact hf8.load_ret hst (by decide), hrsp11, ?_, ?_, ?_, hsv11⟩
    · show (reg st11.data .rax).toNat % 256 = (okWord ((readOod L).run s).isSome).toNat
      rw [hnone, show reg st11.data .rax = _ from hm11.regs .rax _ hrax11]; rfl
    · intro c s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd11]; exact hso8 q hq
  | some p =>
  obtain ⟨v, s3⟩ := p
  rw [hr3] at hopt
  obtain ⟨ht1, hel⟩ := (hopt : OptEWAt st8.data.dmem (off fb 16) (some v))
  rw [ewAt_iff, off_off, off_off] at hel
  have hl : (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0).load 0 16 4 =
      BitVec.ofNat 64 (1 : UInt64).toNat := load4_of_tag (Or.inr rfl) ht1
  have hc : (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not.eval
      (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, Sym.eval, hl]; decide
  rw [hc] at hpc9
  simp (config := { decide := true }) only [↓reduceIte] at hpc9
  have hsome : (readOod L).run s = some (⟨.eq xs, v⟩, s3) := by
    rw [run_eq, hr1]; show ((sampleChallenges L).run s1).bind _ = _
    rw [hr2]; show (readScalar.run s2).bind _ = _
    rw [hr3]; rfl
  -- `b6`: the value stored, AL = `1`; `b8`.
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 (hfrO hf8) nofun
    (hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.ReadOod.b5_next)) hm9 fun st10 hm10 hpc10 => ?_
  simp only [PcOk] at hpc10
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8d (hfrO hf8) nofun
    (hpc10.trans (hp.label NativeRustcVmX64.Vm.ReadOod.label_5_at)) hm10 fun st11 hm11 hpc11 => ?_
  obtain ⟨hepi, hrax11, hw488, hw496, hws11⟩ := end_b8d
  obtain ⟨hsv11, hrsp11⟩ := Frame.epilogue hf8 (hfrO hf8) hm11 hepi
  have hs11 : NativeRustcVm.SameOutside st8.data.dmem st11.data.dmem
      (fun q ↦ Touch o 504 (fun j ↦ 488 ≤ j ∧ j < 504) q ∨ False) :=
    NativeRustcVm.Transcript.SameOutside.mono
      (sameOutside_touch (hfrO hf8) hm11 (r := 1) rfl le_rfl hws11) fun _ h ↦ .inl h
  have hk11 : ∀ {j : Nat} {bs : List UInt8}, j + bs.length ≤ 488 →
      NativeRustcVm.BytesAt st8.data.dmem (off o j) bs →
      NativeRustcVm.BytesAt st11.data.dmem (off o j) bs := fun hle h ↦
    bytesAt_keep hOn (fun _ h ↦ h.elim) hs11 (by omega) (fun i hi hW ↦ by omega) h
  have hl24 : (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0).load 0 24 8 = v.c0.toBitVec :=
    load_ofMachine (o := 24) rfl hel.1
  have hl32 : (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0).load 0 32 8 = v.c1.toBitVec :=
    load_ofMachine (o := 32) rfl hel.2
  have w488 := wordAt_write hm11 (r := 1) (o := 488) rfl (by decide) hw488
  have w496 := wordAt_write hm11 (r := 1) (o := 496) rfl (by decide) hw496
  rw [show UInt64.ofBitVec ((Sym.load 0 24 8).eval
    (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0)) = v.c0 from
      UInt64.toBitVec_inj.mp hl24] at w488
  rw [show UInt64.ofBitVec ((Sym.load 0 32 8).eval
    (frameEnv m0 st8.data 64 [(o, 504)] (fun _ ↦ 0) 0)) = v.c1 from
      UInt64.toBitVec_inj.mp hl32] at w496
  simp only [PcOk] at hpc11
  refine .done _ ⟨by rw [hpc11]; exact hf8.load_ret hst (by decide), hrsp11, ?_, ?_, ?_, hsv11⟩
  · show (reg st11.data .rax).toNat % 256 = (okWord ((readOod L).run s).isSome).toNat
    rw [hsome, show reg st11.data .rax = _ from hm11.regs .rax _ hrax11]
    exact merge_one_mod _
  · intro c s' h
    rw [hsome] at h
    cases h
    have hxl : xs.toList.length = L := by simp [hxsz]
    refine ⟨⟨xs, rfl, ⟨by rw [hxl]; exact hL, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hxl]
      have := hk11 (j := 0) (bs := NativeRustcVm.wordBytes L.toUInt64)
        (by rw [NativeRustcVm.length_wordBytes]; omega) (by rw [off_zero]; exact hlen8)
      rwa [off_zero] at this
    · exact hk11 (j := 8) (by rw [hewsLen]; omega) hews8
    · exact ewAt_iff.mpr ⟨w488, by rw [off_off]; exact w496⟩
    · refine (hnext8 v s3 hr3).frame (hm11.kept (hfrO hf8)) (fun q hq ↦ ?_) hs11
      rcases hq with hq | hq
      · exact hRO q (inRange_of_touch hOn hq)
      · exact hq.elim
  · intro q hq
    rw [hs11 q fun h ↦ h.elim (fun h' ↦ hq (.inl (inRange_of_touch hOn h'))) id]
    exact hso8 q hq

end

end NativeRustcVmX64.Layout.ReadOod
