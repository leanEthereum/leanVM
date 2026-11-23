module

public import NativeRustcVmX64.Sumcheck.QueryOpenings.Open
public import NativeRustcVmX64.Transcript.Arith
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names

/-!
# `TState::query_openings` on x86-64

**`queryOpenings_spec`**: `queryOpenings i positions`'s rows at the output, the `TState` at the next
phase, given `Decoded::phase`'s and `open_phase`'s contracts. `b0` pushes RBP to RBX, reserves the
frame and tests `i < count` (and `count < 9`, always: `TStateAt`), else `b6` (`None`); `b1` calls
`Decoded::phase` with the phase index; `b2` tests its address (`0`, no such phase: `b6`); from
`b3`, `open_spec`.
-/

namespace NativeRustcVmX64.Sumcheck.QueryOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateQueryOpenings
open NativeRustcVm.Transcript NativeVm NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

public section

/-- The model without root `i`: `None`. -/
theorem run_no_root {s : TState} {i : Nat} {Q : Array UInt64} (hi : s.roots.size ≤ i) :
    (queryOpenings i Q).run s = none := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_none hi]

/-- The model without phase `s.phase`: `None`. -/
theorem run_no_phase {s : TState} {i : Nat} {Q : Array UInt64} (hp : s.openings.size ≤ s.phase) :
    (queryOpenings i Q).run s = none := by
  rw [NativeVm.Equiv.queryOpenings_run, Array.getElem?_eq_none hp]
  rcases s.roots[i]? with _ | r <;> rfl

section
variable [Labels]

/-- `b0`'s test: `i ≥ count`, the count below `9`. -/
theorem c0_eval (env : Env) (b : Bool) (h1 : (env.regs .rdx).ult (env.load 1 752 8) = b)
    (h2 : (env.load 1 752 8).ult (BitVec.ofNat 64 9) = true) : c0.eval env = !b := by
  cases b <;>
    simp only [c0, setae, cntSym, SBool.eval, Sym.eval, CmpOp.apply, low_W64, h1, h2,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, BinOp.apply,
      low8_replaceLow, low_ext] <;>
    decide

/-- `b2`'s test: RAX zero. -/
theorem c2_eval (env : Env) : c2.eval env = (env.regs .rax == 0#64) := by
  simp only [c2, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self]

end

variable [Host] {k : Nat}

/-- **`TState::query_openings` meets its contract.** -/
theorem queryOpenings_spec (hp : Placed code k)
    (hph : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings)
      (PhasePost a openings))
    (hop : ∀ P R Q, Spec (Labels.label NativeRustcVmX64.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q) (OpenPhasePost P R Q))
    (a : DecArea) (s : TState) (Q : Array UInt64) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q) (QueryOpeningsPost a s Q) := by
  intro m0 hpre
  have c := ctx hpre
  have hst := hpre.1
  have hts0 := hpre.2.2.1
  set t := reg m0 .rsi with htdef
  set i := (reg m0 .rdx).toNat with hidef
  set fb := stackBelow m0 96 with hfbdef
  have hn : queryOpeningsStack ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hN : queryOpeningsStack = 1280 := rfl
  have hfnw : NativeRustcVm.NoWrap fb (96 + 8) := frame_noWrap hst (by decide)
  have hfb : fb.toNat = (rspOf m0).toNat - 96 := stackBelow_toNat (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, hTA⟩ := hts0.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have hTF : NativeRustcVm.Apart t 760 fb (96 + 8) := apart_frame c.tok.1 hn (by decide)
  set nr := s.roots.size with hnrdef
  have hnr8 : nr ≤ 8 := hts0.roots_le
  have hnr64 : nr.toUInt64.toBitVec.toNat = nr := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hphl : s.phase ≤ 8 := Nat.le_trans hts0.phase_le
    (by have := hts0.decoded.phases_le; simpa [LeanVM.Protocol.Compile.wireMaxPhases] using this)
  have hph64 : s.phase.toUInt64.toBitVec.toNat = s.phase := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  -- `b0`, `b1`: the prologue, the tests, `call phase`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 96) (rest := [(t, 760)]) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b1Offset + b1.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hTm, hTn⟩)
    (List.pairwise_pair.mpr (Apart.symm' hTF))
  have hm0 : Match (frameEnv m0 m0 96 [(t, 760)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b1Offset + b1.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  have hcnt : (frameEnv m0 m0 96 [(t, 760)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b1Offset + b1.length)).toBitVec).load 1 752 8 = nr.toUInt64.toBitVec :=
    load_ofMachine (o := 752) rfl hts0.n_roots
  have hphase : (frameEnv m0 m0 96 [(t, 760)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b1Offset + b1.length)).toBitVec).load 1 360 8 = s.phase.toUInt64.toBitVec :=
    load_ofMachine (o := 360) rfl hts0.phase
  unfold NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.TStateQueryOpenings.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro1, hws1, hr14₁⟩ := ok_b0
  have hc0 : c0.eval (frameEnv m0 m0 96 [(t, 760)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.TStateQueryOpenings.b1Offset + b1.length)).toBitVec) = !decide (i < nr) := by
    refine c0_eval _ _ ?_ ?_
    · rw [hcnt, Env.ofMachine_regs]
      simp only [BitVec.ult, hnr64]
      rfl
    · rw [hcnt]
      simp only [BitVec.ult, hnr64, BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
  simp only [PcOk, hc0] at hpc1
  by_cases hi : i < nr
  swap
  · simp only [hi, decide_false, Bool.not_false, ↓reduceIte] at hpc1
    have hf1 : Frame m0 96 slots 8 st1.data :=
      Frame.of_prologue Frame.entry hwf0 hm1 hpro1 slots_le slots_cs
    have hs1 := sameOutside_low hwf0 hm1 (r := 0) rfl (hi := 96) (by omega) hws1
    exact finish_fail hp hpre (run_no_root (by omega)) (hpc1.trans (hp.label NativeRustcVmX64.Vm.TStateQueryOpenings.label_4_at)) hf1
      (hm1.regs .r14 _ hr14₁)
      (NativeRustcVm.SameOutside.mono hs1 fun _ hq ↦ Or.inr (Or.inr (frame_stk hst hq)))
  simp only [hi, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf0 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b0_next)) hm1 fun st2 hm2 hpc2 => ?_
  obtain ⟨hpro2, hws2, hdi2, hsi2, hr15₂, hbx2, hbp2, hr12₂, hr13₂, hr14₂⟩ := ok_b1
  have hf2 : Frame m0 96 slots 0 st2.data :=
    Frame.of_prologue Frame.entry hwf0 hm2 hpro2 slots_le slots_cs
  have hsp2 : rspOf st2.data = fb := by rw [hf2.sp, off_zero]
  have hs2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Stk m0) :=
    NativeRustcVm.SameOutside.mono (sameOutside_low hwf0 hm2 (r := 0) rfl (hi := 96) (by omega)
      hws2) fun _ hq ↦ frame_stk hst hq
  have hts2 : TStateAt st2.data.dmem t a s := tstate_stk hpre hf2.kept hs2
  have hdi : reg st2.data .rdi = off t 328 := (hm2.regs .rdi _ hdi2).trans (by
    show t + BitVec.ofInt 64 328 = _
    rfl)
  have hsi : (reg st2.data .rsi).toNat = s.phase := by
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ hsi2]
    exact (congrArg BitVec.toNat hphase).trans hph64
  have h15 : reg st2.data .r15 = s.phase.toUInt64.toBitVec := (hm2.regs .r15 _ hr15₂).trans hphase
  have hbx : reg st2.data .rbx = t := (hm2.regs .rbx _ hbx2).trans (eval_ptr rfl)
  have hbp : reg st2.data .rbp = reg m0 .rdx := hm2.regs .rbp _ hbp2
  have h12 : reg st2.data .r12 = reg m0 .r8 := hm2.regs .r12 _ hr12₂
  have h13 : reg st2.data .r13 = reg m0 .rcx := hm2.regs .r13 _ hr13₂
  have h14 : reg st2.data .r14 = reg m0 .rdi := hm2.regs .r14 _ hr14₂
  -- `Decoded::phase`.
  have hAt : At m0 96 st2.data := At.of_frame hf2 (rc_keep hs2 fun q hq ↦ c.not_rc_stack hq)
  have hP : phaseStack = 32 := rfl
  have hSp : (stackBelow st2.data phaseStack).toNat = (rspOf m0).toNat - 128 := by
    rw [stackBelow_callee hsp2 (by omega), stackBelow_toNat (by omega), hP]
  have hS0 : (stackBelow m0 queryOpeningsStack).toNat = (rspOf m0).toNat - 1280 :=
    stackBelow_toNat hn
  have htS : t.toNat + 760 ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ t.toNat := c.tok.1
  have haS : a.words.toNat + 8 * a.len ≤ (stackBelow m0 queryOpeningsStack).toNat ∨
      (stackBelow m0 queryOpeningsStack).toNat + (queryOpeningsStack + 8) ≤ a.words.toNat :=
    c.tok.2.1
  have hTA' : t.toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ t.toNat := hTA
  have hdp : (off t 328).toNat = t.toNat + 328 := toNat_off (by omega)
  have hpre3 : PhasePre a s.stream s.openings st2.data := by
    simp only [PhasePre]
    rw [hdi]
    refine ⟨c.stackOk hAt (by decide), hts2.dec, mapped_off hts2.footprint.1.1 (by
      show 328 + 24 ≤ 760; omega), ?_, ?_, ?_, hts2.footprint.2.1, ?_, hts2.decoded⟩
    · show (off t 328).toNat + 24 ≤ 2 ^ 64; omega
    · show (off t 328).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (off t 328).toNat
      omega
    · show (off t 328).toNat + 24 ≤ (stackBelow st2.data phaseStack).toNat ∨
        (stackBelow st2.data phaseStack).toNat + (phaseStack + 8) ≤ (off t 328).toNat
      rw [hSp, hP]; omega
    · show a.words.toNat + 8 * a.len ≤ (stackBelow st2.data phaseStack).toNat ∨
        (stackBelow st2.data phaseStack).toNat + (phaseStack + 8) ≤ a.words.toNat
      rw [hSp, hP]; omega
  refine call_then hpc2 (hph a s.stream s.openings) hpre3 fun st3 hpc3 hrsp3 ⟨hx0, hs3, hsv3⟩ => ?_
  rw [hsi] at hx0
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st2.data phaseStack) phaseStack q →
      Stk m0 q ∧ ¬ NativeRustcVm.InRange fb (96 + 8) q :=
    fun q hq ↦ inRange_callee hsp2 h8 hn (by decide) hq
  have hf3 : Frame m0 96 slots 8 st3.data :=
    Frame.call hf2 hsv3 hrsp3 hs3 (fun q hq ↦ (hcal q hq).2) hfnw slots_le
  have hs3' : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (Stk m0) := by
    intro q hq
    rw [← hs2 q hq]
    exact hs3 q fun h ↦ hq (hcal q h).1
  -- `b2`: the phase's address against `0`.
  have hwf3 := frame_wf (m0 := m0) (d := st3.data) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf3.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b1_next))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf3.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hka4⟩ := ok_b2
  have hf4 : Frame m0 96 slots 8 st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hs4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (Stk m0) := by
    rw [hd4]; exact hs3'
  have hk4 : ∀ r, calleeSaved r = true → r ≠ .rsp → reg st4.data r = reg st2.data r :=
    fun r hr hr' ↦ (KeepAll.regs hka4 hm4 hr').trans (hsv3.1 r hr)
  have hax : reg st4.data .rax = reg st3.data .rax := KeepAll.regs hka4 hm4 (by decide)
  simp only [PcOk, c2_eval, Env.ofMachine_regs] at hpc4
  by_cases hlt : s.phase < s.openings.size
  swap
  · simp only [hlt, ↓reduceIte] at hx0
    rw [show st3.data.regs.get64 .rax = 0#64 from hx0] at hpc4
    simp only [beq_self_eq_true, ↓reduceIte] at hpc4
    exact finish_fail hp hpre (run_no_phase (by omega)) (hpc4.trans (hp.label NativeRustcVmX64.Vm.TStateQueryOpenings.label_4_at)) hf4
      ((hk4 .r14 rfl (by decide)).trans h14)
      (NativeRustcVm.SameOutside.mono hs4 fun _ hq ↦ Or.inr (Or.inr hq))
  simp only [hlt, ↓reduceIte] at hx0
  have hplen : phaseBase a.l s.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts2.decoded.phases_le))
      hts2.decoded.len
  have hw : (a.word (phaseBase a.l s.phase)).toNat = a.words.toNat + 8 * phaseBase a.l s.phase :=
    toNat_off (by have := phaseWords_eq; omega)
  have hbase : 0 < phaseBase a.l s.phase := by unfold phaseBase; omega
  have hne : (a.word (phaseBase a.l s.phase) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    rw [hw] at this
    simp at this
    omega
  rw [show st3.data.regs.get64 .rax = a.word (phaseBase a.l s.phase) from hx0, hne] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  exact open_spec hp hop hpre hi hlt (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.TStateQueryOpenings.b2_next)) hf4 hs4
    (hax.trans hx0) ((hk4 .rbx rfl (by decide)).trans hbx)
    ((hk4 .rbp rfl (by decide)).trans hbp) ((hk4 .r12 rfl (by decide)).trans h12)
    ((hk4 .r13 rfl (by decide)).trans h13) ((hk4 .r14 rfl (by decide)).trans h14)
    ((hk4 .r15 rfl (by decide)).trans h15)

end

end NativeRustcVmX64.Sumcheck.QueryOpenings
