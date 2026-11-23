module

public import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.DuplexInput.Exec
public import NativeRustcVm.Transcript.Sponge

/-!
# `SpongeW::duplex_input` on AArch64

**`duplexInput_spec`**: the 16 rate lanes of the sponge at X0 become `duplexInput`'s, the rest of
the sponge kept. The blocks (`NativeRustcVmArm.Transcript.DuplexInput.Exec`) run from one
environment, region 0 the sponge; the path taken is the queue's count's, and every path ends with
the lanes `laneSym n i` (`finish`).
-/

namespace NativeRustcVmArm.Transcript.DuplexInput

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWDuplexInput
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm LeanVM.Parameters

public section

/-- The environment: the sponge at X0, region 0. -/
abbrev envOf (m : MachineData) : Env := Env.ofMachine m [(m.regs.X0.toBitVec, 328)]

theorem ofBitVec_ofNat (n : Nat) : UInt64.ofBitVec (BitVec.ofNat 64 n) = n.toUInt64 := rfl

/-- The queue's count, loaded. -/
theorem load_count {m : MachineData} {sp : SpongeW}
    (hsp : SpongeAt m.dmem m.regs.X0.toBitVec sp) :
    (envOf m).load 0 296 8 = BitVec.ofNat 64 sp.pending.size :=
  load_of_wordAt hsp.n_pending

/-- **A rate lane** as the paths store it. -/
theorem lane_eval [Labels] {m : MachineData} {sp : SpongeW} (hsp : SpongeAt m.dmem m.regs.X0.toBitVec sp)
    {i : Nat} (hi : i < 16) :
    UInt64.ofBitVec ((laneSym sp.pending.size i).eval (envOf m)) = sp.duplexInput[i]'(by omega) := by
  rw [duplexInput_lt sp hi]
  unfold laneSym
  by_cases h : i / 4 < sp.pending.size
  · simp only [h, dite_true, show i < 4 * sp.pending.size by omega, ite_true]
    obtain ⟨hx, htag⟩ := hsp.pending (i / 4) h
    rw [ewAt_iff] at hx
    have h0 : (envOf m).load 0 (200 + 24 * (i / 4)) 8 = sp.pending[i / 4].1.c0.toBitVec :=
      load_of_wordAt hx.1
    have h1 : (envOf m).load 0 (208 + 24 * (i / 4)) 8 = sp.pending[i / 4].1.c1.toBitVec :=
      load_of_wordAt (by
        have := hx.2
        rwa [off_off, show 200 + 24 * (i / 4) + 8 = 208 + 24 * (i / 4) by omega] at this)
    have h3 : (envOf m).load 0 (216 + 24 * (i / 4)) 8 = sp.pending[i / 4].2.toBitVec :=
      load_of_wordAt (by
        rwa [off_off, show 200 + 24 * (i / 4) + 16 = 216 + 24 * (i / 4) by omega] at htag)
    have : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases this with c | c | c | c
    · simp (config := { decide := true }) only [c, ↓reduceIte, Sym.eval, h0]
    · simp (config := { decide := true }) only [c, ↓reduceIte, Sym.eval, h1]
    · simp (config := { decide := true }) only [c, ↓reduceIte, Sym.eval]
    · simp (config := { decide := true }) only [c, ↓reduceIte, Sym.eval, h3]
  · simp only [h, dite_false, show ¬ i < 4 * sp.pending.size by omega, ite_false, Sym.eval]
    rfl

variable [Host] {k : Nat}

/-- **A path's end**: the lanes stored, the rest of the sponge kept; `ret`. -/
theorem finish {m0 : MachineData} {sp : SpongeW} (hsp : SpongeAt m0.dmem m0.regs.X0.toBitVec sp)
    (hwf : (envOf m0).WF) (hm0 : Match (envOf m0) entryS m0) {E : SState} {n : Nat}
    (hn : sp.pending.size = n) (hE : EndOk n E) {st : MachineState} (hm : Match (envOf m0) E st.data)
    {next : Int64} (hpc : PcOk (envOf m0) .ret next st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ DuplexInputPost sp m0 st'.data)
      st := by
  subst hn
  obtain ⟨hlanes, hw, h30, hkeeps⟩ := hE
  set p := m0.regs.X0.toBitVec with hpdef
  have hnw : NoWrap p 328 := hwf.noWrap 0 p 328 rfl
  have hx30 : st.data.regs.X30 = m0.regs.X30 := Match.reg_eq hm0 hm rfl h30
  have hsame : SameOutside m0.dmem st.data.dmem
      (fun q ↦ Touch p 328 (fun j ↦ 0 ≤ j ∧ j < 128) q ∨ False) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hW ↦ hq (Or.inl (touch_of_written hwf rfl (by omega) hw hW))
  have hA0 : Agree m0.dmem st.data.dmem p 328 (fun j ↦ 0 ≤ j ∧ j < 128) :=
    agree_of_sameOutside hnw (fun _ h ↦ h.elim) hsame
  have hA : Agree m0.dmem st.data.dmem p spongeBytes (· < 200) := hA0.mono fun j h ↦ by omega
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc]; simp only [retOf, hx30], ?_, ?_,
    Match.saved hm0 hm hwf rfl hkeeps⟩
  · refine hsp.with_state hA (wordsAt_iff.mpr fun i hi ↦ ?_)
    simp only [Vector.length_toList] at hi
    rw [Vector.getElem_toList]
    by_cases h16 : i < 16
    · have := wordAt_write hm (r := 0) (o := 8 * i) rfl (by omega) (hlanes i h16)
      rwa [lane_eval hsp h16] at this
    · rw [duplexInput_ge sp (by omega) hi]
      have hold := (wordsAt_iff.mp hsp.state) i (by simpa using hi)
      rw [Vector.getElem_toList] at hold
      exact wordAt_agree hA0 (by omega) (fun j hj ↦ by omega) hold
  · intro q hq
    refine hsame q fun h ↦ hq ?_
    rcases h with ⟨j, hj, -, rfl⟩ | h
    · exact inRange_off_self hj (by unfold spongeBytes; omega)
    · exact h.elim

/-- **`SpongeW::duplex_input` meets its contract.** -/
theorem duplexInput_spec (hp : Placed code k) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp) := by
  rintro m0 ⟨-, ⟨hmap, hnw, -, -⟩, hsp⟩
  have hwf : (envOf m0).WF :=
    Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (envOf m0) entryS m0 :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial
      trivial
  have hcnt := load_count hsp
  have hle : sp.pending.size ≤ 4 := hsp.pending_le
  unfold NativeRustcVmArm.Vm.SpongeWDuplexInput.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplexInput.entryOffset) NativeRustcVmArm.Vm.SpongeWDuplexInput.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm0 fun st1 hm1 hpc1 => ?_
  have hcases : sp.pending.size = 0 ∨ sp.pending.size = 1 ∨ sp.pending.size = 2 ∨
      sp.pending.size = 3 ∨ sp.pending.size = 4 := by omega
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hcnt] at hpc1
  rcases hcases with h | h | h | h | h <;> rw [h] at hpc1 <;>
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
  · -- `b6`, `b7`, `b8`.
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b0 run_b6) hwf
      (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplexInput.b6Offset) NativeRustcVmArm.Vm.SpongeWDuplexInput.label_6_at)) hm1 fun st2 hm2 hpc2 => ?_
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b6 run_b7_0) hwf
      hpc2 hm2 fun st3 hm3 hpc3 => ?_
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7_0 run_b8_0) hwf
      hpc3 hm3 fun st4 hm4 hpc4 => ?_
    have he := end0
    unfold E0 at he
    rw [after_eq run_b8_0] at he
    exact finish hsp hwf hm0 h he hm4 hpc4
  all_goals
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf
      hpc1 hm1 fun st2 hm2 hpc2 => ?_
    simp only [PcOk] at hpc2
    sym_simp at hpc2
    rw [hcnt, h] at hpc2
    simp (config := { decide := true }) only [↓reduceIte] at hpc2
  · -- `b7`, `b8`.
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b1 run_b7_1) hwf
      (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplexInput.b7Offset) NativeRustcVmArm.Vm.SpongeWDuplexInput.label_7_at)) hm2 fun st3 hm3 hpc3 => ?_
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7_1 run_b8_1) hwf
      hpc3 hm3 fun st4 hm4 hpc4 => ?_
    have he := end1
    unfold E1 at he
    rw [after_eq run_b8_1] at he
    exact finish hsp hwf hm0 h he hm4 hpc4
  all_goals
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b1 run_b2) hwf
      hpc2 hm2 fun st3 hm3 hpc3 => ?_
    simp only [PcOk] at hpc3
    sym_simp at hpc3
    rw [hcnt, h] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
  · -- `b8`.
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b2 run_b8_2) hwf
      (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplexInput.b8Offset) NativeRustcVmArm.Vm.SpongeWDuplexInput.label_8_at)) hm3 fun st4 hm4 hpc4 => ?_
    have he := end2
    unfold E2 at he
    rw [after_eq run_b8_2] at he
    exact finish hsp hwf hm0 h he hm4 hpc4
  all_goals
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2 run_b3) hwf
      hpc3 hm3 fun st4 hm4 hpc4 => ?_
    simp only [PcOk] at hpc4
    sym_simp at hpc4
    rw [hcnt, h] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
  · -- `b5`.
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b3 run_b5_3) hwf
      (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWDuplexInput.b5Offset) NativeRustcVmArm.Vm.SpongeWDuplexInput.label_5_at)) hm4 fun st5 hm5 hpc5 => ?_
    have he := end3
    unfold E3 at he
    rw [after_eq run_b5_3] at he
    exact finish hsp hwf hm0 h he hm5 hpc5
  · -- `b4`, `b5`.
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) (exec_after run_b3 run_b4) hwf
      hpc4 hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b4 run_b5_4) hwf
      hpc5 hm5 fun st6 hm6 hpc6 => ?_
    have he := end4
    unfold E4 at he
    rw [after_eq run_b5_4] at he
    exact finish hsp hwf hm0 h he hm6 hpc6

end

end NativeRustcVmArm.Transcript.DuplexInput
