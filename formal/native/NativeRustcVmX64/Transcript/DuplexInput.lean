module

public import NativeRustcVmX64.Transcript.DuplexInput.Exec
public import NativeRustcVm.Transcript.Sponge
public import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput.Names

/-!
# `SpongeW::duplex_input` on x86-64

**`duplexInput_spec`**: the 16 rate lanes of the sponge at RDI become `duplexInput`'s, the rest of
the sponge kept. The blocks (`NativeRustcVmX64.Transcript.DuplexInput.Exec`) run from one
environment, region 0 the return address, region 1 the sponge; the path taken is the queue's
count's, and every path ends with the lanes `laneSym n i` (`finish`).
-/

namespace NativeRustcVmX64.Transcript.DuplexInput

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWDuplexInput
open NativeRustcVm.Transcript NativeVm.Model LeanVM.Parameters

public section

/-- The environment: the return address at RSP, region 0; the sponge at RDI, region 1. -/
abbrev envOf (m : MachineData) : Env := frameEnv m m 0 [(reg m .rdi, 328)]

/-- The queue's count, loaded. -/
theorem load_count {m : MachineData} {sp : SpongeW} (hsp : SpongeAt m.dmem (reg m .rdi) sp) :
    (envOf m).load 1 296 8 = BitVec.ofNat 64 sp.pending.size :=
  load_of_wordAt hsp.n_pending

/-- **A rate lane** as the paths store it. -/
theorem lane_eval [Labels] {m : MachineData} {sp : SpongeW}
    (hsp : SpongeAt m.dmem (reg m .rdi) sp) {i : Nat} (hi : i < 16) :
    UInt64.ofBitVec ((laneSym sp.pending.size i).eval (envOf m)) =
      sp.duplexInput[i]'(by omega) := by
  rw [duplexInput_lt sp hi]
  unfold laneSym
  by_cases h : i / 4 < sp.pending.size
  · simp only [h, dite_true, show i < 4 * sp.pending.size by omega, ite_true]
    obtain ⟨hx, htag⟩ := hsp.pending (i / 4) h
    rw [ewAt_iff] at hx
    have h0 : (envOf m).load 1 (200 + 24 * (i / 4)) 8 = sp.pending[i / 4].1.c0.toBitVec :=
      load_of_wordAt hx.1
    have h1 : (envOf m).load 1 (208 + 24 * (i / 4)) 8 = sp.pending[i / 4].1.c1.toBitVec :=
      load_of_wordAt (by
        have := hx.2
        rwa [off_off, show 200 + 24 * (i / 4) + 8 = 208 + 24 * (i / 4) by omega] at this)
    have h3 : (envOf m).load 1 (216 + 24 * (i / 4)) 8 = sp.pending[i / 4].2.toBitVec :=
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
theorem finish {m0 : MachineData} {sp : SpongeW} (hst : StackOk m0 0)
    (hsp : SpongeAt m0.dmem (reg m0 .rdi) sp) (hwf : (envOf m0).WF) {E : SState} {n : Nat}
    (hn : sp.pending.size = n) (hE : EndOk n E) {st : MachineState}
    (hm : Match (envOf m0) E st.data) {next : Int64}
    (hpc : PcOk (envOf m0) (.ret (.load 0 0 8)) next st) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ DuplexInputPost sp m0 st'.data) st := by
  subst hn
  obtain ⟨hlanes, hw, hepi⟩ := hE
  set p := reg m0 .rdi with hpdef
  have hnw : NativeRustcVm.NoWrap p 328 := hwf.noWrap 1 p 328 rfl
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue Frame.entry hwf hm hepi
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem
      (fun q ↦ Touch p 328 (fun j ↦ 0 ≤ j ∧ j < 128) q ∨ False) :=
    SameOutside.mono (sameOutside_touch hwf hm (r := 1) rfl (by omega) hw) fun _ h ↦ Or.inl h
  have hA0 : Agree m0.dmem st.data.dmem p 328 (fun j ↦ 0 ≤ j ∧ j < 128) :=
    agree_of_sameOutside hnw (fun _ h ↦ h.elim) hsame
  have hA : Agree m0.dmem st.data.dmem p spongeBytes (· < 200) := hA0.mono fun j h ↦ by omega
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc]; exact Frame.entry.load_ret hst le_rfl,
    hrsp, ?_, ?_, hsv⟩
  · refine hsp.with_state hA (wordsAt_iff.mpr fun i hi ↦ ?_)
    simp only [Vector.length_toList] at hi
    rw [Vector.getElem_toList]
    by_cases h16 : i < 16
    · have := wordAt_write hm (r := 1) (o := 8 * i) rfl (by omega) (hlanes i h16)
      rwa [lane_eval hsp h16] at this
    · rw [duplexInput_ge sp (by omega) hi]
      have hold := (wordsAt_iff.mp hsp.state) i (by simpa using hi)
      rw [Vector.getElem_toList] at hold
      exact wordAt_agree hA0 (by omega) (fun j hj ↦ by omega) hold
  · intro q hq
    refine hsame q fun h ↦ hq ?_
    rcases h with ⟨j, hj, -, rfl⟩ | h
    · exact inRange_off_self hj (by unfold spongeBytes; unfold NativeRustcVm.NoWrap at hnw; omega)
    · exact h.elim

/-- **`SpongeW::duplex_input` meets its contract.** -/
theorem duplexInput_spec (hp : Placed code k) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmX64.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp) := by
  rintro m0 ⟨hst, ⟨hmap, hnw, hapS, -⟩, hsp⟩
  have hwf : (envOf m0).WF :=
    frame_wf ⟨frame_mapped hst le_rfl, frame_noWrap hst le_rfl⟩
      (by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hmap, hnw⟩)
      (List.pairwise_pair.mpr (Apart.symm' hapS))
  have hm0 : Match (envOf m0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  have hcnt := load_count hsp
  have hle : sp.pending.size ≤ 4 := hsp.pending_le
  unfold NativeRustcVmX64.Vm.SpongeWDuplexInput.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm0
    fun st1 hm1 hpc1 => ?_
  have hcases : sp.pending.size = 0 ∨ sp.pending.size = 1 ∨ sp.pending.size = 2 ∨
      sp.pending.size = 3 ∨ sp.pending.size = 4 := by omega
  simp only [PcOk] at hpc1
  sym_simp_at hpc1
  rw [hcnt] at hpc1
  rcases hcases with h | h | h | h | h <;> rw [h] at hpc1 <;>
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
  · -- `b5` to `b9`.
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b0 run_b5_0) hwf nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.label_1_at)) hm1 fun st2 hm2 hpc2 => ?_
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b5_0 run_b6_0) hwf
      nofun hpc2 hm2 fun st3 hm3 hpc3 => ?_
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b6_0 run_b7_0) hwf
      nofun hpc3 hm3 fun st4 hm4 hpc4 => ?_
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7_0 run_b8_0) hwf
      nofun hpc4 hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) (exec_after run_b8_0 run_b9_0) hwf
      nofun hpc5 hm5 fun st6 hm6 hpc6 => ?_
    have he := end0
    unfold E0 at he
    rw [after_eq run_b9_0] at he
    exact finish hst hsp hwf h he hm6 hpc6
  all_goals
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf nofun
      hpc1 hm1 fun st2 hm2 hpc2 => ?_
    simp only [PcOk] at hpc2
    sym_simp_at hpc2
    rw [hcnt, h] at hpc2
    simp (config := { decide := true }) only [↓reduceIte] at hpc2
  · -- `b6` to `b9`.
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) (exec_after run_b1 run_b6_1) hwf nofun
      (hpc2.trans (hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.label_3_at)) hm2 fun st3 hm3 hpc3 => ?_
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b6_1 run_b7_1) hwf
      nofun hpc3 hm3 fun st4 hm4 hpc4 => ?_
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7_1 run_b8_1) hwf
      nofun hpc4 hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) (exec_after run_b8_1 run_b9_1) hwf
      nofun hpc5 hm5 fun st6 hm6 hpc6 => ?_
    have he := end1
    unfold E1 at he
    rw [after_eq run_b9_1] at he
    exact finish hst hsp hwf h he hm6 hpc6
  all_goals
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b1 run_b2) hwf nofun
      hpc2 hm2 fun st3 hm3 hpc3 => ?_
    simp only [PcOk] at hpc3
    sym_simp_at hpc3
    rw [hcnt, h] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
  · -- `b7` to `b9`.
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) (exec_after run_b2 run_b7_2) hwf nofun
      (hpc3.trans (hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.label_5_at)) hm3 fun st4 hm4 hpc4 => ?_
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b7_2 run_b8_2) hwf
      nofun hpc4 hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) (exec_after run_b8_2 run_b9_2) hwf
      nofun hpc5 hm5 fun st6 hm6 hpc6 => ?_
    have he := end2
    unfold E2 at he
    rw [after_eq run_b9_2] at he
    exact finish hst hsp hwf h he hm6 hpc6
  all_goals
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2 run_b3) hwf nofun
      hpc3 hm3 fun st4 hm4 hpc4 => ?_
    simp only [PcOk] at hpc4
    sym_simp_at hpc4
    rw [hcnt, h] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
  · -- `b8`, `b9`.
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) (exec_after run_b3 run_b8_3) hwf nofun
      (hpc4.trans (hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.label_7_at)) hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) (exec_after run_b8_3 run_b9_3) hwf
      nofun hpc5 hm5 fun st6 hm6 hpc6 => ?_
    have he := end3
    unfold E3 at he
    rw [after_eq run_b9_3] at he
    exact finish hst hsp hwf h he hm6 hpc6
  · -- `b4`, `b9`.
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) (exec_after run_b3 run_b4) hwf nofun
      hpc4 hm4 fun st5 hm5 hpc5 => ?_
    refine exec_at (infix_of b9_in_code (by simp [b9]) hp) (exec_after run_b4 run_b9_4) hwf
      nofun (hpc5.trans (hp.label NativeRustcVmX64.Vm.SpongeWDuplexInput.label_9_at)) hm5 fun st6 hm6 hpc6 => ?_
    have he := end4
    unfold E4 at he
    rw [after_eq run_b9_4] at he
    exact finish hst hsp hwf h he hm6 hpc6

end

end NativeRustcVmX64.Transcript.DuplexInput
