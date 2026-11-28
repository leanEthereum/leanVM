module

public import NativeRustcVmX64.Whir.SampleQueries.Basic

/-!
# `sample_queries` on x86-64: the return, the outer loop's end

`fin`: from `NativeRustcVmX64.Vm.SampleQueries.label_12` (`b6`, AL `1`, then `b19`) with the model's positions in the
buffer and its state in the `TState` (`Done`), the postcondition. `b9_step`: after a challenge's
positions (`AtB9`), back at the outer loop's head (`Outer`) or, after the last challenge, `fin`.
-/

namespace NativeRustcVmX64.Whir.SampleQueries

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.SampleQueries
open NativeRustcVmX64.Transcript (Frame frameEnv)
open NativeRustcVmX64.Arrays (pc_cond)
open NativeRustcVm (BufWordsAt WordsAt WordAt)

@[expose] public section

/-- **The end**: the model's positions `qs` in the buffer, its state `s'` in the `TState`. -/
structure Done [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (qs : List UInt64)
    (s' : TState) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  ts : TStateAt st.dmem (tA m0) a s'
  buf : BufWordsAt st.dmem (oA m0) queryCap qs
  model : auxP (dep m0) (cnt m0) (cnt m0) s0 = (qs.toArray, s')

end

public section

variable [Host] {k : Nat} {a : DecArea} {s0 : TState} {m0 : MachineData} {qs : List UInt64}
  {s' : TState}

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- Continue from a state at `pc`. -/
theorem at_pc {R : MachineState → Prop} {pc : Int64} {d : MachineData}
    (h : Eventually (step1 Host.exe) R ⟨d, pc⟩) {s : MachineState} (hd : s.data = d)
    (hpc : s.pc = pc) : Eventually (step1 Host.exe) R s := by
  obtain ⟨d', pc'⟩ := s
  simp only at hd hpc
  subst hd hpc
  exact h

/-- The postcondition from the end's state with AL `1`, back at the return address. -/
theorem post_of (h : SampleQueriesPre a s0 m0) {st : MachineData} (hd : Done a s0 m0 qs s' st)
    {st' : MachineData} (hdm : st'.dmem = st.dmem) (hal : (reg st' .rax).toNat % 256 = 1)
    (hs : Saved m0 st') : SampleQueriesPost a s0 m0 st' := by
  have _ := h
  refine ⟨hal, ⟨qs.toArray, s', ?_, hdm ▸ hd.buf, hdm ▸ hd.ts⟩, fun q hq ↦ ?_, hs⟩
  · rw [sampleQueries_run, hd.model]
  · rw [hdm]
    refine hd.ctx.same q fun ho ↦ hq ?_
    rcases ho with ho | ho | ho
    · exact .inl ⟨_, List.mem_cons_self .., ho⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ho⟩
    · exact .inr ho

/-- **The return** from `NativeRustcVmX64.Vm.SampleQueries.label_12`: AL `1`, `b19`. -/
theorem fin (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {st : MachineData}
    (hd : Done a s0 m0 qs s' st) :
    Eventually (step1 Host.exe) (Post a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.SampleQueries.b6Offset)⟩ := by
  have hwf := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hd.ctx.fr.kept
  refine exec_then (inf hp b6_in_code (by simp [b6])) run_b6 hwf (by intro l h; cases h)
    (mid_match hd.ctx.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hax, hk⟩ := after_eq run_b6 ▸ ok_b6
  have hc1 := hd.ctx.block h hm1 (L := 0) (by omega) hmid (wr0_nil hmem 0) (kept_spec hk (by simp))
  have hd1 : st1.data.dmem = st.dmem := hm1.dmem_eq hwf hmem
  simp only [PcOk] at hpc1
  have hwf1 := mid_wf (vars := fun _ ↦ 0) (ret := 0) h hc1.fr.kept
  refine exec_at (inf hp b19_in_code (by simp [b19])) run_b19 hwf1 (by intro l h; cases h)
    (hpc1.trans (hp.label NativeRustcVmX64.Vm.SampleQueries.label_13_at)) (mid_match hc1.fr) fun st2 hm2 hpc2 ↦ .done _ ?_
  obtain ⟨he, hmem2, hk2⟩ := after_eq run_b19 ▸ ok_b19
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hc1.fr hwf1 hm2 he
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  refine ⟨?_, hrsp, post_of h hd (hd2.trans hd1) ?_ hsv⟩
  · simp only [PcOk] at hpc2
    rw [hpc2]
    exact hc1.fr.load_ret (pre_S h) N_ge
  · rw [show reg st2.data .rax = reg st1.data .rax from reg_kept hm2 (kept_spec hk2 (by simp)),
      show reg st1.data .rax = _ from hm1.regs .rax _ hax]
    exact al_one _

end

end NativeRustcVmX64.Whir.SampleQueries
