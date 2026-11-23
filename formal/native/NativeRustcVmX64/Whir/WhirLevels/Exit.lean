module

public import NativeRustcVmX64.Whir.WhirLevels.Steps

/-!
# `whir_levels`: `None` returned (x86-64)

`none_exit`: at `NativeRustcVmX64.Vm.WhirLevels.label_5` (`b7`) from a state of the frame (RSP at offset `8`) where the run
rejects, `0` in AL, the registers restored, `ret`. `changes`: the frame's changes are the
contract's.
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

theorem outs_inAny {m0 : MachineData} {q : BitVec 64} (hq : outs m0 q) :
    NativeRustcVm.InAny [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] q := by
  rcases hq with hq | hq
  · exact ⟨_, List.mem_cons_self, hq⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

theorem inAny_outs {m0 : MachineData} {q : BitVec 64}
    (hq : NativeRustcVm.InAny [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] q) : outs m0 q := by
  obtain ⟨r, hr, hq⟩ := hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl hq
  · exact Or.inr hq

/-- The frame's changes are the contract's. -/
theorem changes {m0 d : MachineData} {o : Nat} (hf : Fr m0 o d) :
    ChangesIn m0 d whirLevelsStack [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hf.same fun q hq ↦ by
    rcases hq with hq | hq
    · exact Or.inr hq
    · exact Or.inl (outs_inAny hq)

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **`None` returned** at `NativeRustcVmX64.Vm.WhirLevels.label_5`. -/
theorem none_exit (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate)
    {st : MachineState} (hf : Fr m0 8 st.data) (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b7Offset))
    (hnone : runAll s0 levels b claim m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hwf := c.wf (d := st.data) (rest := []) (ret := 0) hf.frame.kept (by simp)
    (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 112 [] (fun _ ↦ 0) 0) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b7
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk, Sym.eval] at hpc'
  refine .done _ ⟨hpc'.trans (hf.frame.load_ret c.stack frame_le), hrsp, ?_, ?_, ?_, hsv⟩
  · show boolRet st'.data = _
    rw [boolRet, show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    simp only [runAll] at hnone ⊢
    rw [hnone]
    rfl
  · intro x s' h
    simp only [runAll] at hnone
    rw [hnone] at h
    cases h
  · rw [show ChangesIn m0 st'.data whirLevelsStack _ ↔ ChangesIn m0 st.data whirLevelsStack _ by
      unfold ChangesIn; rw [hd]]
    exact changes hf

end

end NativeRustcVmX64.Whir.Levels.WL
