module

public import NativeRustcVmArm.Whir.FinalLevel.Basic
public import NativeRustcVmArm.Whir.FinalLevel.Model

/-!
# `final_level`: the exits

`exit3`: from `.LFinalLevel_3` (`b3`, the epilogue) with X0 the verdict of the run `r`;
`exit2`: from `.LFinalLevel_2` (`b2`, `0`, then the epilogue) on a rejection.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel

public section

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

theorem inf (hp : Placed code k) {bl : List Directive} {j : Nat} (hb : bl.IsInfixAt code j)
    (hne : bl ≠ []) : bl.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- The model's run of `final_level`. -/
abbrev runF (s0 : TState) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) : Option (Unit × TState) :=
  (finalLevelM m0.regs.X1.toNat level m0.regs.X3.toNat m0.regs.X4.toNat b w rounds).run s0

/-- **The epilogue** (`b3`): X0 the verdict of the run, the `TState` its state. -/
theorem exit3 (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b3Offset)) (hf : FFr m0 st.data)
    (hx0 : st.data.regs.X0 = okWord (runF s0 level b w rounds m0).isSome)
    (hn : NextAt st.data.dmem (tA m0) a (runF s0 level b w rounds m0)) :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hwf := c.fwf hf
  refine exec_at (inf hp b3_in_code (by simp [b3])) run_b3 hwf hpc (c.fmatch hf)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hret, hsv⟩ := hf.exit hm1 hwf (by decide)
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hX0 : st1.data.regs.X0 = st.data.regs.X0 := reg_of hm1 (r := .X0) rfl rfl
  refine .done _ ⟨hpc1.trans hret, by rw [hX0]; exact hx0, by rw [hd]; exact hn, ?_, hsv⟩
  intro q hq
  rw [hd]
  refine hf.same q fun h ↦ hq ?_
  rcases h with h | h | h
  · exact .inr h
  · exact .inl ⟨_, List.mem_cons_self, c.q_sub h⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩

/-- **A rejection** (`b2`): `0`, the epilogue. -/
theorem exit2 (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b2Offset)) (hf : FFr m0 st.data)
    (hr : runF s0 level b w rounds m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hwf := c.fwf hf
  refine exec_at (inf hp b2_in_code (by simp [b2])) run_b2 hwf hpc (c.fmatch hf)
    fun st1 hm1 hpc1 ↦ ?_
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hf1 : FFr m0 st1.data :=
    Fr.ofBlock hf (c.fmatch hf) hm1 hwf rfl rfl rfl (fun _ h ↦ by cases h)
  refine exec_at (inf hp b3_in_code (by simp [b3])) (exec_after run_b2 run_b3z) hwf hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hret, hsv⟩ := hf.exit hm2 hwf (by decide)
  have hd2 : st2.data.dmem = st.data.dmem := hm2.dmem_eq hwf rfl
  have hX0 : st2.data.regs.X0 = 0 := reg_of hm2 (r := .X0) rfl rfl
  refine .done _ ⟨hpc2.trans hret, ?_, ?_, ?_, hsv⟩
  · rw [hX0]; change _ = okWord (runF s0 level b w rounds m0).isSome; rw [hr]; rfl
  · change NextAt _ _ _ (runF s0 level b w rounds m0); rw [hr]; intro _ _ h; cases h
  · intro q hq
    rw [hd2]
    refine hf.same q fun h ↦ hq ?_
    rcases h with h | h | h
    · exact .inr h
    · exact .inl ⟨_, List.mem_cons_self, c.q_sub h⟩
    · exact .inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩

end

end NativeRustcVmArm.Whir.FinalLevel
