module

public import NativeRustcVmArm.Whir.SampleQueries.Entry

/-!
# `sample_queries`: the frame's environment, the epilogue

A state of the frame runs a block from the environment of the frame alone (`frameEnv`, `frame_wf`,
`frame_match`); the epilogue (`b18`) returns to the caller (`finish`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- The frame's environment. -/
abbrev frameEnv (m0 st : MachineData) : Env := Env.ofMachine st [(base m0 112, 112)]

theorem frame_wf (h : SampleQueriesPre a s0 m0) {st : MachineData} (hf : SFr m0 st) :
    (frameEnv m0 st).WF := by
  have hN := pre_N h
  have hNv := N_val
  refine Env.wf_of ⟨⟨fun i hi ↦ hf.kept _ ?_, base_noWrap (by omega)⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hmap := (pre_stack h).2.2
  have := hmap (sampleQueriesStack - 112 + i) (by omega)
  rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 sampleQueriesStack +
    BitVec.ofNat 64 (sampleQueriesStack - 112 + i) = base m0 112 + BitVec.ofNat 64 i by
    rw [← base_add (F := 112) (by omega) hN, NativeRustcVm.addr_add_add]; rfl] at this

theorem frame_match (h : SampleQueriesPre a s0 m0) {st : MachineData} (hf : SFr m0 st) :
    Match (frameEnv m0 st) frameS st := by
  have hN := pre_N h
  have hNv := N_val
  refine match_ofMachine ⟨rfl, fun _ ↦ ?_, trivial⟩ ?_ trivial trivial trivial trivial
  · have e1 := base_toNat (m0 := m0) (F := 112) (by omega)
    have := (pre_stack h).1
    show (base m0 112).toNat % 16 = 0
    omega
  · rw [hf.sp]; simp [Sym.eval]

omit [Labels] in
/-- The frame's changes are the contract's. -/
theorem changes_of {st : MachineData} (hf : SFr m0 st) : ChangesIn m0 st sampleQueriesStack
    [⟨oA m0, queryBufBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hf.same fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

end

section
variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- `sample_queries`'s postcondition, reached. -/
abbrev Goal (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ SampleQueriesPost a s0 m0 st.data

/-- **The epilogue** (`b18`, `.LSampleQueries_14`): with `1` in X0, the positions and the
`TState` `auxP` gives, the contract met. -/
theorem finish (hp : Placed code k) (h : SampleQueriesPre a s0 m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b18Offset)) (hf : SFr m0 st.data) (hx0 : st.data.regs.X0 = 1)
    {qs : List UInt64} {s : TState}
    (hmod : auxP (dep m0) (cnt m0) (cnt m0) s0 = (qs.toArray, s))
    (hbuf : BufWordsAt st.data.dmem (oA m0) queryCap qs) (hts : TStateAt st.data.dmem (tA m0) a s) :
    Eventually (step1 Host.exe) (Goal a s0 m0) st := by
  have hwf := frame_wf h hf
  have hm := frame_match h hf
  refine exec_at (b18_in_code.trans hp.1 (by simp [b18])) run_b18 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hret, hsv⟩ := hf.exit hm' hwf (by decide)
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have h0 : st'.data.regs.X0 = st.data.regs.X0 := Match.reg_eq (r := .X0) hm hm' rfl rfl
  simp only [PcOk] at hpc'
  refine ⟨hpc'.trans hret, by rw [h0, hx0], ⟨qs.toArray, s, ?_, ?_, ?_⟩, ?_, hsv⟩
  · rw [sampleQueries_run, hmod]
  · rw [hd]; simpa using hbuf
  · rw [hd]; exact hts
  · intro q hq; rw [hd]; exact changes_of hf q hq

end

end

end NativeRustcVmArm.Whir.SampleQueries
