module

public import NativeRustcVmArm.Wire.WriteOpenings.Model
public import NativeRustcVmArm.Wire.WriteOpenings.Mem

/-!
# `write_openings`' end

At the epilogue (`AtEnd`, `b46`): X0 `1` with every opening written, or `0` with something
`Bad`. Then the contract's postcondition (`end_spec`). A rejection (`b45`): X0 cleared, then the
epilogue (`fail_spec`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

variable [Host]

/-- At the epilogue, the result in X0. -/
structure AtEnd (R : Run) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b46Offset
  fr : Frm R st.data
  res : (st.data.regs.X0 = 1 ∧ R.Done st.data.dmem R.nq) ∨ (st.data.regs.X0 = 0 ∧ R.Bad)

/-- What `write_openings` reaches. -/
abbrev Post (R : Run) (st : MachineState) : Prop :=
  st.pc = retOf R.m0 ∧ WriteOpeningsPost R.m0 st.data

end

public section

variable {R : Run}

theorem frMatch [Labels] (G : Geo R) {m : MachineData} (hfr : Frm R m) :
    Match (envOf R m []) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ G.aligned, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

variable [Host]

/-- **The epilogue**: the contract's postcondition. -/
theorem end_spec (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : AtEnd R st) :
    Eventually (step1 Host.exe) (Post R) st := by
  have hwf := G.wf0 H.fr.kept
  refine exec_at (infix_of b46_in_code (by simp [b46]) hp) run_b46 hwf H.pc (frMatch G H.fr)
    fun st' hm hpc' ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit H.fr hm hwf (by decide)
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq hwf rfl
  have h0 : st'.data.regs.X0 = st.data.regs.X0 := UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)
  refine ⟨hpc'.trans hret, fun cnt out hc ho ↦ ?_⟩
  have ec : cnt = R.cnt := congrArg UInt64.toBitVec (NativeRustcVm.WordAt.unique hc G.cntW)
  have eo : out = R.out := congrArg UInt64.toBitVec (NativeRustcVm.WordAt.unique ho G.outW)
  subst ec eo
  refine ⟨fun qs ps leaves sibs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ↦ ?_, ?_, hsv⟩
  · have Hy : Hyp R qs ps leaves sibs := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    rcases H.res with ⟨hx, hdn⟩ | ⟨-, hb⟩
    · exact ⟨h0.trans hx, by rw [hd]; exact Hy.phaseAt_of G hdn⟩
    · exact absurd hb Hy.not_bad
  · rw [hd]
    refine NativeRustcVm.SameOutside.mono H.fr.same fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
    · exact ⟨_, List.mem_cons_self, hq⟩

/-- **A rejection** (`b45`): X0 cleared, then the epilogue. -/
theorem fail_spec (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b45Offset) (hfr : Frm R st.data) (hb : R.Bad) :
    Eventually (step1 Host.exe) (Post R) st := by
  have hwf := G.wf0 hfr.kept
  refine exec_at (infix_of b45_in_code (by simp [b45]) hp) run_b45 hwf hpc (frMatch G hfr)
    fun st' hm hpc' ↦ ?_
  have hfr' : Frm R st'.data := Fr.ofBlock hfr (frMatch G hfr) hm hwf rfl rfl rfl
    (fun r hr ↦ by cases hr)
  refine end_spec hp G ⟨hpc'.trans (congrArg Host.addrOf rfl), hfr', .inr ⟨?_, hb⟩⟩
  apply UInt64.toBitVec_inj.mp
  rw [show st'.data.regs.X0 = st'.data.regs.getXReg .X0 from rfl, hm.regs .X0 _ rfl]
  rfl

end

end NativeRustcVmArm.Wire.WriteOpenings
