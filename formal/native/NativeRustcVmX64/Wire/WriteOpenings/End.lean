module

public import NativeRustcVmX64.Wire.WriteOpenings.Model
public import NativeRustcVmX64.Wire.WriteOpenings.Mem

/-!
# `write_openings`' end (x86-64)

At the epilogue (`AtEnd`, `b54`): AL `1` with every opening written, or something `Bad`. Then
the contract's postcondition (`end_spec`). A rejection (`b53`): RAX cleared, then the epilogue
(`fail_spec`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 hiding InRange SameOutside
open NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.WriteOpenings
open NativeRustcVmX64.Transcript (Frame)
open NativeRustcVm (WordAt WordsAt wordOf InRange SameOutside)

@[expose] public section

variable [Host]

/-- At the epilogue, the result in AL. -/
structure AtEnd (R : Run) (st : MachineState) : Prop where
  pc : st.pc = pcOf R 280
  fr : Fr R 8 st.data
  res : (boolRet st.data = 1 ∧ R.Done st.data.dmem R.nq) ∨ R.Bad

/-- What `write_openings` reaches. -/
abbrev Post (R : Run) (st : MachineState) : Prop :=
  st.pc = retOf R.m0 ∧ rspOf st.data = rspOf R.m0 + 8#64 ∧ WriteOpeningsPost R.m0 st.data

end

public section

variable {R : Run}

/-- The body's state without chunks. -/
theorem frMatch [Labels] {m : MachineData} (hfr : Frame R.m0 160 slots 8 m) {ret : BitVec 64} :
    Match (envOf R m [] ret) frS m :=
  match_fS hfr (csz := []) trivial (al := []) trivial

variable [Host]

/-- **The epilogue**: the contract's postcondition. -/
theorem end_spec (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : AtEnd R st) :
    Eventually (step1 Host.exe) (Post R) st := by
  have hwf := G.wf0 H.fr.fr.kept (ret := 0)
  refine exec_at (infix_of b54_in_code (by simp [b54]) hp) run_b54 hwf nofun H.pc
    (frMatch H.fr.fr) fun st' hm hpc' ↦ Eventually.done _ ?_
  obtain ⟨hsv, hrsp⟩ := NativeRustcVmX64.Transcript.Frame.epilogue H.fr.fr hwf hm (by decide +kernel)
  have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq hwf rfl
  have h0 : reg st'.data .rax = reg st.data .rax := hm.regs .rax _ rfl
  refine ⟨?_, hrsp, fun qs ps leaves sibs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ↦ ?_, ?_, hsv⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact H.fr.fr.load_ret G.st (le_refl _)
  · have Hy : Hyp R qs ps leaves sibs := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    rcases H.res with ⟨hx, hdn⟩ | hb
    · refine ⟨by unfold boolRet; rw [h0]; exact hx, ?_⟩
      rw [hd]
      exact Hy.phaseAt_of G hdn
    · exact absurd hb Hy.not_bad
  · rw [hd]
    refine NativeRustcVm.SameOutside.mono H.fr.chg fun q hq ↦ ?_
    rcases hq with hq | hq
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
    · exact ⟨_, List.mem_cons_self, hq⟩

/-- **A rejection** (`b53`): RAX cleared, then the epilogue. -/
theorem fail_spec (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (hpc : st.pc = pcOf R 278) (hF : Fr R 8 st.data) (hb : R.Bad) :
    Eventually (step1 Host.exe) (Post R) st :=
  blk hp b53_in_code (by simp [b53]) run_b53 hF hpc (G.wf0 hF.fr.kept (ret := 0))
    (frMatch hF.fr) nofun (by decide +kernel) (by decide +kernel) fun st' hF' _ hpc' _ ↦
      end_spec hp G ⟨hpc'.trans (congrArg Host.addrOf rfl), hF', .inr hb⟩

end

end NativeRustcVmX64.Wire.WriteOpenings
