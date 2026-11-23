module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Round

/-!
# `TState::open_phase`

**`openPhase_spec`**: the shape, count and positions checks (`check_spec`), the climbs' start
(`start_spec`), the loop over the openings (a climb each: `hash_spec`, `path_spec`,
`round_spec`); the output holds `openPhase`'s rows or `None` (`OpenPhasePost`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcVmArm.Vm.OpenPhase
open NativeVm.Model NativeRustcVm.Transcript LeanVM.Protocol

public section

variable [Host] {k : Nat}

/-- **The climbs' loop**: from `.L11`, the exit. -/
theorem climbs_spec (hp : Placed code k)
    (hkh : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hcl : ∀ N P, Spec (Labels.label NativeRustcVmArm.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P))
    {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData}
    (hpre : OpenPhasePre P R Q m0) {h w : Nat} (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat}
    {m : MachineData} (hi : CInv m0 P Q R h w j m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset) ∧
      ∃ j, P.size - j = n ∧ CInv m0 P Q R h w j st.data) (fun n st ⟨hpc, j, hn, hi⟩ ↦ ?_)
    ⟨rfl, j, rfl, hi⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  have hl := hi.lt
  refine Eventually.bind (hash_spec hp hkh hpre hph hi) fun st ⟨hpc, hh⟩ ↦ ?_
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (path_spec hp hcl hpre hph hh) fun st ⟨hpc, hc⟩ ↦ ?_
  obtain ⟨d2, pc2⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono (round_spec hp hpre hph hc) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hinv⟩
  · exact .inl h
  · exact .inr ⟨P.size - (j + 1), by omega, hpc, j + 1, rfl, hinv⟩

/-- **`open_phase`: its contract.** -/
theorem openPhase_spec (hp : Placed code k)
    (hkh : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hcl : ∀ N P, Spec (Labels.label NativeRustcVmArm.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P))
    (P : Array OpeningW) (R : Digest) (Q : Array UInt64) :
    Spec (Labels.label NativeRustcVmArm.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q) (OpenPhasePost P R Q) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.OpenPhase.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.OpenPhase.entryOffset) NativeRustcVmArm.Vm.OpenPhase.entry_at]
  obtain ⟨h, w, hph⟩ : ∃ h w, PhaseHW m0.dmem (phO m0) P h w := hpre.2.2.1
  refine Eventually.bind (check_spec hp hpre hph) fun st hst ↦ ?_
  rcases hst with hst | ⟨hpc, hc⟩
  · exact Eventually.done _ hst
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.bind (start_spec hp hpre hph hc) fun st hst ↦ ?_
  rcases hst with hst | ⟨hpc, hi⟩
  · exact Eventually.done _ hst
  obtain ⟨d', pc'⟩ := st
  simp only at hpc
  subst hpc
  exact climbs_spec hp hkh hcl hpre hph hi

end

end NativeRustcVmArm.Sumcheck.OpenPhase
