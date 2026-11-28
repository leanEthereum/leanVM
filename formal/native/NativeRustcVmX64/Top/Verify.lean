module

public import NativeRustcVmX64.Top.Verify.Exit
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmX64.Code.Vm.Seed.Names
public import NativeRustcVmX64.Code.Vm.Verify.Names
public import NativeRustcVmX64.Code.Vm.VerifyExecution.Names

/-!
# `verify` on x86-64

**`verify_spec`**: rustc's `verify`, placed anywhere in the program, meets its contract
(`VerifyPre`, `VerifyPost`) given the contracts of `seed`, `verify_execution` and
`Decoded::phase_count`. The prologue and `seed` (`stageA`), `TState::new` and the walk
(`stageB`), then the end checks (`stageC`): AL is `Model.verify`'s verdict.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcVmX64.Vm.Verify NativeRustcVm.Transcript NativeVm.Model

public section

variable [Host] {k : Nat}

/-- **`verify` meets its contract.** -/
theorem verify_spec (hp : Placed code k)
    (hseed : Spec (Labels.label NativeRustcVmX64.Vm.Seed.entryLabel) SeedPre SeedPost)
    (hve : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmX64.Vm.Verify.entryLabel) (VerifyPre a stream openings) (VerifyPost stream openings) := by
  intro m0 hpre
  rw [lbl_entry hp]
  refine Eventually.bind (stageA hp hseed hpre) fun st1 ⟨hpc1, hSA⟩ ↦ ?_
  refine Eventually.bind (stageB hp hve hpre hpc1 hSA) fun st2 ⟨hpc2, hSB⟩ ↦ ?_
  refine Eventually.mono (stageC hp hpcnt hpre hpc2 hSB) fun st ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, fun bcw hl hbc P hP ↦ ?_, fun q hq ↦ h4 q fun h ↦ hq ?_, h5⟩
  · rw [bcOf_eq hl hbc, pubOf_eq hP]
    exact h3
  · rcases h with h | h
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_self, h⟩

end

end NativeRustcVmX64.Top.Verify
