module

public import NativeRustcVmArm.Code.Vm.ClimbLevel.Names
public import NativeRustcVmArm.Code.Vm.InsD.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Code.Vm.RdRows.Names
public import NativeRustcVmArm.Code.Vm.ReaderLe.Names
public import NativeRustcVmArm.Code.Vm.WriteOpenings.Names
public import NativeRustcVmArm.Wire.PhaseM.Write

/-!
# `phase_m` meets its contract

`phaseM_spec`: the counts and the first query read (`first_run`), the other queries (`qloop`), the
height and the widths (`rest_run`), the queries sorted (`sort_run`), the sizes checked
(`sizes_run`), the rows read (`rows_run`), the leaves hashed (`hash_run`), the climb (`climb_run`),
the openings written (`write_run`); a failed read or check leaves by `none_run`, the end by
`done_run`.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

variable [Host] {k : Nat}

/-- **From the entry.** -/
theorem entry_spec (hp : Placed code k) (G : Geo m0 bp B) (hR : ReaderAt m0.dmem (rdr m0) bp B c)
    (hcl : Spec (Labels.label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost)
    (hins : Spec (Labels.label NativeRustcVmArm.Vm.InsD.entryLabel) InsDPre InsDPost)
    (hkw : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hrows : Spec (Labels.label NativeRustcVmArm.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hwo : Spec (Labels.label NativeRustcVmArm.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b0Offset)⟩ := by
  have hnone : ∀ st, AtNone m0 B c k st → Eventually (step1 Host.exe) (Post m0) st :=
    fun _ h ↦ none_run hp G hR h
  refine Eventually.bind (first_run hp G hle hR) fun _ h1 ↦ ?_
  have h30 : ∀ st, (∃ count qs c2, At30 m0 bp B c k count qs c2 st) →
      Eventually (step1 Host.exe) (Post m0) st := by
    rintro _ ⟨count, qs, c2, h3⟩
    refine Eventually.bind (rest_run hp G hle h3) fun _ h4 ↦ ?_
    rcases h4 with h4 | ⟨height, lw, rw, c5, h4⟩
    · exact hnone _ h4
    refine Eventually.bind (sort_run hp G hins h4) fun _ h5 ↦ ?_
    rcases h5 with h5 | h5
    · exact hnone _ h5
    refine Eventually.bind (sizes_run hp G h5) fun _ h6 ↦ ?_
    rcases h6 with h6 | ⟨h6, hpc6, h32, h64, hrl, hlast⟩
    · exact hnone _ h6
    refine Eventually.bind (rows_run hp G hrows h6 hpc6 h32 h64 hrl hlast) fun _ h7 ↦ ?_
    rcases h7 with h7 | ⟨rows, c6, h7⟩
    · exact hnone _ h7
    refine Eventually.bind (hash_run hp G hkw h7) fun _ h8 ↦ ?_
    refine Eventually.bind (climb_run hp G hcl h8) fun _ h9 ↦ ?_
    rcases h9 with h9 | ⟨sl, cf, h9⟩
    · exact hnone _ h9
    exact Eventually.bind (write_run hp G hwo h9) fun _ h10 ↦ done_run hp G hR h10
  rcases h1 with h1 | ⟨count, h1⟩ | h1
  · exact hnone _ h1
  · refine Eventually.bind (qloop hp G hle h1) fun _ h2 ↦ ?_
    rcases h2 with h2 | ⟨qs, c2, h2⟩
    · exact hnone _ h2
    · exact h30 _ ⟨count, qs, c2, h2⟩
  · exact h30 _ h1

/-- **`phase_m` meets its contract.** -/
theorem phaseM_spec (hp : Placed code k)
    (hcl : Spec (Labels.label NativeRustcVmArm.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost)
    (hins : Spec (Labels.label NativeRustcVmArm.Vm.InsD.entryLabel) InsDPre InsDPost)
    (hkw : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    (hrows : Spec (Labels.label NativeRustcVmArm.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost)
    (hle : Spec (Labels.label NativeRustcVmArm.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hwo : Spec (Labels.label NativeRustcVmArm.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost := by
  intro m0 hpre
  obtain ⟨-, -, -, -, bp, B, c, hR, -⟩ := id hpre
  rw [hp.label (j := NativeRustcVmArm.Vm.PhaseM.entryOffset) NativeRustcVmArm.Vm.PhaseM.entry_at]
  exact entry_spec hp (geo_of hpre hR) hR hcl hins hkw hrows hle hwo

end

end NativeRustcVmArm.Wire.PhaseM
