module

public import NativeRustcVmX64.Wire.PhaseM.Finish
public import NativeRustcVmX64.Code.Vm.ClimbLevel.Names
public import NativeRustcVmX64.Code.Vm.InsD.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.PhaseM.Names
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names
public import NativeRustcVmX64.Code.Vm.WriteOpenings.Names

/-! # `phase_m` meets its contract against the generated x86-64 semantics

The reads, sorting, size checks, rows, leaf hashes, climb, and opening writes compose through
opaque block summaries. Callees are supplied by their unchanged contracts.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcVmX64.Vm.PhaseM

public section

variable [Host] {k : Nat}

theorem phaseM_spec (hp : Placed code k)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hins : Spec (Labels.label NativeRustcVmX64.Vm.InsD.entryLabel) InsDPre InsDPost)
    (hrows : Spec (Labels.label NativeRustcVmX64.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost)
    (hkw : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost)
    (hcl : Spec (Labels.label NativeRustcVmX64.Vm.ClimbLevel.entryLabel) ClimbLevelPre ClimbLevelPost)
    (hwo : Spec (Labels.label NativeRustcVmX64.Vm.WriteOpenings.entryLabel) WriteOpeningsPre WriteOpeningsPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost := by
  intro m0 hpre
  obtain ⟨bp, B, c, hR, _⟩ := hpre.2.2.2.2
  have G := geo_of hpre hR
  rw [hp.label NativeRustcVmX64.Vm.PhaseM.entry_at]
  refine Eventually.bind (reads_run hp G hle hR) fun s1 h1 ↦ ?_
  rcases h1 with h1 | ⟨count, qs, height, lw, rw, c5, h1⟩
  · exact .done _ h1
  refine Eventually.bind (sort_run hp G hins h1) fun s2 h2 ↦ ?_
  rcases h2 with h2 | h2
  · exact .done _ h2
  refine Eventually.bind (sizes_run hp G hR h2) fun s3 h3 ↦ ?_
  rcases h3 with h3 | h3
  · exact .done _ h3
  refine Eventually.bind (rows_run hp G hrows hR h3) fun s4 h4 ↦ ?_
  rcases h4 with h4 | ⟨rows, c6, h4⟩
  · exact .done _ h4
  refine Eventually.bind (hash_run hp G hkw h4) fun s5 h5 ↦ ?_
  refine Eventually.bind (climb_run hp G hR hcl h5) fun s6 h6 ↦ ?_
  rcases h6 with h6 | ⟨sl, cf, h6⟩
  · exact .done _ h6
  exact openings_run hp G hR hwo h6

end

end NativeRustcVmX64.Wire.PhaseM
