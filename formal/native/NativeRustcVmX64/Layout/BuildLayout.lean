module

public import NativeRustcVmX64.Layout.BuildLayout.Finish
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names
public import NativeRustcVmX64.Code.Vm.ColumnKappas.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names

/-!
# `build_layout` on x86-64

**`buildLayout_spec`**: rustc's `build_layout(n, log_memory, rows, layout)`, placed anywhere in the
program, meets `BuildLayoutPre`/`BuildLayoutPost` given `bit_length`'s, `column_kappas`' and
`placements_of`'s contracts. The entry checks the bytecode's length a power of two, the log-sizes
and the row counts (`checks`, else `0` returned); `b9` to `b14` store the log-sizes, the row counts
and the heights (`stores`); `b15` calls `column_kappas` (`kappas`); `b16` to `b20` call
`placements_of`, store the stack's log-size and return `1` (`finish`). The words stored are the
model's `layoutF`, which `buildLayout` returns exactly when the checks pass (`model_some`,
`model_none`).
-/

namespace NativeRustcVmX64.Layout.BuildLayout

open NativeRustcX64 NativeRustcVmX64.Vm.BuildLayout NativeRustcVmX64.Transcript NativeVm.Model
open NativeRustcVm.Layout

public section

variable [Host] {k : Nat}

/-- **`build_layout` meets its contract.** -/
theorem buildLayout_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hck : Spec (Labels.label NativeRustcVmX64.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost)
    (hpl : Spec (Labels.label NativeRustcVmX64.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost)
    {bc : Array UInt64} :
    Spec (Labels.label NativeRustcVmX64.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  refine Eventually.bind (checks hp hbl hF) fun s1 h1 ↦ h1.elim (fun h ↦ .done _ h) fun ⟨hpc1, h9⟩ ↦ ?_
  refine Eventually.bind (stores hp hbl hF hpc1 h9) fun s2 ⟨hpc2, h2, h15⟩ ↦ ?_
  refine Eventually.bind (kappas hp hck hF hpc2 h2 h15) fun s3 ⟨hpc3, h3⟩ ↦ ?_
  exact finish hp hpl hF hpc3 h3

end

end NativeRustcVmX64.Layout.BuildLayout
