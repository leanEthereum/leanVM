/-
  LeanVM.Guest.B1.Da.PureAt

  The functions `da_verify` calls that place nothing (no `HeapBuf`, no `frameAddr`): one set
  closed under calls (`daPure`), so each is `CompleteAtD` from its relation on every memory holding
  the words it reads (`completeAt_of_rel_pureD`).
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Da.LevelsTab
public import LeanVM.Guest.Data.NameStrings

/-!
# The pure callees

`daPureSet`: the cell check, `da_verify`'s loops over the blobs, the columns' row loop, the
column offsets' doubling loops, the trees' `da_levels` and their level loops. `daPure`: it places
nothing and calls only its own members (kernel evaluation).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The pure callees of `da_verify`**: the cell check, the loops over the blobs
(`da_verify_loop0`, `da_verify_loop2`, `da_verify_loop3`), the columns' row loop
(`da_verify_column_loop0`), the offsets' doubling loops
(`da_column_offsets_loop0` to `da_column_offsets_loop6`), the DA levels and their loops (`dlTab`). -/
def daPureSet : List String :=
  ["da_verify_cell", name% «da_verify_loop0», name% «da_verify_loop2», name% «da_verify_loop3»,
      name% «da_verify_column_loop0», name% «da_column_offsets_loop0»,
      name% «da_column_offsets_loop1»,
    name% «da_column_offsets_loop2», name% «da_column_offsets_loop3»,
        name% «da_column_offsets_loop4», name% «da_column_offsets_loop5»,
        name% «da_column_offsets_loop6»] ++ dlTab.map (·.2.1) ++ dlTab.flatMap (·.2.2.2)

/-- Every member's body places nothing and calls members only. -/
noncomputable def daPureOk : Bool :=
  daPureSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList daPureSet fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem daPure_ok : daPureOk = true := by decide +kernel

theorem daPure : coreProgram.PureIn daPureSet := by
  intro g hg fn hf
  have h := List.all_eq_true.mp daPure_ok g hg
  rw [hf] at h
  exact h

end
end LeanVM.Guest.B1.Da
