/-
  LeanVM.Guest.B1.Da.PureAt

  The functions `da_verify` calls that place nothing (no `HeapBuf`, no `frameAddr`): one set
  closed under calls (`daPure`), so each is `CompleteAtD` from its relation on every memory holding
  the words it reads (`completeAt_of_rel_pureD`).
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Da.VerifyDefs

/-!
# The pure callees

`daPureSet`: the cell check, `da_verify`'s loops over the blobs, the columns' row loop, the
column offsets' doubling loops, the trees' `da_levels` and their level loops. `daPure`: it places
nothing and calls only its own members (kernel evaluation).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The level loops of the `da_levels` functions. -/
def lvlLoops : List String :=
  ["__loop69", "__loop70", "__loop71", "__loop72", "__loop73", "__loop74", "__loop75",
  "__loop48", "__loop49", "__loop50", "__loop51", "__loop52", "__loop53", "__loop54",
  "__loop55", "__loop56", "__loop57", "__loop58", "__loop59", "__loop60", "__loop61",
  "__loop62", "__loop63", "__loop64", "__loop65", "__loop66", "__loop67", "__loop68",
  "__loop76", "__loop77", "__loop78", "__loop79", "__loop80", "__loop81", "__loop82",
  "__loop83", "__loop84", "__loop85", "__loop86", "__loop87", "__loop88", "__loop89",
  "__loop90", "__loop91", "__loop92", "__loop93", "__loop94", "__loop95", "__loop96",
  "__loop97", "__loop98", "__loop99", "__loop100", "__loop101", "__loop102"]

/-- **The pure callees of `da_verify`**: the cell check, the loops over the blobs (`__loop21`,
`__loop23`, `__loop24`), the columns' row loop (`__loop25`), the offsets' doubling loops
(`__loop26` to `__loop32`), the DA levels and their loops. -/
def daPureSet : List String :=
  ["da_verify_cell", "__loop21", "__loop23", "__loop24", "__loop25", "__loop26", "__loop27",
    "__loop28", "__loop29", "__loop30", "__loop31", "__loop32"] ++ dlNames ++ lvlLoops

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
