/-
  LeanVM.Guest.B1.Da.PureAt

  The functions `da_verify` calls that place nothing (no `HeapBuf`, no `frameAddr`): one set
  closed under calls (`daPure`), so each is `CompleteAtD` from its relation on every memory holding
  the words it reads (`completeAt_of_rel_pureD`).
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Da.VerifyDefs
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

/-- The level loops of the `da_levels` functions. -/
def lvlLoops : List String :=
  [name% «da_levels__L2_L1_loop0», name% «da_levels__L4_L2_loop0», name% «da_levels__L4_L2_loop1», name% «da_levels__L8_L3_loop0», name% «da_levels__L8_L3_loop1», name% «da_levels__L8_L3_loop2», name% «da_levels__L16_L4_loop0»,
  name% «da_levels__L16_L4_loop1», name% «da_levels__L16_L4_loop2», name% «da_levels__L16_L4_loop3», name% «da_levels__L32_L5_loop0», name% «da_levels__L32_L5_loop1», name% «da_levels__L32_L5_loop2», name% «da_levels__L32_L5_loop3»,
  name% «da_levels__L32_L5_loop4», name% «da_levels__L64_L6_loop0», name% «da_levels__L64_L6_loop1», name% «da_levels__L64_L6_loop2», name% «da_levels__L64_L6_loop3», name% «da_levels__L64_L6_loop4», name% «da_levels__L64_L6_loop5»,
  name% «da_levels__L128_L7_loop0», name% «da_levels__L128_L7_loop1», name% «da_levels__L128_L7_loop2», name% «da_levels__L128_L7_loop3», name% «da_levels__L128_L7_loop4», name% «da_levels__L128_L7_loop5», name% «da_levels__L128_L7_loop6»,
  name% «da_levels__L256_L8_loop0», name% «da_levels__L256_L8_loop1», name% «da_levels__L256_L8_loop2», name% «da_levels__L256_L8_loop3», name% «da_levels__L256_L8_loop4», name% «da_levels__L256_L8_loop5», name% «da_levels__L256_L8_loop6»,
  name% «da_levels__L256_L8_loop7», name% «da_levels__L512_L9_loop0», name% «da_levels__L512_L9_loop1», name% «da_levels__L512_L9_loop2», name% «da_levels__L512_L9_loop3», name% «da_levels__L512_L9_loop4», name% «da_levels__L512_L9_loop5»,
  name% «da_levels__L512_L9_loop6», name% «da_levels__L512_L9_loop7», name% «da_levels__L512_L9_loop8», name% «da_levels__L1024_L10_loop0», name% «da_levels__L1024_L10_loop1», name% «da_levels__L1024_L10_loop2», name% «da_levels__L1024_L10_loop3»,
  name% «da_levels__L1024_L10_loop4», name% «da_levels__L1024_L10_loop5», name% «da_levels__L1024_L10_loop6», name% «da_levels__L1024_L10_loop7», name% «da_levels__L1024_L10_loop8», name% «da_levels__L1024_L10_loop9»]

/-- **The pure callees of `da_verify`**: the cell check, the loops over the blobs (`da_verify_loop0`,
`da_verify_loop2`, `da_verify_loop3`), the columns' row loop (`da_verify_column_loop0`), the offsets' doubling loops
(`da_column_offsets_loop0` to `da_column_offsets_loop6`), the DA levels and their loops. -/
def daPureSet : List String :=
  ["da_verify_cell", name% «da_verify_loop0», name% «da_verify_loop2», name% «da_verify_loop3», name% «da_verify_column_loop0», name% «da_column_offsets_loop0», name% «da_column_offsets_loop1»,
    name% «da_column_offsets_loop2», name% «da_column_offsets_loop3», name% «da_column_offsets_loop4», name% «da_column_offsets_loop5», name% «da_column_offsets_loop6»] ++ dlNames ++ lvlLoops

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
