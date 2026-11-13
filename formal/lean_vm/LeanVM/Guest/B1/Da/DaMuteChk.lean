/-
  LeanVM.Guest.B1.Da.DaMuteChk

  The callees of `da_verify` that pop no witness stream: all but the column loop, the column, the row loop and the cell check, one call-closed set (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Da.PureAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `da_verify`'s callees popping nothing: all but the column loop, the column, the row loop and the cell check. -/
def daMuteSet : List String :=
  ["da_row_shape", "da_vector", "da_column_offsets", "da_expand__L14_L7", "da_factors__L14_L7_L0",
    "da_factors__L7_L8_L128", "da_expand__L7_L8", name% «da_verify_loop0», name% «da_verify_loop2»,
    name% «da_verify_loop3», name% «da_column_offsets_loop0», name% «da_column_offsets_loop1»,
    name% «da_column_offsets_loop2», name% «da_column_offsets_loop3», name% «da_column_offsets_loop4»,
    name% «da_column_offsets_loop5», name% «da_column_offsets_loop6»] ++ dlNames ++ lvlLoops

/-- Every member's body pops nothing and calls members only. -/
noncomputable def daMuteOk : Bool :=
  daMuteSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.muteList daMuteSet.contains fn.body
    | none => true

theorem daMute_ok : daMuteOk = true := by decide +kernel

theorem daMute : MuteIn coreProgram daMuteSet.contains := by
  intro g hg fn hf
  have h := List.all_eq_true.mp daMute_ok g (by simpa using hg)
  rw [hf] at h
  exact h

end
end LeanVM.Guest.B1.Da
