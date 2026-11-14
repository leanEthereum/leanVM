/-
  LeanVM.Guest.B1.Main.MainGoalsFChk

  `main`'s first loops (`main_loop0`, `main_loop1`), checked by kernel evaluation: their places in
  the program, their loop shape, and that they place nothing.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.Data.NameStrings

/-!
# `main`'s first loops, checked

`main_loop0`, `main_loop1` (G:4505-4510) write the hinted duplicate signature claims: each block is
atoms and one heap hint, no load. `mfLoop_pure`: the two place nothing and call only each other.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem mfL1_idx : coreProgram.indexOf? name% «main_loop0» = some idx% «main_loop0» :=
  coreProgram_indexOf?_at (j := idx% «main_loop0») rfl

set_option maxRecDepth 100000 in
theorem mfL2_idx : coreProgram.indexOf? name% «main_loop1» = some idx% «main_loop1» :=
  coreProgram_indexOf?_at (j := idx% «main_loop1») rfl

set_option maxRecDepth 100000 in
theorem mfL1_shape : loopShapeF (coreProgram.getD idx% «main_loop0» default) name% «main_loop0» =
    true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mfL2_shape : loopShapeF (coreProgram.getD idx% «main_loop1» default) name% «main_loop1» =
    true := by decide +kernel

/-- `main`'s first two loops. -/
def mfLoopSet : List String := [name% «main_loop0», name% «main_loop1»]

/-- Every member of `mfLoopSet` places nothing and calls members only. -/
noncomputable def mfLoopOk : Bool :=
  mfLoopSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList mfLoopSet fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem mfLoop_ok : mfLoopOk = true := by decide +kernel

theorem mfLoop_pure : coreProgram.PureIn mfLoopSet := by
  intro g hg fn hf
  have h := List.all_eq_true.mp mfLoop_ok g hg
  rw [hf] at h
  exact h

end
end LeanVM.Guest.B1.Main
