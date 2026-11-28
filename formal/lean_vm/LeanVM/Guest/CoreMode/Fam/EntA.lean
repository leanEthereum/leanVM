/-
  LeanVM.Guest.CoreMode.Fam.EntA

  The deployed alignment enters each function at its compiled entry: `EntIdx Bridge.alignA`.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResTA
public import LeanVM.Guest.Bridge.ProgAlDefs

/-!
# The deployed alignment's entries

`Bridge.alignA f` is the alignment check's data of `f`'s compiled index `j`, whose context is
`AlignCtx.ofData` at `(fnOf j).entryPc`, so its entry is the compiled entry (`entIdx_alignA`), the
hypothesis `termNodeA_of` and `coreTermNodeA` take.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Bridge

public section

/-- **The deployed alignment enters each function at its compiled entry.** -/
theorem entIdx_alignA : EntIdx alignA := by
  intro f j h
  rw [entOf, alignA_of h]
  rfl

end

end LeanVM.Guest.EndExec
