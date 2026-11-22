/-
  LeanVM.Guest.CoreMode.Fam.SubDefs

  The proof stream's reads, as `sub` residuals.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.Gen.AnyLink
public import LeanVM.Guest.CoreMode.Fam.LinkDefs
public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.TermDefs
public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# The stream reads' sites

A read past a cursor in the proof stream (`stRes`); each reader's are its own (`keccak_layer`'s `stB`, `verify_tables`'
`vtStB`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.B2C (cellJ)

@[expose] public section

/-! ## The proof stream's reads -/

/-- The read `c` words past the cursor in cell `o`, inside the stream `st·[0, 8192)`. -/
def stRes (o : ℕ) (st : Mode.Base) (c : ℕ) : Mode.Res :=
  .sub ⟨⟨0, c, [(.fr o, 1)]⟩, .num 0, .num 1, 1, 0⟩ [⟨⟨0, 0, [(st, 1)]⟩, .num 0, .num 8192, 1, 0⟩]

end

end LeanVM.Guest.Res
