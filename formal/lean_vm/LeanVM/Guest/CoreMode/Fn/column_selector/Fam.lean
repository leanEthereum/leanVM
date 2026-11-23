/-
  LeanVM.Guest.CoreMode.Fn.column_selector.Fam

  `column_selector`'s own residual families (`CoreMode/FnReg.lean`): its lowest digit's read in its strided table.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«column_selector__L»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`column_selector__L{κ}`'s lowest digit in its strided table** (F3 on names): the cell
`[sel_eq]·[digit₀]·g^off` one of the run `⟨[sel_eq]·g^off, 2^(4-w), 0, 2^w⟩`, `w` the digit's width,
`sel_eq` its parameter and `digits[0]` its lowest digit. -/
def csSub (κ : ℕ) : CRes :=
  .sub ⟨[(valf% «column_selector» "sel_eq", 1), (valf% «column_selector» "digits[0]", 1)], 32 * (κ / 4) + B1.Tables.selEqOff (B1.Tables.csW κ 0 - 1)⟩
    ⟨⟨[(valf% «column_selector» "sel_eq", 1)], 32 * (κ / 4) + B1.Tables.selEqOff (B1.Tables.csW κ 0 - 1)⟩, 2 ^ (4 - B1.Tables.csW κ 0), .num 0,
      .num (2 ^ B1.Tables.csW κ 0)⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.column_selector

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: `column_selector__L{κ}`'s lowest digit's read (`csSub κ`), `κ < 31`. -/
def fams : List (String × (Fn → CRes → Bool)) :=
  (List.range 31).map fun κ ↦ (B1.Tables.lName "column_selector" κ, fun _ r ↦ decide (r = csSub κ))

end

end LeanVM.Guest.CoreMode.Own.column_selector
