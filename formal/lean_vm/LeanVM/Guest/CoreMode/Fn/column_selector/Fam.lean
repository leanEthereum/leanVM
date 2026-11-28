/-
  LeanVM.Guest.CoreMode.Fn.column_selector.Fam

  `column_selector`'s own residual families (`CoreMode/FnReg.lean`): its lowest digit's read in its strided table.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`column_selector__L{n}_L{κ}`'s lowest digit in its strided table**: the cell `[sel_eq]·[digit₀]·g^off`, its
parameter `sel_eq` (value `1`) and its lowest digit (value `3`), one of the run
`⟨[sel_eq]·g^off, 2^(κ % 4), 0, 2^(4 - κ % 4)⟩`, `off = 32 (κ / 4) + B1.Stack.selOff (3 - κ % 4)` (the level of the digit's
width `4 - κ % 4`, `B1.Stack.cselDigit`). -/
def csSub (κ : ℕ) : CRes :=
  .sub ⟨[(1, 1), (3, 1)], 32 * (κ / 4) + [4, 2, 1, 16].getD (3 - κ % 4) 0⟩
    ⟨⟨[(1, 1)], 32 * (κ / 4) + [4, 2, 1, 16].getD (3 - κ % 4) 0⟩, 2 ^ (κ % 4), .num 0, .num (2 ^ (4 - κ % 4))⟩

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.column_selector

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Its specializations with a digit, `column_selector__L{n}_L{κ}`, `κ < 4n`, with their `n` and `κ`. -/
def csNames : List (String × ℕ × ℕ) :=
  [(name% «column_selector__L4_L0», 4, 0),
    (name% «column_selector__L4_L1», 4, 1),
    (name% «column_selector__L4_L2», 4, 2),
    (name% «column_selector__L4_L3», 4, 3),
    (name% «column_selector__L4_L4», 4, 4),
    (name% «column_selector__L4_L5», 4, 5),
    (name% «column_selector__L4_L6», 4, 6),
    (name% «column_selector__L4_L7», 4, 7),
    (name% «column_selector__L4_L8», 4, 8),
    (name% «column_selector__L4_L9», 4, 9),
    (name% «column_selector__L4_L10», 4, 10),
    (name% «column_selector__L4_L11», 4, 11),
    (name% «column_selector__L4_L12», 4, 12),
    (name% «column_selector__L4_L13», 4, 13),
    (name% «column_selector__L4_L14», 4, 14),
    (name% «column_selector__L4_L15», 4, 15),
    (name% «column_selector__L5_L0», 5, 0),
    (name% «column_selector__L5_L1», 5, 1),
    (name% «column_selector__L5_L2», 5, 2),
    (name% «column_selector__L5_L3», 5, 3),
    (name% «column_selector__L5_L4», 5, 4),
    (name% «column_selector__L5_L5», 5, 5),
    (name% «column_selector__L5_L6», 5, 6),
    (name% «column_selector__L5_L7», 5, 7),
    (name% «column_selector__L5_L8», 5, 8),
    (name% «column_selector__L5_L9», 5, 9),
    (name% «column_selector__L5_L10», 5, 10),
    (name% «column_selector__L5_L11», 5, 11),
    (name% «column_selector__L5_L12», 5, 12),
    (name% «column_selector__L5_L13», 5, 13),
    (name% «column_selector__L5_L14», 5, 14),
    (name% «column_selector__L5_L15», 5, 15),
    (name% «column_selector__L5_L16», 5, 16),
    (name% «column_selector__L5_L17», 5, 17),
    (name% «column_selector__L5_L18», 5, 18),
    (name% «column_selector__L5_L19», 5, 19),
    (name% «column_selector__L6_L0», 6, 0),
    (name% «column_selector__L6_L1», 6, 1),
    (name% «column_selector__L6_L2», 6, 2),
    (name% «column_selector__L6_L3», 6, 3),
    (name% «column_selector__L6_L4», 6, 4),
    (name% «column_selector__L6_L5», 6, 5),
    (name% «column_selector__L6_L6», 6, 6),
    (name% «column_selector__L6_L7», 6, 7),
    (name% «column_selector__L6_L8», 6, 8),
    (name% «column_selector__L6_L9», 6, 9),
    (name% «column_selector__L6_L10», 6, 10),
    (name% «column_selector__L6_L11», 6, 11),
    (name% «column_selector__L6_L12», 6, 12),
    (name% «column_selector__L6_L13», 6, 13),
    (name% «column_selector__L6_L14», 6, 14),
    (name% «column_selector__L6_L15», 6, 15),
    (name% «column_selector__L6_L16», 6, 16),
    (name% «column_selector__L6_L17», 6, 17),
    (name% «column_selector__L6_L18», 6, 18),
    (name% «column_selector__L6_L19», 6, 19),
    (name% «column_selector__L6_L20», 6, 20),
    (name% «column_selector__L6_L21», 6, 21),
    (name% «column_selector__L6_L22», 6, 22),
    (name% «column_selector__L6_L23», 6, 23),
    (name% «column_selector__L7_L0», 7, 0),
    (name% «column_selector__L7_L1», 7, 1),
    (name% «column_selector__L7_L2», 7, 2),
    (name% «column_selector__L7_L3», 7, 3),
    (name% «column_selector__L7_L4», 7, 4),
    (name% «column_selector__L7_L5», 7, 5),
    (name% «column_selector__L7_L6», 7, 6),
    (name% «column_selector__L7_L7», 7, 7),
    (name% «column_selector__L7_L8», 7, 8),
    (name% «column_selector__L7_L9», 7, 9),
    (name% «column_selector__L7_L10», 7, 10),
    (name% «column_selector__L7_L11», 7, 11),
    (name% «column_selector__L7_L12», 7, 12),
    (name% «column_selector__L7_L13», 7, 13),
    (name% «column_selector__L7_L14», 7, 14),
    (name% «column_selector__L7_L15», 7, 15),
    (name% «column_selector__L7_L16», 7, 16),
    (name% «column_selector__L7_L17», 7, 17),
    (name% «column_selector__L7_L18», 7, 18),
    (name% «column_selector__L7_L19», 7, 19),
    (name% «column_selector__L7_L20», 7, 20),
    (name% «column_selector__L7_L21», 7, 21),
    (name% «column_selector__L7_L22», 7, 22),
    (name% «column_selector__L7_L23», 7, 23),
    (name% «column_selector__L7_L24», 7, 24),
    (name% «column_selector__L7_L25», 7, 25),
    (name% «column_selector__L7_L26», 7, 26),
    (name% «column_selector__L7_L27», 7, 27),
    (name% «column_selector__L8_L0», 8, 0),
    (name% «column_selector__L8_L1», 8, 1),
    (name% «column_selector__L8_L2», 8, 2),
    (name% «column_selector__L8_L3», 8, 3),
    (name% «column_selector__L8_L4», 8, 4),
    (name% «column_selector__L8_L5», 8, 5),
    (name% «column_selector__L8_L6», 8, 6),
    (name% «column_selector__L8_L7», 8, 7),
    (name% «column_selector__L8_L8», 8, 8),
    (name% «column_selector__L8_L9», 8, 9),
    (name% «column_selector__L8_L10», 8, 10),
    (name% «column_selector__L8_L11», 8, 11),
    (name% «column_selector__L8_L12», 8, 12),
    (name% «column_selector__L8_L13», 8, 13),
    (name% «column_selector__L8_L14», 8, 14),
    (name% «column_selector__L8_L15», 8, 15),
    (name% «column_selector__L8_L16», 8, 16),
    (name% «column_selector__L8_L17», 8, 17),
    (name% «column_selector__L8_L18», 8, 18),
    (name% «column_selector__L8_L19», 8, 19),
    (name% «column_selector__L8_L20», 8, 20),
    (name% «column_selector__L8_L21», 8, 21),
    (name% «column_selector__L8_L22», 8, 22),
    (name% «column_selector__L8_L23», 8, 23),
    (name% «column_selector__L8_L24», 8, 24),
    (name% «column_selector__L8_L25», 8, 25),
    (name% «column_selector__L8_L26», 8, 26),
    (name% «column_selector__L8_L27», 8, 27),
    (name% «column_selector__L8_L28», 8, 28),
    (name% «column_selector__L8_L29», 8, 29),
    (name% «column_selector__L8_L30», 8, 30)]

/-- **Its family**: each specialization's lowest digit's read (`csSub κ`). -/
def fams : List (String × (Fn → CRes → Bool)) :=
  csNames.map fun p ↦ (p.1, fun _ r ↦ decide (r = csSub p.2.2))

end

end LeanVM.Guest.CoreMode.Own.column_selector
