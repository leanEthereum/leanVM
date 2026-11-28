/-
  LeanVM.Guest.CoreMode.Fn.link_rounds_last.Data

  `link_rounds_last`'s own routing data (`CoreMode/FnReg.lean`): its arms of `k > 0` rounds read the proof stream past
  their record's cursor.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.link_rounds_last

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its arms of `k > 0` rounds read past a cursor** (`CoreMode.stLoops`): `link_rounds_last__L{t}_L{b}_L{k}`'s reads
lie in the `W = t + 1 + [b > 0]` residue runs past its caller's `cursor` (`link_rounds`' frame cell `7`) below the
exponent of its `count_g` (frame cell `10`), its record's cursor its value `9`, `W·k` words read past it. -/
def stLoops : List (String × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(name% «link_rounds_last__L1_L0_L1», 7, 10, 2, 9, 2),
    (name% «link_rounds_last__L1_L0_L2», 7, 10, 2, 9, 4),
    (name% «link_rounds_last__L1_L0_L3», 7, 10, 2, 9, 6),
    (name% «link_rounds_last__L6_L0_L1», 7, 10, 7, 9, 7),
    (name% «link_rounds_last__L6_L0_L2», 7, 10, 7, 9, 14),
    (name% «link_rounds_last__L6_L0_L3», 7, 10, 7, 9, 21),
    (name% «link_rounds_last__L7_L0_L1», 7, 10, 8, 9, 8),
    (name% «link_rounds_last__L7_L0_L2», 7, 10, 8, 9, 16),
    (name% «link_rounds_last__L7_L0_L3», 7, 10, 8, 9, 24),
    (name% «link_rounds_last__L8_L1_L1», 7, 10, 10, 9, 10),
    (name% «link_rounds_last__L8_L1_L2», 7, 10, 10, 9, 20),
    (name% «link_rounds_last__L8_L1_L3», 7, 10, 10, 9, 30),
    (name% «link_rounds_last__L9_L1_L1», 7, 10, 11, 9, 11),
    (name% «link_rounds_last__L9_L1_L2», 7, 10, 11, 9, 22),
    (name% «link_rounds_last__L9_L1_L3», 7, 10, 11, 9, 33),
    (name% «link_rounds_last__L10_L1_L1», 7, 10, 12, 9, 12),
    (name% «link_rounds_last__L10_L1_L2», 7, 10, 12, 9, 24),
    (name% «link_rounds_last__L10_L1_L3», 7, 10, 12, 9, 36)]

/-- **Their callers** (`Res.termCallers`): each `link_rounds`' specialization. -/
def stCallers : List (String × String) :=
  [(name% «link_rounds_last__L1_L0_L1», name% «link_rounds__L1_L0»),
    (name% «link_rounds_last__L1_L0_L2», name% «link_rounds__L1_L0»),
    (name% «link_rounds_last__L1_L0_L3», name% «link_rounds__L1_L0»),
    (name% «link_rounds_last__L6_L0_L1», name% «link_rounds__L6_L0»),
    (name% «link_rounds_last__L6_L0_L2», name% «link_rounds__L6_L0»),
    (name% «link_rounds_last__L6_L0_L3», name% «link_rounds__L6_L0»),
    (name% «link_rounds_last__L7_L0_L1», name% «link_rounds__L7_L0»),
    (name% «link_rounds_last__L7_L0_L2», name% «link_rounds__L7_L0»),
    (name% «link_rounds_last__L7_L0_L3», name% «link_rounds__L7_L0»),
    (name% «link_rounds_last__L8_L1_L1», name% «link_rounds__L8_L1»),
    (name% «link_rounds_last__L8_L1_L2», name% «link_rounds__L8_L1»),
    (name% «link_rounds_last__L8_L1_L3», name% «link_rounds__L8_L1»),
    (name% «link_rounds_last__L9_L1_L1», name% «link_rounds__L9_L1»),
    (name% «link_rounds_last__L9_L1_L2», name% «link_rounds__L9_L1»),
    (name% «link_rounds_last__L9_L1_L3», name% «link_rounds__L9_L1»),
    (name% «link_rounds_last__L10_L1_L1», name% «link_rounds__L10_L1»),
    (name% «link_rounds_last__L10_L1_L2», name% «link_rounds__L10_L1»),
    (name% «link_rounds_last__L10_L1_L3», name% «link_rounds__L10_L1»)]

end

end LeanVM.Guest.CoreMode.Own.link_rounds_last
