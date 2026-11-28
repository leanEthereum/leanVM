/-
  LeanVM.Guest.CoreMode.Fn.link_rounds.Data

  `link_rounds`' own routing data (`CoreMode/FnReg.lean`): its loops read the proof stream past their records' cursors.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.link_rounds

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its loops are cursor-run loops** (`CoreMode.stLoops`): `link_rounds__L{t}_L{b}_loop0`'s reads lie in the
`W = t + 1 + [b > 0]` residue runs past its caller's `cursor` (frame cell `7`) below the exponent of its `count_g` (frame
cell `10`), its record's cursor its value `18`, `4W` words read past it an iteration. -/
def stLoops : List (String × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(name% «link_rounds__L1_L0_loop0», 7, 10, 2, 18, 8),
    (name% «link_rounds__L6_L0_loop0», 7, 10, 7, 18, 28),
    (name% «link_rounds__L7_L0_loop0», 7, 10, 8, 18, 32),
    (name% «link_rounds__L8_L1_loop0», 7, 10, 10, 18, 40),
    (name% «link_rounds__L9_L1_loop0», 7, 10, 11, 18, 44),
    (name% «link_rounds__L10_L1_loop0», 7, 10, 12, 18, 48)]

/-- **Its loops' callers** (`Res.termCallers`): each its specialization, and itself. -/
def stCallers : List (String × String) :=
  [(name% «link_rounds__L1_L0_loop0», name% «link_rounds__L1_L0»),
    (name% «link_rounds__L6_L0_loop0», name% «link_rounds__L6_L0»),
    (name% «link_rounds__L7_L0_loop0», name% «link_rounds__L7_L0»),
    (name% «link_rounds__L8_L1_loop0», name% «link_rounds__L8_L1»),
    (name% «link_rounds__L9_L1_loop0», name% «link_rounds__L9_L1»),
    (name% «link_rounds__L10_L1_loop0», name% «link_rounds__L10_L1»)]

end

end LeanVM.Guest.CoreMode.Own.link_rounds
