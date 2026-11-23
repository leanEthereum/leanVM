/-
  LeanVM.Guest.CoreMode.WitOf

  Runs of consecutive witnesses, as generated heap certificates write them (`scripts/core-mode/emitc.py`'s `lwits`):
  `evR a n` the write events `a` to `a + n - 1`, `runR a n` the runs `a` to `a + n - 1` with no residual.
-/

module

public import LeanVM.Guest.CoreMode.Defs

namespace LeanVM.Guest.CoreMode

@[expose] public section

/-- The write events `a`, `a + 1`, …, `n` of them. -/
def evR (a : ℕ) : ℕ → List Wit
  | 0 => []
  | n + 1 => .ev a :: evR (a + 1) n

/-- The runs `a`, `a + 1`, …, `n` of them, each with no residual. -/
def runR (a : ℕ) : ℕ → List Wit
  | 0 => []
  | n + 1 => .run a [] :: runR (a + 1) n

end

end LeanVM.Guest.CoreMode
