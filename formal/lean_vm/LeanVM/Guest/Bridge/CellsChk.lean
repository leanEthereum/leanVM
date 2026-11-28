/-
  LeanVM.Guest.Bridge.CellsChk

  The frame cells the hints write: within their function's frame, decided by the kernel over every
  compiled function.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.ProgAlData
public import LeanVM.Guest.EndExecCUsed
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# The frame cells the hints write

`cellsChk F fs`: every hint of `F`'s advice passes `hintCellsOk fs` (each frame cell it writes below
the frame size `fs`). `cellsChk_all`: every compiled function's advice passes it at its frame size
`B2C.fsN j`, the bus era's check, by the kernel.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest

@[expose] public section

/-- Every hint of a function's advice writes its frame cells within `fs`. -/
noncomputable def cellsChk (F : FnAl) (fs : ℕ) : Bool := F.d.2.2.all fun p ↦ p.2.all (hintCellsOk fs)

end

public section

theorem cellsChk_0 : ∀ j < 400, cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_1 : ∀ j < 800, 400 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_2 : ∀ j < 1200, 800 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_3 : ∀ j < nFns, 1200 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

/-- **Every compiled function's hints write their frame cells within its frame.** -/
theorem cellsChk_all (j : ℕ) (h : j < nFns) : cellsChk (fnAl j) (B2C.fsN j) = true := by
  rcases Nat.lt_or_ge j 400 with h0 | h0
  · exact cellsChk_0 j h0
  rcases Nat.lt_or_ge j 800 with h1 | h1
  · exact cellsChk_1 j h1 h0
  rcases Nat.lt_or_ge j 1200 with h2 | h2
  · exact cellsChk_2 j h2 h1
  · exact cellsChk_3 j h h2

end

end LeanVM.Guest.Bridge
