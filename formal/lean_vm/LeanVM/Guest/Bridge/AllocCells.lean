/-
  LeanVM.Guest.Bridge.AllocCells

  The frame cells the hints write: within their function's frame, decided by the kernel over every
  compiled function.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Bridge.ProgAlData
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# The frame cells the hints write

`hintCellsOk fs h`: each frame cell hint `h` writes (an allocation's or a cell address's pointer
cell, a stack run, a destination cell, a stack destination's run) is below the frame size `fs`.
`cellsChk_all`: every compiled function's hints pass it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest

@[expose] public section

/-- A destination's run of `n` cells within the frame, when on the stack. -/
def dstCellsOk (fs : ℕ) : Prover.Exec.BitsDest → ℕ → Bool
  | .stack base, n => decide (base + n ≤ fs)
  | .heap _, _ => true

/-- **The frame cells a hint writes are below the frame size.** -/
def hintCellsOk (fs : ℕ) : Prover.Exec.Hint → Bool
  | .alloc p _ | .allocDyn p _ | .allocArm p _ _ | .cellAddress p _
  | .allocFrames p _ _ _ => decide (p < fs)
  | .witnessStack _ base len => decide (base + len ≤ fs)
  | .log2Ceil _ dst _ _ => decide (dst < fs)
  | .bitDecompose _ d n | .bitDecomposeExp _ d n => dstCellsOk fs d n
  | .windowsExp _ d pos _ _ count => dstCellsOk fs d (pos + count)
  | .digitDecomposeExp _ d _ ndigits _ _ _ => dstCellsOk fs d ndigits
  | .fieldLimbs _ base len => decide (base + len ≤ fs)
  | .inverse _ dst => decide (dst < fs)
  | .frameAddress _ | .witnessHeap .. => true

/-- Every hint of a function's advice writes its frame cells within `fs`. -/
noncomputable def cellsChk (F : FnAl) (fs : ℕ) : Bool := F.d.2.2.all fun p ↦ p.2.all (hintCellsOk fs)

end

public section

theorem cellsChk_0 : ∀ j < 400, cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_1 : ∀ j < 800, 400 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_2 : ∀ j < 1200, 800 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_3 : ∀ j < nFns, 1200 ≤ j → cellsChk (fnAl j) (B2C.fsN j) = true := by decide +kernel

theorem cellsChk_all (j : ℕ) (h : j < nFns) : cellsChk (fnAl j) (B2C.fsN j) = true := by
  have : nFns = fn_count% := rfl
  rcases Nat.lt_or_ge j 400 with h0 | h0
  · exact cellsChk_0 j h0
  rcases Nat.lt_or_ge j 800 with h1 | h1
  · exact cellsChk_1 j h1 h0
  rcases Nat.lt_or_ge j 1200 with h2 | h2
  · exact cellsChk_2 j h2 h1
  · exact cellsChk_3 j h h2

end

end LeanVM.Guest.Bridge
