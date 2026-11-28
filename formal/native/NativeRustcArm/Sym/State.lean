module

public import NativeRustcArm.Sym.Types
meta import Lean.Elab.Deriving.ToExpr

/-!
# Symbolic states

The decidable equality of symbolic values and booleans, the symbolic flags `SFlags`, writes
`Write`, states `Sym.SState` and how a block ends, `Sym.Exit`.
-/

namespace NativeRustcArm

@[expose] public section

deriving instance DecidableEq for Sym, SBool

/-- Symbolic NZCV flags. -/
structure SFlags where
  n : SBool
  z : SBool
  c : SBool
  v : SBool
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A symbolic write: the low `n` bytes of `v` at offset `off` of region `r`. -/
structure Write where
  r : Nat
  off : Nat
  n : Nat
  v : Sym
  deriving DecidableEq, Repr, Lean.ToExpr

namespace Sym

/-- A symbolic machine state. A register or the flags `none` are unknown. -/
structure SState where
  /-- X0 to X30. -/
  regs : List (Option Sym)
  sp : Sym
  flags : Option SFlags
  /-- The writes into the regions, newest first. -/
  mem : List Write
  /-- Each region's size and whether its base is 16-byte aligned. -/
  regions : List (Nat × Bool)
  /-- Labels whose address is a region's base (read-only data the code reaches by `ADRP`). -/
  labels : List (Label × Nat) := []
  /-- Facts `(x, B)`: `x`'s value is below `B`; they bound indexed accesses. -/
  bounds : List (Sym × Nat) := []
  /-- Facts `(x, (r, o))`: `x`'s value is region `r`'s base plus `o` (an address the code computes
  from an index, e.g. `x0 + x8`). -/
  aliases : List (Sym × Nat × Int) := []
  deriving DecidableEq, Repr, Lean.ToExpr

/-- How a block ends. -/
inductive Exit
  /-- It falls through to the next directive. -/
  | fall
  /-- `b l`. -/
  | jump (l : Label)
  /-- A conditional branch to `l`, taken when `c` holds. -/
  | cond (c : SBool) (l : Label)
  /-- `bl l`. -/
  | call (l : Label)
  /-- `ret`. -/
  | ret
  deriving DecidableEq, Repr, Lean.ToExpr

end Sym

end

end NativeRustcArm
