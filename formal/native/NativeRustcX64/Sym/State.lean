module

public import NativeRustcX64.Sym.Types
meta import Lean.Elab.Deriving.ToExpr

/-!
# Symbolic states

The decidable equality of symbolic values and booleans, the symbolic flags `SFlags`, writes
`Write`, states `Sym.SState` and how a block ends, `Sym.Exit`.
-/

namespace NativeRustcX64

@[expose] public section

deriving instance DecidableEq for Sym, SBool

/-- Symbolic CF, ZF, SF and OF; `none` is unknown (PF and AF are always unknown). -/
structure SFlags where
  cf : Option SBool
  zf : Option SBool
  sf : Option SBool
  of : Option SBool
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A symbolic write: the low `n` bytes of `v` at offset `off` of region `r`. -/
structure Write where
  r : Nat
  off : Nat
  n : Nat
  v : Sym
  deriving DecidableEq, Repr, Lean.ToExpr

namespace Sym

/-- A symbolic machine state. A register `none` is unknown. -/
structure SState where
  /-- RAX to R15, in `Reg64`'s order. -/
  regs : List (Option Sym)
  flags : SFlags
  /-- The writes into the regions, newest first. -/
  mem : List Write
  /-- Each region's size. -/
  regions : List Nat
  /-- Labels whose address is a region's base (read-only data the code reaches RIP-relative). -/
  labels : List (Label × Nat) := []
  /-- Facts `(x, B)`: `x`'s value is below `B`; they bound indexed accesses. -/
  bounds : List (Sym × Nat) := []
  /-- Facts `(x, (r, o))`: `x`'s value is region `r`'s base plus `o` (an address the code computes
  from an index, e.g. `rsi + rcx`). -/
  aliases : List (Sym × Nat × Int) := []
  /-- Symbolic descriptions of initial memory, independent of the actual writes in `mem`. -/
  known : List Write := []
  deriving DecidableEq, Repr, Lean.ToExpr

/-- How a block ends. -/
inductive Exit
  /-- It falls through to the next directive. -/
  | fall
  /-- `jmp l`. -/
  | jump (l : Label)
  /-- A conditional jump to `l`, taken when `c` holds. -/
  | cond (c : SBool) (l : Label)
  /-- `call l`: the return address pushed. -/
  | call (l : Label)
  /-- `ret` to the address `a` it popped. -/
  | ret (a : Sym)
  deriving DecidableEq, Repr, Lean.ToExpr

end Sym

end

end NativeRustcX64
