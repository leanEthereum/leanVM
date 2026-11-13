/-
  LeanVM.Guest.Executor

  The guest's execution on a node, computed from its statement and witness alone.
-/

module

public import Statement.Prover.Execute
public import LeanVM.Prover.Advice
public import LeanVM.Guest.Data.Advice
public import LeanVM.Guest.Hints
public import LeanVM.Facts.Guest

/-!
# The guest's execution

`guestAdvice seed s w` is the compiler's hints (`Data.adviceText`) with the honest witness streams
(`Hints.honestStreams`); `guestExecution seed s w` runs the guest on the statement's digest with it
(`Exec.execute`). The honest streams read the bytecode only through its length, `2^23` words.
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Prover LeanVM.Prover.Exec

/-- The bytecode's words as the honest streams read them: its length. -/
def bytecodeShape : List K := List.replicate (2 ^ 23) 0

/-- The guest's advice on a node. -/
def guestAdvice (seed : Digest) (s : NodeStatement) (w : NodeWitness) : Except String Advice := do
  let a ← parseAdvice Data.adviceText
  pure { a with streams := Hints.honestStreams bytecodeShape seed s w }

/-- **The guest's execution on a node**, or where it stops. -/
def guestExecution (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Except String (Execution guestProgram) := do
  let adv ← guestAdvice seed s w
  match execute guestProgram (End.publicInputOf (statementDigest seed s)) adv with
  | .ok t => pure t
  | .error (pc, _) => throw s!"the guest stops at pc {pc}"

end LeanVM.Guest
