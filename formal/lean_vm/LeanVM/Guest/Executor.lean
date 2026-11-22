/-
  LeanVM.Guest.Executor

  The guest's execution on a node, computed from its statement and witness alone.
-/

module

public import Statement.Prover.Execute
public import Statement.Data.AdviceHints
public import LeanVM.Guest.Hints
public import LeanVM.Facts.Guest

/-!
# The guest's execution

`honestAdvice seed s w` is `main`'s frame size and the compiler's hints by pc, as data
(`Data.adviceMainFrame`, `Data.adviceHints`, `Statement/Data/AdviceHints*.lean`: the text
`Data.adviceText` that `guest-export` writes, which `tests/LeanVMTests/Guest/AdviceData.lean` checks
against its parse), with the honest witness streams (`Hints.honestStreams`); `honestExecution seed s
w` runs the guest on the statement's digest with it (`Exec.execute`). The honest streams read the
bytecode only through its length, `2^23` words. The proofs are about these; `Statement/`'s
`guestAdvice` is the same advice (`EndExec.prover_guestAdvice_eq`).
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Prover LeanVM.Prover.Exec

/-- The bytecode's words as the honest streams read them: its length. -/
def bytecodeShape : List K := List.replicate (2 ^ 23) 0

/-- The guest's advice on a node. -/
def honestAdvice (seed : Digest) (s : NodeStatement) (w : NodeWitness) : Advice :=
  ⟨Data.adviceMainFrame, Data.adviceHints, Hints.honestStreams bytecodeShape seed s w⟩

/-- **The guest's execution on a node**, or where it stops. -/
def honestExecution (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Except String (Execution guestProgram) :=
  match execute guestProgram (End.publicInputOf (statementDigest seed s)) (honestAdvice seed s w) with
  | .ok t => pure t
  | .error (pc, _) => throw s!"the guest stops at pc {pc}"

/-- `honestExecution` is the executor's execution. -/
theorem honestExecution_of_execute {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    {t : Execution guestProgram}
    (h : execute guestProgram (End.publicInputOf (statementDigest seed s)) (honestAdvice seed s w) = .ok t) :
    honestExecution seed s w = .ok t := by
  unfold honestExecution
  rw [h]
  rfl

end LeanVM.Guest
