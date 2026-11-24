/-
  LeanVM.Guest.B1.Main.MainGoalsDvT

  `main`'s `da_verify` on an honest run, by a tree of its honest shape (`Da.dvNH`) at the direct DA
  witness's row count and padded log.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.AcceptableChild

/-!
# `da_verify` on an honest run, its honest shape

`hDvNH w`: `da_verify`'s honest shape on the directly held DA claim's witness (no constraint
without one).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Coverage (coveragePlan)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

/-- **`da_verify`'s honest shape on the checked DA claim's witness.** -/
def hDvNH (w : NodeWitness) : Tree → Prop :=
  (w.daMatrix.map fun p => Da.dvNH p.2.rows.length (wLog p.2)).getD fun _ => True

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ)

end
end LeanVM.Guest.B1.Main
