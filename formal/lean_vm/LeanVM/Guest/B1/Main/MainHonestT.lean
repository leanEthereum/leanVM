/-
  LeanVM.Guest.B1.Main.MainHonestT

  The predicates on `main`'s callees' trees on a node's honest run.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestEnd
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings

/-!
# The predicates on `main`'s callees' trees

`MainPreds`: the predicates on `main`'s claim lists' digests, `da_verify`'s, `aggregate_claims`'
and the children's loop's trees. `mTs m p`: those predicates aligned with `mKids`, none on the
others'.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within Kid CompleteAtD CompleteAtDT KidsDT Returns)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The predicates on `main`'s callees' trees**: on its claim lists' digests (`Px`, `Ps`),
`da_verify`'s (`Pd`), `aggregate_claims`' (`Pa`), the children's loop's (`T5`). -/
structure MainPreds where
  Px : Tree → Prop
  Ps : Tree → Prop
  Pd : Tree → Prop
  Pa : Tree → Prop
  T5 : Tree → Prop

/-- **The predicates on `main`'s callees' trees**, aligned with `mKids`. -/
def mTs (m : MainIn) (p : MainPreds) : List (Tree → Prop) :=
  [p.Px, p.Ps, fun _ => True, fun _ => True, fun _ => True, fun _ => True] ++
    (if m.nd = 1 then [p.Pd] else []) ++ [p.T5] ++
    (if m.nc = 0 then [] else [p.Pa]) ++ [fun _ => True]

variable {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {bytecode : List K}

end
end LeanVM.Guest.B1.Main
