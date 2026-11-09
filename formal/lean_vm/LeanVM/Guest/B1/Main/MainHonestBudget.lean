/-
  LeanVM.Guest.B1.Main.MainHonestBudget

  `main`'s completeness on a node's honest run, its callees' trees of honest shape where the
  budget needs them: its claim lists' digests (`clHonest`), each child's (`ccHonest`),
  `aggregate_claims` (`aggHonest`); `da_verify`'s and each `verify_sub`'s by given predicates.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestFull
public import LeanVM.Guest.B1.Main.MainGoalsHClT
public import LeanVM.Guest.B1.Main.MainGoalsHAgT
public import LeanVM.Guest.B1.Main.MainGoalsDvT

/-!
# `main` on an honest run, for the budget

`mainPredsH w Pd Pvs`: `main`'s callees' predicates, of honest shape on its claim lists' digests,
each child's and `aggregate_claims`; `Pd` on `da_verify`'s, `Pvs c` on child `c`'s
`verify_sub`'s. `main_honest_budget`: `main_honest_fullT` with those.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDT Returns)

@[expose] public section

/-- **`main`'s callees' predicates for the budget.** -/
def mainPredsH (s : NodeStatement) (w : NodeWitness) (Pd : Tree → Prop) (Pvs : ℕ → Tree → Prop) :
    MainPreds :=
  ⟨clHonest s.claims.xmss.length, clHonest s.claims.sphincs.length, Pd, aggHonest w.children.length,
    L5Hinted w (fun c => ccHonest (hKid s w c).ex) (fun c => ccHonest (hKid s w c).es) Pvs⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

end
end LeanVM.Guest.B1.Main
