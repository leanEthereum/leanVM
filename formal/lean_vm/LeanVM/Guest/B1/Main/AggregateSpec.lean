/-
  LeanVM.Guest.B1.Main.AggregateSpec

  The meaning of `aggregate_claims` (G:3319-3486; TRIAGE #77): `Node.batch` of the claims its
  three buffers hold.
-/

module

public import LeanVM.Guest.B1.Main.Callees

/-!
# `aggregate_claims`, the statement

`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)` reads child
`c`'s public input at `child_pi·g^(2c)`, its fresh claims at `child_fresh·g^(106c)` and its
carried claim at `child_carried·g^(53c)` (`ChildClaimsAt`), and stores at `defer_stmt` the claim
`Node.batch` defers for them.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The children's claims at the three buffers: child `c`'s public input's two cells at
`pis·g^(2c)`, its fresh claims of the guest's shape at `fresh·g^(106c)`, its carried claim of the
guest's shape at `carried·g^(53c)`. -/
def ChildClaimsAt (rd : Reader) (pis fresh carried : E) (cs : List ChildClaims) : Prop :=
  ∀ c (h : c < cs.length),
    LoadHolds rd pis (2 * c) (digestScalars cs[c].publicInput).1 ∧
    LoadHolds rd pis (2 * c + 1) (digestScalars cs[c].publicInput).2 ∧
    FreshShaped cs[c].fresh ∧ ReadsAt rd (fresh * gen ^ (106 * c)) (fixedCells cs[c].fresh) ∧
    cs[c].carried.bytecodePoint.length = 22 ∧ cs[c].carried.matrixPoint.length = 28 ∧
    ReadsAt rd (carried * gen ^ (53 * c)) cs[c].carried.cells

/-- **`aggregate_claims`** (G:3319-3486; TRIAGE #77): for the nonempty claims `cs` its buffers
hold, at most `16` and `n_children_g = g^|cs|`, the batching closes (`Node.batch`, N:261, with
hints of `22` and `28` rounds) on a claim of the guest's shape, stored at `defer_stmt`. -/
def Meaning_aggregate_claims (rd : Reader) (args rets : List E) : Prop :=
  ∃ n_g pis fresh carried dp, args = [n_g, pis, fresh, carried, dp] ∧ rets = [] ∧
    ∀ cs : List ChildClaims, cs ≠ [] → cs.length ≤ 16 → n_g = gen ^ cs.length →
      ChildClaimsAt rd pis fresh carried cs →
      ∃ (h : BatchHints) (d : DeferredClaim), batch cs h = some d ∧
        d.bytecodePoint.length = 22 ∧ d.matrixPoint.length = 28 ∧ ReadsAt rd dp d.cells

end
end LeanVM.Guest.B1.Main
