/-
  LeanVM.Guest.B1.Main.AggAtT

  `aggregate_claims`' tree of honest shape (`Budget.NodeHonest`): its node at a valuation holding
  the children's count `g^m` and its buffers' sizes, its calls and `HeapBuf`s `aggCallList`,
  `aggSizes m`.
-/

module

public import LeanVM.Guest.B1.Main.AggAt
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims»

/-!
# `aggregate_claims`, its tree exposed

`aggQ m`: the children's count `g^m` (`n_children_g`) and the sizes' words.
`aggCallList`: its four calls, every one entered. `aggHonest m`: its honest shape, no predicate on
its callees' trees.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT Returns Kid OutsOk CallsMatch RegionsOk outRegion
  DisjL Within disj_append disj_nil kidsFromInT_of_kidsDT completeAt_of_rel_pureD regionsOk_of
  within_append bufL bufL_within bufL_disj bufL_region)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- `aggregate_claims`' honest words: the children's count, its buffers' sizes. -/
def aggQ (m : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «aggregate_claims» "n_children_g")) = gen ^ m ∧ σ (.n (val% «aggregate_claims» "absorb~6")) = gen ^ (13 * (m + 1)) ∧ σ (.n (val% «aggregate_claims» "bc_chain~2")) = gen ^ (2 * (m + 1)) ∧
    σ (.n (val% «aggregate_claims» "bc_wsum~1")) = gen ^ (m + 1)

/-- `aggregate_claims`' calls, in order. -/
def aggCallList : List Call :=
  [⟨name% «aggregate_claims_loop0», [.n (val% «aggregate_claims» "s12#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "absorb"), .n (val% «aggregate_claims» "child_fresh"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "child_carried"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "child_pi")], [], true⟩,
    ⟨name% «aggregate_claims_loop1», [.n (val% «aggregate_claims» "s22#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "bc_chain"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "lam_sq"), .n (val% «aggregate_claims» "fs_perm.nxt[0]")], [], true⟩,
    ⟨"batch_sumcheck__L23", [.n (val% «aggregate_claims» "fs_perm.nxt[8]"), .n (val% «aggregate_claims» "fs_perm.nxt[9]"), .n (val% «aggregate_claims» "fs_perm.nxt[10]"), .n (val% «aggregate_claims» "fs_perm.nxt[11]"), .n (val% «aggregate_claims» "fs_perm.nxt[12]"), .n (val% «aggregate_claims» "fs0~7"), .n (val% «aggregate_claims» "bc_running@1"), .n (val% «aggregate_claims» "bc_point"), .n (val% «aggregate_claims» "tabs")],
      [.n (val% «aggregate_claims» "fs0"), .n (val% «aggregate_claims» "fs1"), .n (val% «aggregate_claims» "fs2"), .n (val% «aggregate_claims» "fs3"), .n (val% «aggregate_claims» "fs4"), .n (val% «aggregate_claims» "bc_running@2")], true⟩,
    ⟨name% «aggregate_claims_loop2», [.n (val% «aggregate_claims» "s31#2"), .n (val% «aggregate_claims» "n_children_g"), .n (val% «aggregate_claims» "fresh_row"), .n (val% «aggregate_claims» "carried_row"), .n (val% «aggregate_claims» "bc_point1"), .n (val% «aggregate_claims» "bc_chain"), .n (val% «aggregate_claims» "bc_wsum"), .n (val% «aggregate_claims» "fs_perm.nxt[0]")], [],
        true⟩]

/-- No predicate on `aggregate_claims`' callees' trees. -/
def aggTs : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, fun _ => True]

/-- **`aggregate_claims`' honest shape** on `m` children. -/
def aggHonest (m : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "aggregate_claims" (aggQ m) (fun _ => aggCallList) (fun _ => aggSizes m) aggTs

end
end LeanVM.Guest.B1.Main
