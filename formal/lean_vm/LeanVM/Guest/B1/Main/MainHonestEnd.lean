/-
  LeanVM.Guest.B1.Main.MainHonestEnd

  Facts of a node's honest run that `main`'s placed completeness reads: the bytecode's log, the
  children's fresh claims' shape, and each child's `verify_sub` call as a goal.
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.B1.Main.MainHonestFit
public import LeanVM.Guest.B1.Main.MainGoalsF
public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Main.MainGoalsHL5
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run, its callees discharged

`log2_of_length`: a bytecode of `2^23` words has log `23`. `freshShaped_of`: the children's fresh
claims have `23` coordinates. `VerifySubGoals`: each child's `verify_sub` call complete at the words
`main`'s children's loop passes it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

theorem log2_of_length (hbl : bytecode.length = 2 ^ 23) : Nat.log2 bytecode.length = 23 := by
  rw [hbl]; exact Nat.log2_two_pow

/-- **The children's fresh claims have `23` coordinates** (`kid_shapes`). -/
theorem freshShaped_of (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) :
    FreshShaped w := fun c hc => (kid_shapes hbl hr c hc).1

/-- **Each child's `verify_sub` on the honest run**, at the words `main`'s children's loop passes
it (B1-d's `verify_sub` completeness, per honest child). -/
def VerifySubGoals (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  ∀ c (hc : c < w.children.length), CompleteAtD fs cert 20 "verify_sub" (hLmain fs fp seed s w)
    [(digestHalves (statementDigest seed w.children[c].statement)).1,
      (digestHalves (statementDigest seed w.children[c].statement)).2,
      (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
      (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns [])

end
end LeanVM.Guest.B1.Main
