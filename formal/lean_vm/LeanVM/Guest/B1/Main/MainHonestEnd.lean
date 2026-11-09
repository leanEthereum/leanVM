/-
  LeanVM.Guest.B1.Main.MainHonestEnd

  `main` placed on a node's honest run, its callees discharged: the list, digest and loop callees
  (`MainGoalsF`), the raw signatures' and the direct DA claim's (`MainGoalsG`), the children's
  loop and the aggregation taken as hypotheses.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestAt
public import LeanVM.Guest.B1.Main.MainGoalsFCl
public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Main.MainGoalsHL5
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run, its callees discharged

`mainGoals_of`: `MainGoals` from `NodeRelation`, `Limits`, a bytecode of `2^23` words, the signature
schemes' completeness (B1-e), and the direct DA check, the children's loop and aggregation
(`MainGoalDv`, `MainGoalL5`, `MainGoalAg`). `main_honest_end`:
`main_honest_relAtInW` on those.
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

/-- **`main`'s callees on the honest run**, but the children's loop and the aggregation. -/
theorem mainGoals_of (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w)
    (hl : DeployedLimits s w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs)
    (hdv : MainGoalDv fs cert fp seed s w) (hl5 : MainGoalL5 fs cert fp seed s w)
    (hag : MainGoalAg fs cert fp seed s w) : MainGoals fs cert fp seed s w where
  clx := mainGoalClX fs cert fp seed s w hl
  cls := mainGoalClS fs cert fp seed s w hl
  l1 := mainGoalL1 fs cert fp seed s w
  l2 := mainGoalL2 fs cert fp seed s w
  l3 := mainGoalL3 (fs := fs) (cert := cert) (fp := fp) hr hl hxc
  l4 := mainGoalL4 (fs := fs) (cert := cert) (fp := fp) hr hl hsc
  dv := hdv
  l5 := hl5
  ag := hag
  st := mainGoalSt fs cert fp seed s w hr hbl

/-- **Each child's `verify_sub` on the honest run**, at the words `main`'s children's loop passes
it (B1-d's `verify_sub` completeness, per honest child). -/
def VerifySubGoals (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : Prop :=
  ∀ c (hc : c < w.children.length), CompleteAtD fs cert 16 "verify_sub" (hLmain fs fp seed s w)
    [(digestHalves (statementDigest seed w.children[c].statement)).1,
      (digestHalves (statementDigest seed w.children[c].statement)).2,
      (digestHalves seed).1, (digestHalves seed).2, (hm fs fp seed s w).et,
      (hm fs fp seed s w).a400 * gen ^ (24 * c)] (Returns [])

end
end LeanVM.Guest.B1.Main
