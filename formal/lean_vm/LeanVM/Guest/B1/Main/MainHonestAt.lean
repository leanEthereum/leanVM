/-
  LeanVM.Guest.B1.Main.MainHonestAt

  `main` placed at a frame pointer on a node's honest run: from its callees' completeness on that
  run (`MainGoals`), the statement of the bytecode's shape and the deployed limits.
-/

module

public import LeanVM.Guest.B1.Main.MainAt
public import LeanVM.Guest.B1.Main.MainHonestFit
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run

`MainGoals`: the ten callee statements of `MainGoals.lean`. `mainKids_ok`: they are what
`main_relAtInW` asks of `mKids`. `main_honest_relAtInW`: for `NodeRelation` within `Limits`, on every
memory holding `main`'s honest layout and the statement's digest at words `0`, `1`, `main` holds
by its node at `fp`, at a valuation with the honest values (`MVals` of `hm`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns bufL Kid LowDef DisjL Within)

@[expose] public section

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`main`'s callees on the honest run.** -/
structure MainGoals : Prop where
  clx : MainGoalClX fs cert fp seed s w
  cls : MainGoalClS fs cert fp seed s w
  l1 : MainGoalL1 fs cert fp seed s w
  l2 : MainGoalL2 fs cert fp seed s w
  l3 : MainGoalL3 fs cert fp seed s w
  l4 : MainGoalL4 fs cert fp seed s w
  dv : MainGoalDv fs cert fp seed s w
  l5 : MainGoalL5 fs cert fp seed s w
  ag : MainGoalAg fs cert fp seed s w
  st : MainGoalSt fs cert fp seed s w

variable {fs cert fp seed s w}

/-- **The callees `main_relAtInW` asks for.** -/
theorem mainKids_ok (hg : MainGoals fs cert fp seed s w) :
    ∀ k ∈ mKids (hm fs fp seed s w) (hLmain fs fp seed s w), k.taken = true →
      CompleteAtD fs cert 16 k.f k.Lin k.args k.Out := by
  intro k hk ht
  simp only [mKids, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with ((((hk | hk | hk | hk | hk | hk) | hk) | hk) | hk) | hk
  · subst hk; exact hg.clx
  · subst hk; exact hg.cls
  · subst hk; exact hg.l1 (of_decide_eq_true ht)
  · subst hk; exact hg.l2 (of_decide_eq_true ht)
  · subst hk; exact hg.l3 (of_decide_eq_true ht)
  · subst hk; exact hg.l4 (of_decide_eq_true ht)
  · split at hk
    · rename_i hnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk; exact hg.dv hnd
    · simp at hk
  · subst hk; exact hg.l5 (of_decide_eq_true ht)
  · split at hk
    · simp at hk
    · rename_i hnc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk; exact hg.ag hnc
  · subst hk; exact hg.st

variable {bytecode : List K}

/-- **`main` at `fp` on the honest run**: for `NodeRelation` within `Limits`, a statement of the
bytecode's shape (`log₂` of its length `23`) and fresh claims at points of `23` coordinates, from
its callees' completeness on the run: a layout `L` within `[fp, fp + n)`, pairwise disjoint,
above `main`'s frame, containing `main`'s honest words, on every memory holding which and the statement's digest at
words `0`, `1` `main` holds by its node at `fp`, at a valuation with the honest values. -/
theorem main_honest_relAtInW (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRelation bytecode seed s w)
    (hl : DeployedLimits s w) (hf : FreshShaped w) (hg : MainGoals fs cert fp seed s w) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInW coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun σ => MVals rd σ (hm fs fp seed s w)) :=
  main_relAtInW fs cert fp (hData seed s w) (hOwn seed s w) (hOwn_fit hlog hr hf)
    (hData_bounds hl fs fp) (mainKids_ok hg)
    (fun rd hM h0 h1 => hMainMem hlog hr hf hl fs fp rd hM h0 h1)

end
end LeanVM.Guest.B1.Main
