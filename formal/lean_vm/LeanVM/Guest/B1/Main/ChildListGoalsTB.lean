/-
  LeanVM.Guest.B1.Main.ChildListGoalsTB

  Each child's claim lists' digests on `main`'s honest run, complete within bounds before the
  memory (`CompleteAtDTB`), by trees satisfying given predicates.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.Budget.Bounded

/-!
# The children's claim lists, within bounds

`ChildListGoalsTB … Pxs Pss Bxs Bss`: `ChildListGoalsT` with `CompleteAtDTB`, child `c`'s two
calls within `Bxs c`, `Bss c` words. `ChildListGoalsTB.toT` forgets the bounds.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (CompleteAtDTB Returns)

@[expose] public section

/-- **Each child's claim lists' digests complete within `Bxs c`, `Bss c` words, by trees satisfying
`Pxs c`, `Pss c`**, at the words `main`'s children loop passes them. -/
def ChildListGoalsTB (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (Pxs Pss : ℕ → Tree → Prop) (Bxs Bss : ℕ → ℕ) : Prop :=
  ∀ c, c < w.children.length →
    CompleteAtDTB fs cert 16 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, (hm fs fp seed s w).a117, (hKid s w c).base,
        gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), gen ^ (hKid s w c).ex]
      (Returns [(hKid s w c).cx.1, (hKid s w c).cx.2]) (Pxs c) (Bxs c) ∧
    CompleteAtDTB fs cert 16 "child_claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hKid s w c).base * gen ^ (hKid s w c).ex,
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), gen ^ (hKid s w c).es]
      (Returns [(hKid s w c).cs.1, (hKid s w c).cs.2]) (Pss c) (Bss c)

theorem ChildListGoalsTB.toT {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} {Pxs Pss : ℕ → Tree → Prop} {Bxs Bss : ℕ → ℕ}
    (h : ChildListGoalsTB fs cert fp seed s w Pxs Pss Bxs Bss) :
    ChildListGoalsT fs cert fp seed s w Pxs Pss := fun c hc =>
  ⟨(h c hc).1.toDT, (h c hc).2.toDT⟩

end
end LeanVM.Guest.B1.Main
