/-
  LeanVM.Guest.Budget.Shape

  A child's shape as the count reads it, off its proof: the stacked opening's stack log and rate
  `readAnnouncedSizes` announces, and whether its opening takes the zero-challenge sum; admissible
  for every child the deferring verifier accepts.
-/

module

public import LeanVM.Guest.Budget.Count
public import LeanVM.Guest.B1.VsC.Shape

/-!
# A child's shape

`shapeOf bytecode z c`: the stack log and rate of `announcedLayoutAndRate bytecode c.proof.stream`
(what `verify_sub` reads first and dispatches its opening on), and `z c` for the zero-challenge sum.
Whether a level of the opening takes `level_residual_sum` is a Fiat-Shamir outcome (a zero product of
the level's later fold and tail challenges), not a size the proof announces, so it is a parameter:
the count's theorems read it as the shape's `zeroSum`, and `RunWithinCount`'s run must take the sum
only where `z` says so (`notes/hotwire-port.md`, the budget's verdict).

`shapeOf_admissible`: on a child the deferring verifier accepts (`ChildrenProven`'s second
conjunct), the shape is admissible (`vsShape_of_verifyDeferred`: rate `1 ..= 4`, stack log
`16 ..= 30`). `shapeOf_admissible_of_rel`: so on every child of a node with `NodeRelation`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **A child's shape**: its announced stack log and rate, and `z c` for the zero-challenge sum
(an unreadable announcement at the largest admissible shape). -/
noncomputable def shapeOf (bytecode : List K) (z : Child → Bool) (c : Child) : ChildShape :=
  match announcedLayoutAndRate bytecode c.proof.stream with
  | some (layout, r) => ⟨layout.stackLog, r, z c⟩
  | none => ⟨30, 1, z c⟩

theorem shapeOf_zeroSum (bytecode : List K) (z : Child → Bool) (c : Child) :
    (shapeOf bytecode z c).zeroSum = z c := by
  unfold shapeOf; split <;> rfl

/-- **An accepted child's shape is admissible.** -/
theorem shapeOf_admissible {bytecode : List K} {iv publicInput : Digest} {fresh : FreshClaim}
    (z : Child → Bool) {c : Child} (h : verifyDeferred bytecode iv publicInput fresh c.proof = true) :
    (shapeOf bytecode z c).Admissible := by
  obtain ⟨layout, r, hann, hs⟩ := B1.VsC.vsShape_of_verifyDeferred h
  unfold shapeOf
  rw [hann]
  have h1 := hs.stack_ge
  have h2 := hs.stack_le
  simp only [Whir.minLogStack, Whir.maxLogStack] at h1 h2
  exact ⟨h1, h2, hs.rate_ge, hs.rate_le⟩

/-- **The children of a node with `NodeRelation` have admissible shapes.** -/
theorem shapeOf_admissible_of_rel {bytecode : List K} {seed : Digest} (z : Child → Bool)
    {statement : NodeStatement} {witness : NodeWitness}
    (hrel : NodeRelation bytecode seed statement witness) :
    ∀ c ∈ witness.children, (shapeOf bytecode z c).Admissible :=
  fun c hc ↦ shapeOf_admissible z (hrel.2.2.1 c hc).2

end

end LeanVM.Guest.Budget
