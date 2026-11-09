/-
  LeanVM.Guest.B1.Opening.LoopsTable

  Every deployed shape of `opening_queries` has its loop helper in `openingQueriesLoops`.
-/

module

public import LeanVM.Guest.B1.Opening.Witness

/-!
# The loop helpers of the deployed shapes

`shapes_loops`: for every deployed shape `(name, odd, base, I, leafCells, depth, cd)` of
`openingQueriesShapes`, `openingQueriesLoops` holds `(name, oqLoopOf name, ⟨base, I, depth - cd,
cd⟩, odd)` (a kernel-decided check over the two tables).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The tables agree, as a check. -/
def shapesLoopsB : Bool :=
  openingQueriesShapes.all fun e ↦ openingQueriesLoops.any fun p ↦
    p.1 == e.1 && p.2.1 == oqLoopOf e.1 && p.2.2.1.base == e.2.2.1 &&
      p.2.2.1.I == e.2.2.2.1 && p.2.2.1.pd == e.2.2.2.2.2.1 - e.2.2.2.2.2.2 &&
      p.2.2.1.cd == e.2.2.2.2.2.2 && p.2.2.2 == e.2.1

theorem shapesLoopsB_true : shapesLoopsB = true := by decide +kernel

/-- **Every deployed shape has its loop helper.** -/
theorem shapes_loops {e : String × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (he : e ∈ openingQueriesShapes) :
    (e.1, oqLoopOf e.1, (⟨e.2.2.1, e.2.2.2.1, e.2.2.2.2.2.1 - e.2.2.2.2.2.2, e.2.2.2.2.2.2⟩ : Oq),
      e.2.1) ∈ openingQueriesLoops := by
  have h := shapesLoopsB_true
  simp only [shapesLoopsB, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ := h e he
  obtain ⟨n, l, ⟨b, i, pd, cd⟩, o⟩ := p
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact hp

end
end LeanVM.Guest.B1
