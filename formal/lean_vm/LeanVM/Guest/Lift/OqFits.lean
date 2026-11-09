/-
  LeanVM.Guest.Lift.OqFits

  A fact of the frame certificates: two frame runs of a body meet only at a common value
  (`Lift.RunsApart`).
-/

module

public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2

/-!
# Frame runs apart

At 40f877dc neither `opening_queries`' queries nor their `walk_path` frames place a frame run (the
path children are hinted into `walk_path`'s frame cells), so its frame facts `OqFits` are `True`; `RunsApart` stays, a fact of the
certificates the completeness statements read (`VerifySub.CompleteSpec`).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Two frame runs of a body meet only at a common value**: where their cells coincide, their
values do. The certificates' fact, discharged for the deployed instance from the checker's
(`B2C.FnStatic.runsFun`). -/
def RunsApart (cert : String → V → ℕ) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ p r rs p' r' rs',
    Atom.frameAddr p (r :: rs) ∈ blockAtoms fn.body →
    Atom.frameAddr p' (r' :: rs') ∈ blockAtoms fn.body →
    ∀ (k : ℕ) (hk : k < (r :: rs).length) (k' : ℕ) (hk' : k' < (r' :: rs').length),
      cert f r + k = cert f r' + k' → (r :: rs)[k] = (r' :: rs')[k']

theorem mem_blockAtoms {a : Atom} : ∀ {ss : List Stmt}, Stmt.atom a ∈ ss → a ∈ blockAtoms ss
  | [], h => by cases h
  | s :: ss, h => by
    rw [blockAtoms, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp [stmtAtoms])
    · exact Or.inr (mem_blockAtoms h)

end
end LeanVM.Guest.Lift
