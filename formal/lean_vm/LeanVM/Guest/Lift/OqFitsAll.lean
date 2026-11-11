/-
  LeanVM.Guest.Lift.OqFitsAll

  Every deployed specialization of `opening_queries` fits its frames (`OqFits`).
-/

module

public import LeanVM.Guest.Lift.OqFits

/-!
# `opening_queries`' frames, every specialization

At 40f877dc a query places no frame run, nor does its `walk_path` (its path children are hinted
into the walk's frame cells), so
`OqFits` asks nothing (`True`, `QueriesPlacedD2`): every specialization fits, for any
certificates.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries`' frames fit its runs**, for certificates whose runs fit
their frames and meet only at common values. -/
theorem opening_queries_fits (fs : String → ℕ) (cert : String → V → ℕ)
    (_hfit : Lift.RunsFit fs cert) (_hap : Lift.RunsApart cert) :
    ∀ p ∈ openingQueriesLoops, OqFits fs cert p.1 p.2.1 p.2.2.1 p.2.2.2 :=
  fun _ _ ↦ trivial

end
end LeanVM.Guest.B1
