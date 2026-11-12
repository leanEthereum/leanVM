/-
  LeanVM.Guest.B1.Opening.QueriesPlacedAll

  Every deployed specialization of `opening_queries` is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesFns
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2

/-!
# `opening_queries`, `CompleteAtB`, every specialization

`opening_queries_completeAtB`: each deployed specialization (`openingQueriesLoops`: name, loop
helper, shape) is `CompleteAtB` (`OqCompleteDB` at the shape's `Oq` and `odd`, by a tree of at most
`oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert` (`OqFits`
trivial: no frame runs): its base's theorem (`oqCompleteDB0`, `oqCompleteDB1`) at its functions
(`oqFns_all`) and its shape's facts (`oqSide_all`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtB`.** -/
theorem opening_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDB fs cert p.1 p.2.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  obtain ⟨hW, fm, fl, hfm, hpm, hbm, hfl, hpl, hbl⟩ := oqFns_all p hp
  obtain ⟨hs, hfin, hb, hpd, hcd, -, -, hE⟩ := oqSide_all p hp
  rcases hb with ⟨hb0, hodd⟩ | ⟨hb1, -, hodd⟩
  · rw [hodd] at hbm hE ⊢
    exact oqCompleteDB0 fs cert hs hfin hb0 hpd hcd hE hW hfm hpm hbm hfl hpl
      (hbl.trans (oqLoopT_zero hb0 _ _ _))
  · exact oqCompleteDB1 fs cert hs hfin hb1 hpd hcd hodd hE hW hfm hpm hbm hfl hpl
      (hbl.trans (oqLoopT_one hb1 _ _ _))

end
end LeanVM.Guest.B1
