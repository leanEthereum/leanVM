/-
  LeanVM.Guest.B1.Opening.QueriesPlacedAll

  Every deployed specialization of `opening_queries` is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedS0
public import LeanVM.Guest.B1.Opening.QueriesPlacedS1
public import LeanVM.Guest.B1.Opening.QueriesPlacedS2
public import LeanVM.Guest.B1.Opening.QueriesPlacedS3

/-!
# `opening_queries`, `CompleteAtB`, every specialization

`opening_queries_completeAtB`: each of the 73 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape) is `CompleteAtB` (`OqCompleteDB` at the shape's `Oq` and `odd`, by a tree
of at most `oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert`
(`OqFits` trivial: no frame runs).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtB`.** -/
theorem opening_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDB fs cert p.1 p.2.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqD_482 fs cert
  · exact oqD_489 fs cert
  · exact oqD_495 fs cert
  · exact oqD_499 fs cert
  · exact oqD_508 fs cert
  · exact oqD_513 fs cert
  · exact oqD_518 fs cert
  · exact oqD_521 fs cert
  · exact oqD_530 fs cert
  · exact oqD_535 fs cert
  · exact oqD_540 fs cert
  · exact oqD_546 fs cert
  · exact oqD_556 fs cert
  · exact oqD_561 fs cert
  · exact oqD_566 fs cert
  · exact oqD_572 fs cert
  · exact oqD_582 fs cert
  · exact oqD_585 fs cert
  · exact oqD_588 fs cert
  · exact oqD_591 fs cert
  · exact oqD_600 fs cert
  · exact oqD_603 fs cert
  · exact oqD_606 fs cert
  · exact oqD_609 fs cert
  · exact oqD_617 fs cert
  · exact oqD_620 fs cert
  · exact oqD_623 fs cert
  · exact oqD_629 fs cert
  · exact oqD_638 fs cert
  · exact oqD_642 fs cert
  · exact oqD_648 fs cert
  · exact oqD_652 fs cert
  · exact oqD_658 fs cert
  · exact oqD_663 fs cert
  · exact oqD_670 fs cert
  · exact oqD_675 fs cert
  · exact oqD_682 fs cert
  · exact oqD_687 fs cert
  · exact oqD_694 fs cert
  · exact oqD_699 fs cert
  · exact oqD_706 fs cert
  · exact oqD_709 fs cert
  · exact oqD_712 fs cert
  · exact oqD_716 fs cert
  · exact oqD_719 fs cert
  · exact oqD_729 fs cert
  · exact oqD_737 fs cert
  · exact oqD_746 fs cert
  · exact oqD_756 fs cert
  · exact oqD_766 fs cert
  · exact oqD_776 fs cert
  · exact oqD_783 fs cert
  · exact oqD_786 fs cert
  · exact oqD_789 fs cert
  · exact oqD_793 fs cert
  · exact oqD_795 fs cert
  · exact oqD_802 fs cert
  · exact oqD_806 fs cert
  · exact oqD_811 fs cert
  · exact oqD_815 fs cert
  · exact oqD_820 fs cert
  · exact oqD_825 fs cert
  · exact oqD_831 fs cert
  · exact oqD_836 fs cert
  · exact oqD_842 fs cert
  · exact oqD_847 fs cert
  · exact oqD_854 fs cert
  · exact oqD_857 fs cert
  · exact oqD_861 fs cert
  · exact oqD_868 fs cert
  · exact oqD_871 fs cert
  · exact oqD_876 fs cert
  · exact oqD_878 fs cert

end
end LeanVM.Guest.B1
