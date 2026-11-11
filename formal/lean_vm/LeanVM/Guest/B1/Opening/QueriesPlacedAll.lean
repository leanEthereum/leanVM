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
  · exact oqD_481 fs cert
  · exact oqD_487 fs cert
  · exact oqD_492 fs cert
  · exact oqD_496 fs cert
  · exact oqD_504 fs cert
  · exact oqD_508 fs cert
  · exact oqD_512 fs cert
  · exact oqD_515 fs cert
  · exact oqD_523 fs cert
  · exact oqD_527 fs cert
  · exact oqD_531 fs cert
  · exact oqD_535 fs cert
  · exact oqD_544 fs cert
  · exact oqD_548 fs cert
  · exact oqD_552 fs cert
  · exact oqD_557 fs cert
  · exact oqD_566 fs cert
  · exact oqD_569 fs cert
  · exact oqD_572 fs cert
  · exact oqD_575 fs cert
  · exact oqD_583 fs cert
  · exact oqD_586 fs cert
  · exact oqD_589 fs cert
  · exact oqD_592 fs cert
  · exact oqD_599 fs cert
  · exact oqD_602 fs cert
  · exact oqD_605 fs cert
  · exact oqD_611 fs cert
  · exact oqD_620 fs cert
  · exact oqD_624 fs cert
  · exact oqD_630 fs cert
  · exact oqD_634 fs cert
  · exact oqD_640 fs cert
  · exact oqD_645 fs cert
  · exact oqD_652 fs cert
  · exact oqD_657 fs cert
  · exact oqD_664 fs cert
  · exact oqD_669 fs cert
  · exact oqD_676 fs cert
  · exact oqD_681 fs cert
  · exact oqD_688 fs cert
  · exact oqD_691 fs cert
  · exact oqD_694 fs cert
  · exact oqD_698 fs cert
  · exact oqD_701 fs cert
  · exact oqD_711 fs cert
  · exact oqD_719 fs cert
  · exact oqD_728 fs cert
  · exact oqD_738 fs cert
  · exact oqD_748 fs cert
  · exact oqD_758 fs cert
  · exact oqD_765 fs cert
  · exact oqD_768 fs cert
  · exact oqD_771 fs cert
  · exact oqD_775 fs cert
  · exact oqD_777 fs cert
  · exact oqD_784 fs cert
  · exact oqD_788 fs cert
  · exact oqD_793 fs cert
  · exact oqD_797 fs cert
  · exact oqD_802 fs cert
  · exact oqD_807 fs cert
  · exact oqD_813 fs cert
  · exact oqD_818 fs cert
  · exact oqD_824 fs cert
  · exact oqD_829 fs cert
  · exact oqD_836 fs cert
  · exact oqD_839 fs cert
  · exact oqD_843 fs cert
  · exact oqD_850 fs cert
  · exact oqD_853 fs cert
  · exact oqD_858 fs cert
  · exact oqD_860 fs cert

end
end LeanVM.Guest.B1
