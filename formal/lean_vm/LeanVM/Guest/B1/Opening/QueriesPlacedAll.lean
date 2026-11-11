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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact oqD_699 fs cert
  · exact oqD_709 fs cert
  · exact oqD_717 fs cert
  · exact oqD_726 fs cert
  · exact oqD_736 fs cert
  · exact oqD_746 fs cert
  · exact oqD_757 fs cert
  · exact oqD_764 fs cert
  · exact oqD_767 fs cert
  · exact oqD_770 fs cert
  · exact oqD_774 fs cert
  · exact oqD_776 fs cert
  · exact oqD_783 fs cert
  · exact oqD_787 fs cert
  · exact oqD_792 fs cert
  · exact oqD_796 fs cert
  · exact oqD_801 fs cert
  · exact oqD_806 fs cert
  · exact oqD_812 fs cert
  · exact oqD_817 fs cert
  · exact oqD_823 fs cert
  · exact oqD_828 fs cert
  · exact oqD_835 fs cert
  · exact oqD_838 fs cert
  · exact oqD_842 fs cert
  · exact oqD_849 fs cert
  · exact oqD_852 fs cert
  · exact oqD_857 fs cert
  · exact oqD_859 fs cert

end
end LeanVM.Guest.B1
