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

`opening_queries_completeAtB`: each of the 56 deployed specializations (`openingQueriesLoops`:
name, loop helper, shape, `odd`) is `CompleteAtB` (`OqCompleteDB`, by a tree of at most
`oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert` (`OqFits`
trivial: no frame runs); `opening_queries_completeAtD`, its `CompleteAtD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtB`.** -/
theorem opening_queries_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDB fs cert p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqD_413 fs cert
  · exact oqD_449 fs cert
  · exact oqD_701 fs cert
  · exact oqD_575 fs cert
  · exact oqD_598 fs cert
  · exact oqD_623 fs cert
  · exact oqD_654 fs cert
  · exact oqD_425 fs cert
  · exact oqD_418 fs cert
  · exact oqD_524 fs cert
  · exact oqD_491 fs cert
  · exact oqD_489 fs cert
  · exact oqD_761 fs cert
  · exact oqD_600 fs cert
  · exact oqD_533 fs cert
  · exact oqD_692 fs cert
  · exact oqD_563 fs cert
  · exact oqD_721 fs cert
  · exact oqD_743 fs cert
  · exact oqD_632 fs cert
  · exact oqD_515 fs cert
  · exact oqD_422 fs cert
  · exact oqD_568 fs cert
  · exact oqD_474 fs cert
  · exact oqD_471 fs cert
  · exact oqD_683 fs cert
  · exact oqD_602 fs cert
  · exact oqD_745 fs cert
  · exact oqD_433 fs cert
  · exact oqD_551 fs cert
  · exact oqD_487 fs cert
  · exact oqD_586 fs cert
  · exact oqD_755 fs cert
  · exact oqD_643 fs cert
  · exact oqD_665 fs cert
  · exact oqD_556 fs cert
  · exact oqD_455 fs cert
  · exact oqD_452 fs cert
  · exact oqD_605 fs cert
  · exact oqD_519 fs cert
  · exact oqD_517 fs cert
  · exact oqD_678 fs cert
  · exact oqD_542 fs cert
  · exact oqD_468 fs cert
  · exact oqD_710 fs cert
  · exact oqD_732 fs cert
  · exact oqD_614 fs cert
  · exact oqD_501 fs cert
  · exact oqD_676 fs cert
  · exact oqD_439 fs cert
  · exact oqD_436 fs cert
  · exact oqD_591 fs cert
  · exact oqD_505 fs cert
  · exact oqD_503 fs cert
  · exact oqD_680 fs cert
  · exact oqD_757 fs cert

end
end LeanVM.Guest.B1
