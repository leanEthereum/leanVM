/-
  LeanVM.Guest.B1.Opening.QueriesAllW

  Every deployed specialization of `opening_queries` is sound with its queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW0
public import LeanVM.Guest.B1.Opening.QueriesW1
public import LeanVM.Guest.B1.Opening.QueriesW2
public import LeanVM.Guest.B1.Opening.QueriesW3

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **Every deployed `opening_queries` is sound with its queries named.** -/
theorem opening_queries_all_sound_w : opening_queries_all_sound_w_Spec := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oqSpecW_413
  · exact oqSpecW_449
  · exact oqSpecW_701
  · exact oqSpecW_575
  · exact oqSpecW_598
  · exact oqSpecW_623
  · exact oqSpecW_654
  · exact oqSpecW_425
  · exact oqSpecW_418
  · exact oqSpecW_524
  · exact oqSpecW_491
  · exact oqSpecW_489
  · exact oqSpecW_761
  · exact oqSpecW_600
  · exact oqSpecW_533
  · exact oqSpecW_692
  · exact oqSpecW_563
  · exact oqSpecW_721
  · exact oqSpecW_743
  · exact oqSpecW_632
  · exact oqSpecW_515
  · exact oqSpecW_422
  · exact oqSpecW_568
  · exact oqSpecW_474
  · exact oqSpecW_471
  · exact oqSpecW_683
  · exact oqSpecW_602
  · exact oqSpecW_745
  · exact oqSpecW_433
  · exact oqSpecW_551
  · exact oqSpecW_487
  · exact oqSpecW_586
  · exact oqSpecW_755
  · exact oqSpecW_643
  · exact oqSpecW_665
  · exact oqSpecW_556
  · exact oqSpecW_455
  · exact oqSpecW_452
  · exact oqSpecW_605
  · exact oqSpecW_519
  · exact oqSpecW_517
  · exact oqSpecW_678
  · exact oqSpecW_542
  · exact oqSpecW_468
  · exact oqSpecW_710
  · exact oqSpecW_732
  · exact oqSpecW_614
  · exact oqSpecW_501
  · exact oqSpecW_676
  · exact oqSpecW_439
  · exact oqSpecW_436
  · exact oqSpecW_591
  · exact oqSpecW_505
  · exact oqSpecW_503
  · exact oqSpecW_680
  · exact oqSpecW_757

end
end LeanVM.Guest.B1
