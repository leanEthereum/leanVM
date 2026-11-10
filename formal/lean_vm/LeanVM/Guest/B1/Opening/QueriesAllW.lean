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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact oqSpecW_482
  · exact oqSpecW_489
  · exact oqSpecW_495
  · exact oqSpecW_499
  · exact oqSpecW_508
  · exact oqSpecW_513
  · exact oqSpecW_518
  · exact oqSpecW_521
  · exact oqSpecW_530
  · exact oqSpecW_535
  · exact oqSpecW_540
  · exact oqSpecW_546
  · exact oqSpecW_556
  · exact oqSpecW_561
  · exact oqSpecW_566
  · exact oqSpecW_572
  · exact oqSpecW_582
  · exact oqSpecW_585
  · exact oqSpecW_588
  · exact oqSpecW_591
  · exact oqSpecW_600
  · exact oqSpecW_603
  · exact oqSpecW_606
  · exact oqSpecW_609
  · exact oqSpecW_617
  · exact oqSpecW_620
  · exact oqSpecW_623
  · exact oqSpecW_629
  · exact oqSpecW_638
  · exact oqSpecW_642
  · exact oqSpecW_648
  · exact oqSpecW_652
  · exact oqSpecW_658
  · exact oqSpecW_663
  · exact oqSpecW_670
  · exact oqSpecW_675
  · exact oqSpecW_682
  · exact oqSpecW_687
  · exact oqSpecW_694
  · exact oqSpecW_699
  · exact oqSpecW_706
  · exact oqSpecW_709
  · exact oqSpecW_712
  · exact oqSpecW_716
  · exact oqSpecW_719
  · exact oqSpecW_729
  · exact oqSpecW_737
  · exact oqSpecW_746
  · exact oqSpecW_756
  · exact oqSpecW_766
  · exact oqSpecW_776
  · exact oqSpecW_783
  · exact oqSpecW_786
  · exact oqSpecW_789
  · exact oqSpecW_793
  · exact oqSpecW_795
  · exact oqSpecW_802
  · exact oqSpecW_806
  · exact oqSpecW_811
  · exact oqSpecW_815
  · exact oqSpecW_820
  · exact oqSpecW_825
  · exact oqSpecW_831
  · exact oqSpecW_836
  · exact oqSpecW_842
  · exact oqSpecW_847
  · exact oqSpecW_854
  · exact oqSpecW_857
  · exact oqSpecW_861
  · exact oqSpecW_868
  · exact oqSpecW_871
  · exact oqSpecW_876
  · exact oqSpecW_878

end
end LeanVM.Guest.B1
