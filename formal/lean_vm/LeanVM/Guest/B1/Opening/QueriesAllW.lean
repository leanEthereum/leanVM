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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl

  · exact oqSpecW_481
  · exact oqSpecW_487
  · exact oqSpecW_492
  · exact oqSpecW_496
  · exact oqSpecW_504
  · exact oqSpecW_508
  · exact oqSpecW_512
  · exact oqSpecW_515
  · exact oqSpecW_523
  · exact oqSpecW_527
  · exact oqSpecW_531
  · exact oqSpecW_535
  · exact oqSpecW_544
  · exact oqSpecW_548
  · exact oqSpecW_552
  · exact oqSpecW_557
  · exact oqSpecW_566
  · exact oqSpecW_569
  · exact oqSpecW_572
  · exact oqSpecW_575
  · exact oqSpecW_583
  · exact oqSpecW_586
  · exact oqSpecW_589
  · exact oqSpecW_592
  · exact oqSpecW_599
  · exact oqSpecW_602
  · exact oqSpecW_605
  · exact oqSpecW_611
  · exact oqSpecW_620
  · exact oqSpecW_624
  · exact oqSpecW_630
  · exact oqSpecW_634
  · exact oqSpecW_640
  · exact oqSpecW_645
  · exact oqSpecW_652
  · exact oqSpecW_657
  · exact oqSpecW_664
  · exact oqSpecW_669
  · exact oqSpecW_676
  · exact oqSpecW_681
  · exact oqSpecW_688
  · exact oqSpecW_691
  · exact oqSpecW_694
  · exact oqSpecW_699
  · exact oqSpecW_709
  · exact oqSpecW_717
  · exact oqSpecW_726
  · exact oqSpecW_736
  · exact oqSpecW_746
  · exact oqSpecW_757
  · exact oqSpecW_764
  · exact oqSpecW_767
  · exact oqSpecW_770
  · exact oqSpecW_774
  · exact oqSpecW_776
  · exact oqSpecW_783
  · exact oqSpecW_787
  · exact oqSpecW_792
  · exact oqSpecW_796
  · exact oqSpecW_801
  · exact oqSpecW_806
  · exact oqSpecW_812
  · exact oqSpecW_817
  · exact oqSpecW_823
  · exact oqSpecW_828
  · exact oqSpecW_835
  · exact oqSpecW_838
  · exact oqSpecW_842
  · exact oqSpecW_849
  · exact oqSpecW_852
  · exact oqSpecW_857
  · exact oqSpecW_859

end
end LeanVM.Guest.B1
