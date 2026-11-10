/-
  LeanVM.Guest.WalkOq3

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody3.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk3.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk3
public import LeanVM.Guest.B1.Opening.QueriesBody3

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
theorem walk_458 : CutsKnown 458 :=
  main_cutsKnown (j := 458) oqBody_436
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_458

set_option maxRecDepth 100000 in
theorem walk_461 : CutsKnown 461 :=
  main_cutsKnown (j := 461) oqBody_439
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_461

set_option maxRecDepth 100000 in
theorem walk_490 : CutsKnown 490 :=
  main_cutsKnown (j := 1346) oqBody_468
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_490

set_option maxRecDepth 100000 in
theorem walk_523 : CutsKnown 523 :=
  main_cutsKnown (j := 523) oqBody_501
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_523

set_option maxRecDepth 100000 in
theorem walk_525 : CutsKnown 525 :=
  main_cutsKnown (j := 525) oqBody_503
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_525

set_option maxRecDepth 100000 in
theorem walk_527 : CutsKnown 527 :=
  main_cutsKnown (j := 527) oqBody_505
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_527

set_option maxRecDepth 100000 in
theorem walk_564 : CutsKnown 564 :=
  main_cutsKnown (j := 1200) oqBody_542
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_564

set_option maxRecDepth 100000 in
theorem walk_613 : CutsKnown 613 :=
  main_cutsKnown (j := 613) oqBody_591
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_613

set_option maxRecDepth 100000 in
theorem walk_636 : CutsKnown 636 :=
  main_cutsKnown (j := 1236) oqBody_614
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_636

set_option maxRecDepth 100000 in
theorem walk_698 : CutsKnown 698 :=
  main_cutsKnown (j := 1460) oqBody_676
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_698

set_option maxRecDepth 100000 in
theorem walk_702 : CutsKnown 702 :=
  main_cutsKnown (j := 1389) oqBody_680
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_702

set_option maxRecDepth 100000 in
theorem walk_732 : CutsKnown 732 :=
  main_cutsKnown (j := 732) oqBody_710
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_732

set_option maxRecDepth 100000 in
theorem walk_754 : CutsKnown 754 :=
  main_cutsKnown (j := 1386) oqBody_732
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_754

set_option maxRecDepth 100000 in
theorem walk_779 : CutsKnown 779 :=
  main_cutsKnown (j := 779) oqBody_757
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_779

set_option maxRecDepth 100000 in
theorem walk_857 : CutsKnown 857 :=
  loop0_cutsKnown (j := 857) oqBody_836
    (by decide) (by decide) (by decide) walkOk_857

set_option maxRecDepth 100000 in
theorem walk_859 : CutsKnown 859 :=
  loop0_cutsKnown (j := 859) oqBody_837
    (by decide) (by decide) (by decide) walkOk_859

set_option maxRecDepth 100000 in
theorem walk_867 : CutsKnown 867 :=
  loop1_cutsKnown (j := 867) oqBody_843
    (by decide) (by decide) (by decide) (by decide) walkOk_867

set_option maxRecDepth 100000 in
theorem walk_880 : CutsKnown 880 :=
  loop1_cutsKnown (j := 880) oqBody_851
    (by decide) (by decide) (by decide) (by decide) walkOk_880

set_option maxRecDepth 100000 in
theorem walk_882 : CutsKnown 882 :=
  loop0_cutsKnown (j := 882) oqBody_852
    (by decide) (by decide) (by decide) walkOk_882

set_option maxRecDepth 100000 in
theorem walk_884 : CutsKnown 884 :=
  loop0_cutsKnown (j := 884) oqBody_853
    (by decide) (by decide) (by decide) walkOk_884

set_option maxRecDepth 100000 in
theorem walk_897 : CutsKnown 897 :=
  loop1_cutsKnown (j := 897) oqBody_860
    (by decide) (by decide) (by decide) (by decide) walkOk_897

set_option maxRecDepth 100000 in
theorem walk_911 : CutsKnown 911 :=
  loop0_cutsKnown (j := 911) oqBody_867
    (by decide) (by decide) (by decide) walkOk_911

set_option maxRecDepth 100000 in
theorem walk_921 : CutsKnown 921 :=
  loop1_cutsKnown (j := 921) oqBody_873
    (by decide) (by decide) (by decide) (by decide) walkOk_921

set_option maxRecDepth 100000 in
theorem walk_934 : CutsKnown 934 :=
  loop1_cutsKnown (j := 934) oqBody_880
    (by decide) (by decide) (by decide) (by decide) walkOk_934

set_option maxRecDepth 100000 in
theorem walk_938 : CutsKnown 938 :=
  loop0_cutsKnown (j := 938) oqBody_882
    (by decide) (by decide) (by decide) walkOk_938

set_option maxRecDepth 100000 in
theorem walk_943 : CutsKnown 943 :=
  loop1_cutsKnown (j := 1136) oqBody_886
    (by decide) (by decide) (by decide) (by decide) walkOk_943

set_option maxRecDepth 100000 in
theorem walk_945 : CutsKnown 945 :=
  loop1_cutsKnown (j := 1138) oqBody_888
    (by decide) (by decide) (by decide) (by decide) walkOk_945

set_option maxRecDepth 100000 in
theorem walk_953 : CutsKnown 953 :=
  loop0_cutsKnown (j := 1142) oqBody_893
    (by decide) (by decide) (by decide) walkOk_953

end
end LeanVM.Guest.End
