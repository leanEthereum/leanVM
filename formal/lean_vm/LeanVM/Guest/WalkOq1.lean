/-
  LeanVM.Guest.WalkOq1

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody1.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk1.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk1
public import LeanVM.Guest.B1.Opening.QueriesBody1

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L6_L0_L0_L0_L0_L0`. -/
theorem walk_488 : CutsKnown 488 :=
  main_cutsKnown (j := 488) oqBody_487
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_488

set_option maxRecDepth 100000 in
/-- `__loop341`. -/
theorem walk_922 : CutsKnown 922 :=
  loop0_cutsKnown (j := 922) oqLoopBody_487
    (by decide) (by decide) (by decide) walkOk_922

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0`. -/
theorem walk_509 : CutsKnown 509 :=
  main_cutsKnown (j := 509) oqBody_508
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_509

set_option maxRecDepth 100000 in
/-- `__loop345`. -/
theorem walk_926 : CutsKnown 926 :=
  loop0_cutsKnown (j := 926) oqLoopBody_508
    (by decide) (by decide) (by decide) walkOk_926

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem walk_528 : CutsKnown 528 :=
  main_cutsKnown (j := 528) oqBody_527
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_528

set_option maxRecDepth 100000 in
/-- `__loop349`. -/
theorem walk_930 : CutsKnown 930 :=
  loop0_cutsKnown (j := 930) oqLoopBody_527
    (by decide) (by decide) (by decide) walkOk_930

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0`. -/
theorem walk_549 : CutsKnown 549 :=
  main_cutsKnown (j := 549) oqBody_548
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_549

set_option maxRecDepth 100000 in
/-- `__loop353`. -/
theorem walk_934 : CutsKnown 934 :=
  loop0_cutsKnown (j := 934) oqLoopBody_548
    (by decide) (by decide) (by decide) walkOk_934

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0`. -/
theorem walk_570 : CutsKnown 570 :=
  main_cutsKnown (j := 570) oqBody_569
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_570

set_option maxRecDepth 100000 in
/-- `__loop357`. -/
theorem walk_938 : CutsKnown 938 :=
  loop0_cutsKnown (j := 938) oqLoopBody_569
    (by decide) (by decide) (by decide) walkOk_938

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_587 : CutsKnown 587 :=
  main_cutsKnown (j := 587) oqBody_586
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_587

set_option maxRecDepth 100000 in
/-- `__loop361`. -/
theorem walk_942 : CutsKnown 942 :=
  loop0_cutsKnown (j := 942) oqLoopBody_586
    (by decide) (by decide) (by decide) walkOk_942

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0`. -/
theorem walk_603 : CutsKnown 603 :=
  main_cutsKnown (j := 603) oqBody_602
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_603

set_option maxRecDepth 100000 in
/-- `__loop365`. -/
theorem walk_946 : CutsKnown 946 :=
  loop0_cutsKnown (j := 946) oqLoopBody_602
    (by decide) (by decide) (by decide) walkOk_946

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1`. -/
theorem walk_625 : CutsKnown 625 :=
  main_cutsKnown (j := 625) oqBody_624
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_625

set_option maxRecDepth 100000 in
/-- `__loop369`. -/
theorem walk_951 : CutsKnown 951 :=
  loop0_cutsKnown (j := 951) oqLoopBody_624
    (by decide) (by decide) (by decide) walkOk_951

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1`. -/
theorem walk_646 : CutsKnown 646 :=
  main_cutsKnown (j := 646) oqBody_645
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_646

set_option maxRecDepth 100000 in
/-- `__loop373`. -/
theorem walk_957 : CutsKnown 957 :=
  loop0_cutsKnown (j := 957) oqLoopBody_645
    (by decide) (by decide) (by decide) walkOk_957

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1`. -/
theorem walk_670 : CutsKnown 670 :=
  main_cutsKnown (j := 670) oqBody_669
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_670

set_option maxRecDepth 100000 in
/-- `__loop377`. -/
theorem walk_963 : CutsKnown 963 :=
  loop0_cutsKnown (j := 963) oqLoopBody_669
    (by decide) (by decide) (by decide) walkOk_963

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_692 : CutsKnown 692 :=
  main_cutsKnown (j := 692) oqBody_691
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_692

set_option maxRecDepth 100000 in
/-- `__loop381`. -/
theorem walk_969 : CutsKnown 969 :=
  loop0_cutsKnown (j := 969) oqLoopBody_691
    (by decide) (by decide) (by decide) walkOk_969

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem walk_718 : CutsKnown 718 :=
  main_cutsKnown (j := 718) oqBody_717
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_718

set_option maxRecDepth 100000 in
/-- `__loop385`. -/
theorem walk_973 : CutsKnown 973 :=
  loop0_cutsKnown (j := 973) oqLoopBody_717
    (by decide) (by decide) (by decide) walkOk_973

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem walk_758 : CutsKnown 758 :=
  main_cutsKnown (j := 758) oqBody_757
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_758

set_option maxRecDepth 100000 in
/-- `__loop389`. -/
theorem walk_977 : CutsKnown 977 :=
  loop0_cutsKnown (j := 977) oqLoopBody_757
    (by decide) (by decide) (by decide) walkOk_977

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem walk_775 : CutsKnown 775 :=
  main_cutsKnown (j := 775) oqBody_774
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_775

set_option maxRecDepth 100000 in
/-- `__loop393`. -/
theorem walk_982 : CutsKnown 982 :=
  loop0_cutsKnown (j := 982) oqLoopBody_774
    (by decide) (by decide) (by decide) walkOk_982

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_793 : CutsKnown 793 :=
  main_cutsKnown (j := 793) oqBody_792
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_793

set_option maxRecDepth 100000 in
/-- `__loop397`. -/
theorem walk_988 : CutsKnown 988 :=
  loop1_cutsKnown (j := 988) oqLoopBody_792
    (by decide) (by decide) (by decide) (by decide) walkOk_988

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_813 : CutsKnown 813 :=
  main_cutsKnown (j := 813) oqBody_812
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_813

set_option maxRecDepth 100000 in
/-- `__loop401`. -/
theorem walk_994 : CutsKnown 994 :=
  loop1_cutsKnown (j := 994) oqLoopBody_812
    (by decide) (by decide) (by decide) (by decide) walkOk_994

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem walk_836 : CutsKnown 836 :=
  main_cutsKnown (j := 836) oqBody_835
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_836

set_option maxRecDepth 100000 in
/-- `__loop405`. -/
theorem walk_1000 : CutsKnown 1000 :=
  loop1_cutsKnown (j := 1000) oqLoopBody_835
    (by decide) (by decide) (by decide) (by decide) walkOk_1000

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem walk_853 : CutsKnown 853 :=
  main_cutsKnown (j := 853) oqBody_852
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_853

set_option maxRecDepth 100000 in
/-- `__loop409`. -/
theorem walk_1005 : CutsKnown 1005 :=
  loop0_cutsKnown (j := 1005) oqLoopBody_852
    (by decide) (by decide) (by decide) walkOk_1005

end
end LeanVM.Guest.End
