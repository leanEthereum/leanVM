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
theorem walk_923 : CutsKnown 923 :=
  loop0_cutsKnown (j := 923) oqLoopBody_487
    (by decide) (by decide) (by decide) walkOk_923

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0`. -/
theorem walk_509 : CutsKnown 509 :=
  main_cutsKnown (j := 509) oqBody_508
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_509

set_option maxRecDepth 100000 in
/-- `__loop345`. -/
theorem walk_927 : CutsKnown 927 :=
  loop0_cutsKnown (j := 927) oqLoopBody_508
    (by decide) (by decide) (by decide) walkOk_927

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem walk_528 : CutsKnown 528 :=
  main_cutsKnown (j := 528) oqBody_527
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_528

set_option maxRecDepth 100000 in
/-- `__loop349`. -/
theorem walk_931 : CutsKnown 931 :=
  loop0_cutsKnown (j := 931) oqLoopBody_527
    (by decide) (by decide) (by decide) walkOk_931

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0`. -/
theorem walk_549 : CutsKnown 549 :=
  main_cutsKnown (j := 549) oqBody_548
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_549

set_option maxRecDepth 100000 in
/-- `__loop353`. -/
theorem walk_935 : CutsKnown 935 :=
  loop0_cutsKnown (j := 935) oqLoopBody_548
    (by decide) (by decide) (by decide) walkOk_935

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0`. -/
theorem walk_570 : CutsKnown 570 :=
  main_cutsKnown (j := 570) oqBody_569
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_570

set_option maxRecDepth 100000 in
/-- `__loop357`. -/
theorem walk_939 : CutsKnown 939 :=
  loop0_cutsKnown (j := 939) oqLoopBody_569
    (by decide) (by decide) (by decide) walkOk_939

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_587 : CutsKnown 587 :=
  main_cutsKnown (j := 587) oqBody_586
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_587

set_option maxRecDepth 100000 in
/-- `__loop361`. -/
theorem walk_943 : CutsKnown 943 :=
  loop0_cutsKnown (j := 943) oqLoopBody_586
    (by decide) (by decide) (by decide) walkOk_943

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0`. -/
theorem walk_603 : CutsKnown 603 :=
  main_cutsKnown (j := 603) oqBody_602
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_603

set_option maxRecDepth 100000 in
/-- `__loop365`. -/
theorem walk_947 : CutsKnown 947 :=
  loop0_cutsKnown (j := 947) oqLoopBody_602
    (by decide) (by decide) (by decide) walkOk_947

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1`. -/
theorem walk_625 : CutsKnown 625 :=
  main_cutsKnown (j := 625) oqBody_624
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_625

set_option maxRecDepth 100000 in
/-- `__loop369`. -/
theorem walk_952 : CutsKnown 952 :=
  loop0_cutsKnown (j := 952) oqLoopBody_624
    (by decide) (by decide) (by decide) walkOk_952

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1`. -/
theorem walk_646 : CutsKnown 646 :=
  main_cutsKnown (j := 646) oqBody_645
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_646

set_option maxRecDepth 100000 in
/-- `__loop373`. -/
theorem walk_958 : CutsKnown 958 :=
  loop0_cutsKnown (j := 958) oqLoopBody_645
    (by decide) (by decide) (by decide) walkOk_958

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1`. -/
theorem walk_670 : CutsKnown 670 :=
  main_cutsKnown (j := 670) oqBody_669
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_670

set_option maxRecDepth 100000 in
/-- `__loop377`. -/
theorem walk_964 : CutsKnown 964 :=
  loop0_cutsKnown (j := 964) oqLoopBody_669
    (by decide) (by decide) (by decide) walkOk_964

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_692 : CutsKnown 692 :=
  main_cutsKnown (j := 692) oqBody_691
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_692

set_option maxRecDepth 100000 in
/-- `__loop381`. -/
theorem walk_970 : CutsKnown 970 :=
  loop0_cutsKnown (j := 970) oqLoopBody_691
    (by decide) (by decide) (by decide) walkOk_970

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L4_L1131_L20_L5_L1`. -/
theorem walk_712 : CutsKnown 712 :=
  main_cutsKnown (j := 712) oqBody_711
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_712

set_option maxRecDepth 100000 in
/-- `__loop385`. -/
theorem walk_974 : CutsKnown 974 :=
  loop0_cutsKnown (j := 974) oqLoopBody_711
    (by decide) (by decide) (by decide) walkOk_974

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L4_L1464_L20_L5_L1`. -/
theorem walk_749 : CutsKnown 749 :=
  main_cutsKnown (j := 749) oqBody_748
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_749

set_option maxRecDepth 100000 in
/-- `__loop389`. -/
theorem walk_978 : CutsKnown 978 :=
  loop0_cutsKnown (j := 978) oqLoopBody_748
    (by decide) (by decide) (by decide) walkOk_978

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem walk_772 : CutsKnown 772 :=
  main_cutsKnown (j := 772) oqBody_771
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_772

set_option maxRecDepth 100000 in
/-- `__loop393`. -/
theorem walk_983 : CutsKnown 983 :=
  loop0_cutsKnown (j := 983) oqLoopBody_771
    (by decide) (by decide) (by decide) walkOk_983

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L1677_L20_L5_L1`. -/
theorem walk_789 : CutsKnown 789 :=
  main_cutsKnown (j := 789) oqBody_788
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_789

set_option maxRecDepth 100000 in
/-- `__loop397`. -/
theorem walk_988 : CutsKnown 988 :=
  loop0_cutsKnown (j := 988) oqLoopBody_788
    (by decide) (by decide) (by decide) walkOk_988

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L1846_L8_L3_L1`. -/
theorem walk_808 : CutsKnown 808 :=
  main_cutsKnown (j := 808) oqBody_807
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_808

set_option maxRecDepth 100000 in
/-- `__loop401`. -/
theorem walk_994 : CutsKnown 994 :=
  loop0_cutsKnown (j := 994) oqLoopBody_807
    (by decide) (by decide) (by decide) walkOk_994

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L4_L2010_L20_L5_L1`. -/
theorem walk_830 : CutsKnown 830 :=
  main_cutsKnown (j := 830) oqBody_829
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_830

set_option maxRecDepth 100000 in
/-- `__loop405`. -/
theorem walk_1000 : CutsKnown 1000 :=
  loop0_cutsKnown (j := 1000) oqLoopBody_829
    (by decide) (by decide) (by decide) walkOk_1000

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L6_L0_L0_L0_L0_L0`. -/
theorem walk_851 : CutsKnown 851 :=
  main_cutsKnown (j := 851) oqBody_850
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_851

set_option maxRecDepth 100000 in
/-- `__loop409`. -/
theorem walk_1006 : CutsKnown 1006 :=
  loop1_cutsKnown (j := 1006) oqLoopBody_850
    (by decide) (by decide) (by decide) (by decide) walkOk_1006

end
end LeanVM.Guest.End
