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
/-- `opening_queries__L0_L0_L4_L16_L14_L5_L4_L39_L20_L5_L1`. -/
theorem walk_500 : CutsKnown 500 :=
  main_cutsKnown (j := 500) oqBody_499
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_500

set_option maxRecDepth 100000 in
/-- `__loop343`. -/
theorem walk_943 : CutsKnown 943 :=
  loop0_cutsKnown (j := 943) oqLoopBody_499
    (by decide) (by decide) (by decide) walkOk_943

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1`. -/
theorem walk_522 : CutsKnown 522 :=
  main_cutsKnown (j := 522) oqBody_521
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_522

set_option maxRecDepth 100000 in
/-- `__loop347`. -/
theorem walk_948 : CutsKnown 948 :=
  loop0_cutsKnown (j := 948) oqLoopBody_521
    (by decide) (by decide) (by decide) walkOk_948

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1`. -/
theorem walk_547 : CutsKnown 547 :=
  main_cutsKnown (j := 547) oqBody_546
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_547

set_option maxRecDepth 100000 in
/-- `__loop351`. -/
theorem walk_953 : CutsKnown 953 :=
  loop0_cutsKnown (j := 953) oqLoopBody_546
    (by decide) (by decide) (by decide) walkOk_953

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1`. -/
theorem walk_573 : CutsKnown 573 :=
  main_cutsKnown (j := 573) oqBody_572
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_573

set_option maxRecDepth 100000 in
/-- `__loop355`. -/
theorem walk_958 : CutsKnown 958 :=
  loop0_cutsKnown (j := 958) oqLoopBody_572
    (by decide) (by decide) (by decide) walkOk_958

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1`. -/
theorem walk_592 : CutsKnown 592 :=
  main_cutsKnown (j := 592) oqBody_591
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_592

set_option maxRecDepth 100000 in
/-- `__loop359`. -/
theorem walk_963 : CutsKnown 963 :=
  loop0_cutsKnown (j := 963) oqLoopBody_591
    (by decide) (by decide) (by decide) walkOk_963

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1`. -/
theorem walk_610 : CutsKnown 610 :=
  main_cutsKnown (j := 610) oqBody_609
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_610

set_option maxRecDepth 100000 in
/-- `__loop363`. -/
theorem walk_968 : CutsKnown 968 :=
  loop0_cutsKnown (j := 968) oqLoopBody_609
    (by decide) (by decide) (by decide) walkOk_968

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1`. -/
theorem walk_630 : CutsKnown 630 :=
  main_cutsKnown (j := 630) oqBody_629
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_630

set_option maxRecDepth 100000 in
/-- `__loop367`. -/
theorem walk_973 : CutsKnown 973 :=
  loop0_cutsKnown (j := 973) oqLoopBody_629
    (by decide) (by decide) (by decide) walkOk_973

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1`. -/
theorem walk_653 : CutsKnown 653 :=
  main_cutsKnown (j := 653) oqBody_652
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_653

set_option maxRecDepth 100000 in
/-- `__loop371`. -/
theorem walk_979 : CutsKnown 979 :=
  loop0_cutsKnown (j := 979) oqLoopBody_652
    (by decide) (by decide) (by decide) walkOk_979

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1`. -/
theorem walk_676 : CutsKnown 676 :=
  main_cutsKnown (j := 676) oqBody_675
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_676

set_option maxRecDepth 100000 in
/-- `__loop375`. -/
theorem walk_985 : CutsKnown 985 :=
  loop0_cutsKnown (j := 985) oqLoopBody_675
    (by decide) (by decide) (by decide) walkOk_985

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1`. -/
theorem walk_700 : CutsKnown 700 :=
  main_cutsKnown (j := 700) oqBody_699
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_700

set_option maxRecDepth 100000 in
/-- `__loop379`. -/
theorem walk_991 : CutsKnown 991 :=
  loop0_cutsKnown (j := 991) oqLoopBody_699
    (by decide) (by decide) (by decide) walkOk_991

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0`. -/
theorem walk_717 : CutsKnown 717 :=
  main_cutsKnown (j := 717) oqBody_716
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_717

set_option maxRecDepth 100000 in
/-- `__loop383`. -/
theorem walk_996 : CutsKnown 996 :=
  loop0_cutsKnown (j := 996) oqLoopBody_716
    (by decide) (by decide) (by decide) walkOk_996

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1`. -/
theorem walk_747 : CutsKnown 747 :=
  main_cutsKnown (j := 747) oqBody_746
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_747

set_option maxRecDepth 100000 in
/-- `__loop387`. -/
theorem walk_1000 : CutsKnown 1000 :=
  loop0_cutsKnown (j := 1000) oqLoopBody_746
    (by decide) (by decide) (by decide) walkOk_1000

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem walk_784 : CutsKnown 784 :=
  main_cutsKnown (j := 784) oqBody_783
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_784

set_option maxRecDepth 100000 in
/-- `__loop391`. -/
theorem walk_1005 : CutsKnown 1005 :=
  loop1_cutsKnown (j := 1005) oqLoopBody_783
    (by decide) (by decide) (by decide) (by decide) walkOk_1005

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1`. -/
theorem walk_796 : CutsKnown 796 :=
  main_cutsKnown (j := 796) oqBody_795
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_796

set_option maxRecDepth 100000 in
/-- `__loop395`. -/
theorem walk_1009 : CutsKnown 1009 :=
  loop0_cutsKnown (j := 1009) oqLoopBody_795
    (by decide) (by decide) (by decide) walkOk_1009

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1`. -/
theorem walk_816 : CutsKnown 816 :=
  main_cutsKnown (j := 816) oqBody_815
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_816

set_option maxRecDepth 100000 in
/-- `__loop399`. -/
theorem walk_1015 : CutsKnown 1015 :=
  loop0_cutsKnown (j := 1015) oqLoopBody_815
    (by decide) (by decide) (by decide) walkOk_1015

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1`. -/
theorem walk_837 : CutsKnown 837 :=
  main_cutsKnown (j := 837) oqBody_836
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_837

set_option maxRecDepth 100000 in
/-- `__loop403`. -/
theorem walk_1021 : CutsKnown 1021 :=
  loop0_cutsKnown (j := 1021) oqLoopBody_836
    (by decide) (by decide) (by decide) walkOk_1021

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0`. -/
theorem walk_858 : CutsKnown 858 :=
  main_cutsKnown (j := 858) oqBody_857
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_858

set_option maxRecDepth 100000 in
/-- `__loop407`. -/
theorem walk_1027 : CutsKnown 1027 :=
  loop0_cutsKnown (j := 1027) oqLoopBody_857
    (by decide) (by decide) (by decide) walkOk_1027

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem walk_877 : CutsKnown 877 :=
  main_cutsKnown (j := 877) oqBody_876
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_877

set_option maxRecDepth 100000 in
/-- `__loop411`. -/
theorem walk_1032 : CutsKnown 1032 :=
  loop0_cutsKnown (j := 1032) oqLoopBody_876
    (by decide) (by decide) (by decide) walkOk_1032

end
end LeanVM.Guest.End
