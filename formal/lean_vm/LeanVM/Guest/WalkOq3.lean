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
theorem walk_497 : CutsKnown 497 :=
  main_cutsKnown (j := 497) oqBody_496
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_497

set_option maxRecDepth 100000 in
/-- `__loop343`. -/
theorem walk_924 : CutsKnown 924 :=
  loop0_cutsKnown (j := 924) oqLoopBody_496
    (by decide) (by decide) (by decide) walkOk_924

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1`. -/
theorem walk_516 : CutsKnown 516 :=
  main_cutsKnown (j := 516) oqBody_515
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_516

set_option maxRecDepth 100000 in
/-- `__loop347`. -/
theorem walk_928 : CutsKnown 928 :=
  loop0_cutsKnown (j := 928) oqLoopBody_515
    (by decide) (by decide) (by decide) walkOk_928

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1`. -/
theorem walk_536 : CutsKnown 536 :=
  main_cutsKnown (j := 536) oqBody_535
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_536

set_option maxRecDepth 100000 in
/-- `__loop351`. -/
theorem walk_932 : CutsKnown 932 :=
  loop0_cutsKnown (j := 932) oqLoopBody_535
    (by decide) (by decide) (by decide) walkOk_932

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1`. -/
theorem walk_558 : CutsKnown 558 :=
  main_cutsKnown (j := 558) oqBody_557
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_558

set_option maxRecDepth 100000 in
/-- `__loop355`. -/
theorem walk_936 : CutsKnown 936 :=
  loop0_cutsKnown (j := 936) oqLoopBody_557
    (by decide) (by decide) (by decide) walkOk_936

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1`. -/
theorem walk_576 : CutsKnown 576 :=
  main_cutsKnown (j := 576) oqBody_575
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_576

set_option maxRecDepth 100000 in
/-- `__loop359`. -/
theorem walk_940 : CutsKnown 940 :=
  loop0_cutsKnown (j := 940) oqLoopBody_575
    (by decide) (by decide) (by decide) walkOk_940

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1`. -/
theorem walk_593 : CutsKnown 593 :=
  main_cutsKnown (j := 593) oqBody_592
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_593

set_option maxRecDepth 100000 in
/-- `__loop363`. -/
theorem walk_944 : CutsKnown 944 :=
  loop0_cutsKnown (j := 944) oqLoopBody_592
    (by decide) (by decide) (by decide) walkOk_944

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1`. -/
theorem walk_612 : CutsKnown 612 :=
  main_cutsKnown (j := 612) oqBody_611
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_612

set_option maxRecDepth 100000 in
/-- `__loop367`. -/
theorem walk_948 : CutsKnown 948 :=
  loop0_cutsKnown (j := 948) oqLoopBody_611
    (by decide) (by decide) (by decide) walkOk_948

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1`. -/
theorem walk_635 : CutsKnown 635 :=
  main_cutsKnown (j := 635) oqBody_634
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_635

set_option maxRecDepth 100000 in
/-- `__loop371`. -/
theorem walk_954 : CutsKnown 954 :=
  loop0_cutsKnown (j := 954) oqLoopBody_634
    (by decide) (by decide) (by decide) walkOk_954

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1`. -/
theorem walk_658 : CutsKnown 658 :=
  main_cutsKnown (j := 658) oqBody_657
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_658

set_option maxRecDepth 100000 in
/-- `__loop375`. -/
theorem walk_960 : CutsKnown 960 :=
  loop0_cutsKnown (j := 960) oqLoopBody_657
    (by decide) (by decide) (by decide) walkOk_960

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1`. -/
theorem walk_682 : CutsKnown 682 :=
  main_cutsKnown (j := 682) oqBody_681
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_682

set_option maxRecDepth 100000 in
/-- `__loop379`. -/
theorem walk_966 : CutsKnown 966 :=
  loop0_cutsKnown (j := 966) oqLoopBody_681
    (by decide) (by decide) (by decide) walkOk_966

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1`. -/
theorem walk_700 : CutsKnown 700 :=
  main_cutsKnown (j := 700) oqBody_699
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_700

set_option maxRecDepth 100000 in
/-- `__loop383`. -/
theorem walk_971 : CutsKnown 971 :=
  loop0_cutsKnown (j := 971) oqLoopBody_699
    (by decide) (by decide) (by decide) walkOk_971

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1`. -/
theorem walk_737 : CutsKnown 737 :=
  main_cutsKnown (j := 737) oqBody_736
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_737

set_option maxRecDepth 100000 in
/-- `__loop387`. -/
theorem walk_975 : CutsKnown 975 :=
  loop0_cutsKnown (j := 975) oqLoopBody_736
    (by decide) (by decide) (by decide) walkOk_975

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem walk_768 : CutsKnown 768 :=
  main_cutsKnown (j := 768) oqBody_767
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_768

set_option maxRecDepth 100000 in
/-- `__loop391`. -/
theorem walk_980 : CutsKnown 980 :=
  loop0_cutsKnown (j := 980) oqLoopBody_767
    (by decide) (by decide) (by decide) walkOk_980

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0`. -/
theorem walk_784 : CutsKnown 784 :=
  main_cutsKnown (j := 784) oqBody_783
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_784

set_option maxRecDepth 100000 in
/-- `__loop395`. -/
theorem walk_985 : CutsKnown 985 :=
  loop1_cutsKnown (j := 985) oqLoopBody_783
    (by decide) (by decide) (by decide) (by decide) walkOk_985

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0`. -/
theorem walk_802 : CutsKnown 802 :=
  main_cutsKnown (j := 802) oqBody_801
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_802

set_option maxRecDepth 100000 in
/-- `__loop399`. -/
theorem walk_991 : CutsKnown 991 :=
  loop1_cutsKnown (j := 991) oqLoopBody_801
    (by decide) (by decide) (by decide) (by decide) walkOk_991

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem walk_824 : CutsKnown 824 :=
  main_cutsKnown (j := 824) oqBody_823
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_824

set_option maxRecDepth 100000 in
/-- `__loop403`. -/
theorem walk_997 : CutsKnown 997 :=
  loop1_cutsKnown (j := 997) oqLoopBody_823
    (by decide) (by decide) (by decide) (by decide) walkOk_997

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1`. -/
theorem walk_843 : CutsKnown 843 :=
  main_cutsKnown (j := 843) oqBody_842
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_843

set_option maxRecDepth 100000 in
/-- `__loop407`. -/
theorem walk_1002 : CutsKnown 1002 :=
  loop0_cutsKnown (j := 1002) oqLoopBody_842
    (by decide) (by decide) (by decide) walkOk_1002

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1`. -/
theorem walk_860 : CutsKnown 860 :=
  main_cutsKnown (j := 860) oqBody_859
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_860

set_option maxRecDepth 100000 in
/-- `__loop411`. -/
theorem walk_1007 : CutsKnown 1007 :=
  loop0_cutsKnown (j := 1007) oqLoopBody_859
    (by decide) (by decide) (by decide) walkOk_1007

end
end LeanVM.Guest.End
