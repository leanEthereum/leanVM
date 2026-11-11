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
theorem walk_925 : CutsKnown 925 :=
  loop0_cutsKnown (j := 925) oqLoopBody_496
    (by decide) (by decide) (by decide) walkOk_925

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1`. -/
theorem walk_516 : CutsKnown 516 :=
  main_cutsKnown (j := 516) oqBody_515
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_516

set_option maxRecDepth 100000 in
/-- `__loop347`. -/
theorem walk_929 : CutsKnown 929 :=
  loop0_cutsKnown (j := 929) oqLoopBody_515
    (by decide) (by decide) (by decide) walkOk_929

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1`. -/
theorem walk_536 : CutsKnown 536 :=
  main_cutsKnown (j := 536) oqBody_535
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_536

set_option maxRecDepth 100000 in
/-- `__loop351`. -/
theorem walk_933 : CutsKnown 933 :=
  loop0_cutsKnown (j := 933) oqLoopBody_535
    (by decide) (by decide) (by decide) walkOk_933

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1`. -/
theorem walk_558 : CutsKnown 558 :=
  main_cutsKnown (j := 558) oqBody_557
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_558

set_option maxRecDepth 100000 in
/-- `__loop355`. -/
theorem walk_937 : CutsKnown 937 :=
  loop0_cutsKnown (j := 937) oqLoopBody_557
    (by decide) (by decide) (by decide) walkOk_937

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1`. -/
theorem walk_576 : CutsKnown 576 :=
  main_cutsKnown (j := 576) oqBody_575
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_576

set_option maxRecDepth 100000 in
/-- `__loop359`. -/
theorem walk_941 : CutsKnown 941 :=
  loop0_cutsKnown (j := 941) oqLoopBody_575
    (by decide) (by decide) (by decide) walkOk_941

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1`. -/
theorem walk_593 : CutsKnown 593 :=
  main_cutsKnown (j := 593) oqBody_592
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_593

set_option maxRecDepth 100000 in
/-- `__loop363`. -/
theorem walk_945 : CutsKnown 945 :=
  loop0_cutsKnown (j := 945) oqLoopBody_592
    (by decide) (by decide) (by decide) walkOk_945

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1`. -/
theorem walk_612 : CutsKnown 612 :=
  main_cutsKnown (j := 612) oqBody_611
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_612

set_option maxRecDepth 100000 in
/-- `__loop367`. -/
theorem walk_949 : CutsKnown 949 :=
  loop0_cutsKnown (j := 949) oqLoopBody_611
    (by decide) (by decide) (by decide) walkOk_949

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1`. -/
theorem walk_635 : CutsKnown 635 :=
  main_cutsKnown (j := 635) oqBody_634
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_635

set_option maxRecDepth 100000 in
/-- `__loop371`. -/
theorem walk_955 : CutsKnown 955 :=
  loop0_cutsKnown (j := 955) oqLoopBody_634
    (by decide) (by decide) (by decide) walkOk_955

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1`. -/
theorem walk_658 : CutsKnown 658 :=
  main_cutsKnown (j := 658) oqBody_657
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_658

set_option maxRecDepth 100000 in
/-- `__loop375`. -/
theorem walk_961 : CutsKnown 961 :=
  loop0_cutsKnown (j := 961) oqLoopBody_657
    (by decide) (by decide) (by decide) walkOk_961

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1`. -/
theorem walk_682 : CutsKnown 682 :=
  main_cutsKnown (j := 682) oqBody_681
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_682

set_option maxRecDepth 100000 in
/-- `__loop379`. -/
theorem walk_967 : CutsKnown 967 :=
  loop0_cutsKnown (j := 967) oqLoopBody_681
    (by decide) (by decide) (by decide) walkOk_967

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0`. -/
theorem walk_699 : CutsKnown 699 :=
  main_cutsKnown (j := 699) oqBody_698
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_699

set_option maxRecDepth 100000 in
/-- `__loop383`. -/
theorem walk_972 : CutsKnown 972 :=
  loop0_cutsKnown (j := 972) oqLoopBody_698
    (by decide) (by decide) (by decide) walkOk_972

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1`. -/
theorem walk_729 : CutsKnown 729 :=
  main_cutsKnown (j := 729) oqBody_728
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_729

set_option maxRecDepth 100000 in
/-- `__loop387`. -/
theorem walk_976 : CutsKnown 976 :=
  loop0_cutsKnown (j := 976) oqLoopBody_728
    (by decide) (by decide) (by decide) walkOk_976

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem walk_766 : CutsKnown 766 :=
  main_cutsKnown (j := 766) oqBody_765
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_766

set_option maxRecDepth 100000 in
/-- `__loop391`. -/
theorem walk_981 : CutsKnown 981 :=
  loop1_cutsKnown (j := 981) oqLoopBody_765
    (by decide) (by decide) (by decide) (by decide) walkOk_981

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1`. -/
theorem walk_778 : CutsKnown 778 :=
  main_cutsKnown (j := 778) oqBody_777
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_778

set_option maxRecDepth 100000 in
/-- `__loop395`. -/
theorem walk_985 : CutsKnown 985 :=
  loop0_cutsKnown (j := 985) oqLoopBody_777
    (by decide) (by decide) (by decide) walkOk_985

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1`. -/
theorem walk_798 : CutsKnown 798 :=
  main_cutsKnown (j := 798) oqBody_797
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_798

set_option maxRecDepth 100000 in
/-- `__loop399`. -/
theorem walk_991 : CutsKnown 991 :=
  loop0_cutsKnown (j := 991) oqLoopBody_797
    (by decide) (by decide) (by decide) walkOk_991

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1`. -/
theorem walk_819 : CutsKnown 819 :=
  main_cutsKnown (j := 819) oqBody_818
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_819

set_option maxRecDepth 100000 in
/-- `__loop403`. -/
theorem walk_997 : CutsKnown 997 :=
  loop0_cutsKnown (j := 997) oqLoopBody_818
    (by decide) (by decide) (by decide) walkOk_997

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0`. -/
theorem walk_840 : CutsKnown 840 :=
  main_cutsKnown (j := 840) oqBody_839
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_840

set_option maxRecDepth 100000 in
/-- `__loop407`. -/
theorem walk_1003 : CutsKnown 1003 :=
  loop0_cutsKnown (j := 1003) oqLoopBody_839
    (by decide) (by decide) (by decide) walkOk_1003

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem walk_859 : CutsKnown 859 :=
  main_cutsKnown (j := 859) oqBody_858
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_859

set_option maxRecDepth 100000 in
/-- `__loop411`. -/
theorem walk_1008 : CutsKnown 1008 :=
  loop0_cutsKnown (j := 1008) oqLoopBody_858
    (by decide) (by decide) (by decide) walkOk_1008

end
end LeanVM.Guest.End
