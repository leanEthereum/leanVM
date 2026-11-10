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
theorem walk_490 : CutsKnown 490 :=
  main_cutsKnown (j := 490) oqBody_489
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_490

set_option maxRecDepth 100000 in
/-- `__loop341`. -/
theorem walk_941 : CutsKnown 941 :=
  loop0_cutsKnown (j := 941) oqLoopBody_489
    (by decide) (by decide) (by decide) walkOk_941

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0`. -/
theorem walk_514 : CutsKnown 514 :=
  main_cutsKnown (j := 514) oqBody_513
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_514

set_option maxRecDepth 100000 in
/-- `__loop345`. -/
theorem walk_946 : CutsKnown 946 :=
  loop0_cutsKnown (j := 946) oqLoopBody_513
    (by decide) (by decide) (by decide) walkOk_946

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem walk_536 : CutsKnown 536 :=
  main_cutsKnown (j := 536) oqBody_535
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_536

set_option maxRecDepth 100000 in
/-- `__loop349`. -/
theorem walk_951 : CutsKnown 951 :=
  loop0_cutsKnown (j := 951) oqLoopBody_535
    (by decide) (by decide) (by decide) walkOk_951

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0`. -/
theorem walk_562 : CutsKnown 562 :=
  main_cutsKnown (j := 562) oqBody_561
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_562

set_option maxRecDepth 100000 in
/-- `__loop353`. -/
theorem walk_956 : CutsKnown 956 :=
  loop0_cutsKnown (j := 956) oqLoopBody_561
    (by decide) (by decide) (by decide) walkOk_956

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0`. -/
theorem walk_586 : CutsKnown 586 :=
  main_cutsKnown (j := 586) oqBody_585
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_586

set_option maxRecDepth 100000 in
/-- `__loop357`. -/
theorem walk_961 : CutsKnown 961 :=
  loop0_cutsKnown (j := 961) oqLoopBody_585
    (by decide) (by decide) (by decide) walkOk_961

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_604 : CutsKnown 604 :=
  main_cutsKnown (j := 604) oqBody_603
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_604

set_option maxRecDepth 100000 in
/-- `__loop361`. -/
theorem walk_966 : CutsKnown 966 :=
  loop0_cutsKnown (j := 966) oqLoopBody_603
    (by decide) (by decide) (by decide) walkOk_966

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0`. -/
theorem walk_621 : CutsKnown 621 :=
  main_cutsKnown (j := 621) oqBody_620
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_621

set_option maxRecDepth 100000 in
/-- `__loop365`. -/
theorem walk_971 : CutsKnown 971 :=
  loop0_cutsKnown (j := 971) oqLoopBody_620
    (by decide) (by decide) (by decide) walkOk_971

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1`. -/
theorem walk_643 : CutsKnown 643 :=
  main_cutsKnown (j := 643) oqBody_642
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_643

set_option maxRecDepth 100000 in
/-- `__loop369`. -/
theorem walk_976 : CutsKnown 976 :=
  loop0_cutsKnown (j := 976) oqLoopBody_642
    (by decide) (by decide) (by decide) walkOk_976

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1`. -/
theorem walk_664 : CutsKnown 664 :=
  main_cutsKnown (j := 664) oqBody_663
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_664

set_option maxRecDepth 100000 in
/-- `__loop373`. -/
theorem walk_982 : CutsKnown 982 :=
  loop0_cutsKnown (j := 982) oqLoopBody_663
    (by decide) (by decide) (by decide) walkOk_982

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1`. -/
theorem walk_688 : CutsKnown 688 :=
  main_cutsKnown (j := 688) oqBody_687
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_688

set_option maxRecDepth 100000 in
/-- `__loop377`. -/
theorem walk_988 : CutsKnown 988 :=
  loop0_cutsKnown (j := 988) oqLoopBody_687
    (by decide) (by decide) (by decide) walkOk_988

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_710 : CutsKnown 710 :=
  main_cutsKnown (j := 710) oqBody_709
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_710

set_option maxRecDepth 100000 in
/-- `__loop381`. -/
theorem walk_994 : CutsKnown 994 :=
  loop0_cutsKnown (j := 994) oqLoopBody_709
    (by decide) (by decide) (by decide) walkOk_994

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L4_L1131_L20_L5_L1`. -/
theorem walk_730 : CutsKnown 730 :=
  main_cutsKnown (j := 730) oqBody_729
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_730

set_option maxRecDepth 100000 in
/-- `__loop385`. -/
theorem walk_998 : CutsKnown 998 :=
  loop0_cutsKnown (j := 998) oqLoopBody_729
    (by decide) (by decide) (by decide) walkOk_998

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L4_L1464_L20_L5_L1`. -/
theorem walk_767 : CutsKnown 767 :=
  main_cutsKnown (j := 767) oqBody_766
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_767

set_option maxRecDepth 100000 in
/-- `__loop389`. -/
theorem walk_1002 : CutsKnown 1002 :=
  loop0_cutsKnown (j := 1002) oqLoopBody_766
    (by decide) (by decide) (by decide) walkOk_1002

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem walk_790 : CutsKnown 790 :=
  main_cutsKnown (j := 790) oqBody_789
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_790

set_option maxRecDepth 100000 in
/-- `__loop393`. -/
theorem walk_1007 : CutsKnown 1007 :=
  loop0_cutsKnown (j := 1007) oqLoopBody_789
    (by decide) (by decide) (by decide) walkOk_1007

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L1677_L20_L5_L1`. -/
theorem walk_807 : CutsKnown 807 :=
  main_cutsKnown (j := 807) oqBody_806
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_807

set_option maxRecDepth 100000 in
/-- `__loop397`. -/
theorem walk_1012 : CutsKnown 1012 :=
  loop0_cutsKnown (j := 1012) oqLoopBody_806
    (by decide) (by decide) (by decide) walkOk_1012

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L1846_L8_L3_L1`. -/
theorem walk_826 : CutsKnown 826 :=
  main_cutsKnown (j := 826) oqBody_825
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_826

set_option maxRecDepth 100000 in
/-- `__loop401`. -/
theorem walk_1018 : CutsKnown 1018 :=
  loop0_cutsKnown (j := 1018) oqLoopBody_825
    (by decide) (by decide) (by decide) walkOk_1018

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L4_L2010_L20_L5_L1`. -/
theorem walk_848 : CutsKnown 848 :=
  main_cutsKnown (j := 848) oqBody_847
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_848

set_option maxRecDepth 100000 in
/-- `__loop405`. -/
theorem walk_1024 : CutsKnown 1024 :=
  loop0_cutsKnown (j := 1024) oqLoopBody_847
    (by decide) (by decide) (by decide) walkOk_1024

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L6_L0_L0_L0_L0_L0`. -/
theorem walk_869 : CutsKnown 869 :=
  main_cutsKnown (j := 869) oqBody_868
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_869

set_option maxRecDepth 100000 in
/-- `__loop409`. -/
theorem walk_1030 : CutsKnown 1030 :=
  loop1_cutsKnown (j := 1030) oqLoopBody_868
    (by decide) (by decide) (by decide) (by decide) walkOk_1030

end
end LeanVM.Guest.End
