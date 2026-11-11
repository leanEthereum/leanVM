/-
  LeanVM.Guest.WalkOq2

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody2.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk2.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk2
public import LeanVM.Guest.B1.Opening.QueriesBody2

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L0_L0_L0_L0_L0`. -/
theorem walk_493 : CutsKnown 493 :=
  main_cutsKnown (j := 493) oqBody_492
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_493

set_option maxRecDepth 100000 in
/-- `__loop342`. -/
theorem walk_923 : CutsKnown 923 :=
  loop0_cutsKnown (j := 923) oqLoopBody_492
    (by decide) (by decide) (by decide) walkOk_923

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0`. -/
theorem walk_513 : CutsKnown 513 :=
  main_cutsKnown (j := 513) oqBody_512
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_513

set_option maxRecDepth 100000 in
/-- `__loop346`. -/
theorem walk_927 : CutsKnown 927 :=
  loop0_cutsKnown (j := 927) oqLoopBody_512
    (by decide) (by decide) (by decide) walkOk_927

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem walk_532 : CutsKnown 532 :=
  main_cutsKnown (j := 532) oqBody_531
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_532

set_option maxRecDepth 100000 in
/-- `__loop350`. -/
theorem walk_931 : CutsKnown 931 :=
  loop0_cutsKnown (j := 931) oqLoopBody_531
    (by decide) (by decide) (by decide) walkOk_931

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0`. -/
theorem walk_553 : CutsKnown 553 :=
  main_cutsKnown (j := 553) oqBody_552
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_553

set_option maxRecDepth 100000 in
/-- `__loop354`. -/
theorem walk_935 : CutsKnown 935 :=
  loop0_cutsKnown (j := 935) oqLoopBody_552
    (by decide) (by decide) (by decide) walkOk_935

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0`. -/
theorem walk_573 : CutsKnown 573 :=
  main_cutsKnown (j := 573) oqBody_572
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_573

set_option maxRecDepth 100000 in
/-- `__loop358`. -/
theorem walk_939 : CutsKnown 939 :=
  loop0_cutsKnown (j := 939) oqLoopBody_572
    (by decide) (by decide) (by decide) walkOk_939

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0`. -/
theorem walk_590 : CutsKnown 590 :=
  main_cutsKnown (j := 590) oqBody_589
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_590

set_option maxRecDepth 100000 in
/-- `__loop362`. -/
theorem walk_943 : CutsKnown 943 :=
  loop0_cutsKnown (j := 943) oqLoopBody_589
    (by decide) (by decide) (by decide) walkOk_943

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0`. -/
theorem walk_606 : CutsKnown 606 :=
  main_cutsKnown (j := 606) oqBody_605
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_606

set_option maxRecDepth 100000 in
/-- `__loop366`. -/
theorem walk_947 : CutsKnown 947 :=
  loop0_cutsKnown (j := 947) oqLoopBody_605
    (by decide) (by decide) (by decide) walkOk_947

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_631 : CutsKnown 631 :=
  main_cutsKnown (j := 631) oqBody_630
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_631

set_option maxRecDepth 100000 in
/-- `__loop370`. -/
theorem walk_953 : CutsKnown 953 :=
  loop1_cutsKnown (j := 953) oqLoopBody_630
    (by decide) (by decide) (by decide) (by decide) walkOk_953

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0`. -/
theorem walk_653 : CutsKnown 653 :=
  main_cutsKnown (j := 653) oqBody_652
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_653

set_option maxRecDepth 100000 in
/-- `__loop374`. -/
theorem walk_959 : CutsKnown 959 :=
  loop1_cutsKnown (j := 959) oqLoopBody_652
    (by decide) (by decide) (by decide) (by decide) walkOk_959

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0`. -/
theorem walk_677 : CutsKnown 677 :=
  main_cutsKnown (j := 677) oqBody_676
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_677

set_option maxRecDepth 100000 in
/-- `__loop378`. -/
theorem walk_965 : CutsKnown 965 :=
  loop1_cutsKnown (j := 965) oqLoopBody_676
    (by decide) (by decide) (by decide) (by decide) walkOk_965

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0`. -/
theorem walk_695 : CutsKnown 695 :=
  main_cutsKnown (j := 695) oqBody_694
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_695

set_option maxRecDepth 100000 in
/-- `__loop382`. -/
theorem walk_970 : CutsKnown 970 :=
  loop0_cutsKnown (j := 970) oqLoopBody_694
    (by decide) (by decide) (by decide) walkOk_970

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1`. -/
theorem walk_727 : CutsKnown 727 :=
  main_cutsKnown (j := 727) oqBody_726
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_727

set_option maxRecDepth 100000 in
/-- `__loop386`. -/
theorem walk_974 : CutsKnown 974 :=
  loop0_cutsKnown (j := 974) oqLoopBody_726
    (by decide) (by decide) (by decide) walkOk_974

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem walk_765 : CutsKnown 765 :=
  main_cutsKnown (j := 765) oqBody_764
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_765

set_option maxRecDepth 100000 in
/-- `__loop390`. -/
theorem walk_979 : CutsKnown 979 :=
  loop1_cutsKnown (j := 979) oqLoopBody_764
    (by decide) (by decide) (by decide) (by decide) walkOk_979

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1`. -/
theorem walk_777 : CutsKnown 777 :=
  main_cutsKnown (j := 777) oqBody_776
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_777

set_option maxRecDepth 100000 in
/-- `__loop394`. -/
theorem walk_983 : CutsKnown 983 :=
  loop0_cutsKnown (j := 983) oqLoopBody_776
    (by decide) (by decide) (by decide) walkOk_983

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1`. -/
theorem walk_797 : CutsKnown 797 :=
  main_cutsKnown (j := 797) oqBody_796
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_797

set_option maxRecDepth 100000 in
/-- `__loop398`. -/
theorem walk_989 : CutsKnown 989 :=
  loop0_cutsKnown (j := 989) oqLoopBody_796
    (by decide) (by decide) (by decide) walkOk_989

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1`. -/
theorem walk_818 : CutsKnown 818 :=
  main_cutsKnown (j := 818) oqBody_817
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_818

set_option maxRecDepth 100000 in
/-- `__loop402`. -/
theorem walk_995 : CutsKnown 995 :=
  loop0_cutsKnown (j := 995) oqLoopBody_817
    (by decide) (by decide) (by decide) walkOk_995

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0`. -/
theorem walk_839 : CutsKnown 839 :=
  main_cutsKnown (j := 839) oqBody_838
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_839

set_option maxRecDepth 100000 in
/-- `__loop406`. -/
theorem walk_1001 : CutsKnown 1001 :=
  loop0_cutsKnown (j := 1001) oqLoopBody_838
    (by decide) (by decide) (by decide) walkOk_1001

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem walk_858 : CutsKnown 858 :=
  main_cutsKnown (j := 858) oqBody_857
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_858

set_option maxRecDepth 100000 in
/-- `__loop410`. -/
theorem walk_1006 : CutsKnown 1006 :=
  loop0_cutsKnown (j := 1006) oqLoopBody_857
    (by decide) (by decide) (by decide) walkOk_1006

end
end LeanVM.Guest.End
