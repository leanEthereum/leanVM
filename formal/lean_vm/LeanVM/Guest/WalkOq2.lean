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
theorem walk_924 : CutsKnown 924 :=
  loop0_cutsKnown (j := 924) oqLoopBody_492
    (by decide) (by decide) (by decide) walkOk_924

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0`. -/
theorem walk_513 : CutsKnown 513 :=
  main_cutsKnown (j := 513) oqBody_512
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_513

set_option maxRecDepth 100000 in
/-- `__loop346`. -/
theorem walk_928 : CutsKnown 928 :=
  loop0_cutsKnown (j := 928) oqLoopBody_512
    (by decide) (by decide) (by decide) walkOk_928

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem walk_532 : CutsKnown 532 :=
  main_cutsKnown (j := 532) oqBody_531
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_532

set_option maxRecDepth 100000 in
/-- `__loop350`. -/
theorem walk_932 : CutsKnown 932 :=
  loop0_cutsKnown (j := 932) oqLoopBody_531
    (by decide) (by decide) (by decide) walkOk_932

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0`. -/
theorem walk_553 : CutsKnown 553 :=
  main_cutsKnown (j := 553) oqBody_552
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_553

set_option maxRecDepth 100000 in
/-- `__loop354`. -/
theorem walk_936 : CutsKnown 936 :=
  loop0_cutsKnown (j := 936) oqLoopBody_552
    (by decide) (by decide) (by decide) walkOk_936

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0`. -/
theorem walk_573 : CutsKnown 573 :=
  main_cutsKnown (j := 573) oqBody_572
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_573

set_option maxRecDepth 100000 in
/-- `__loop358`. -/
theorem walk_940 : CutsKnown 940 :=
  loop0_cutsKnown (j := 940) oqLoopBody_572
    (by decide) (by decide) (by decide) walkOk_940

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0`. -/
theorem walk_590 : CutsKnown 590 :=
  main_cutsKnown (j := 590) oqBody_589
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_590

set_option maxRecDepth 100000 in
/-- `__loop362`. -/
theorem walk_944 : CutsKnown 944 :=
  loop0_cutsKnown (j := 944) oqLoopBody_589
    (by decide) (by decide) (by decide) walkOk_944

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0`. -/
theorem walk_606 : CutsKnown 606 :=
  main_cutsKnown (j := 606) oqBody_605
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_606

set_option maxRecDepth 100000 in
/-- `__loop366`. -/
theorem walk_948 : CutsKnown 948 :=
  loop0_cutsKnown (j := 948) oqLoopBody_605
    (by decide) (by decide) (by decide) walkOk_948

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_631 : CutsKnown 631 :=
  main_cutsKnown (j := 631) oqBody_630
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_631

set_option maxRecDepth 100000 in
/-- `__loop370`. -/
theorem walk_954 : CutsKnown 954 :=
  loop1_cutsKnown (j := 954) oqLoopBody_630
    (by decide) (by decide) (by decide) (by decide) walkOk_954

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0`. -/
theorem walk_653 : CutsKnown 653 :=
  main_cutsKnown (j := 653) oqBody_652
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_653

set_option maxRecDepth 100000 in
/-- `__loop374`. -/
theorem walk_960 : CutsKnown 960 :=
  loop1_cutsKnown (j := 960) oqLoopBody_652
    (by decide) (by decide) (by decide) (by decide) walkOk_960

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0`. -/
theorem walk_677 : CutsKnown 677 :=
  main_cutsKnown (j := 677) oqBody_676
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_677

set_option maxRecDepth 100000 in
/-- `__loop378`. -/
theorem walk_966 : CutsKnown 966 :=
  loop1_cutsKnown (j := 966) oqLoopBody_676
    (by decide) (by decide) (by decide) (by decide) walkOk_966

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0`. -/
theorem walk_695 : CutsKnown 695 :=
  main_cutsKnown (j := 695) oqBody_694
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_695

set_option maxRecDepth 100000 in
/-- `__loop382`. -/
theorem walk_971 : CutsKnown 971 :=
  loop0_cutsKnown (j := 971) oqLoopBody_694
    (by decide) (by decide) (by decide) walkOk_971

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem walk_720 : CutsKnown 720 :=
  main_cutsKnown (j := 720) oqBody_719
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_720

set_option maxRecDepth 100000 in
/-- `__loop386`. -/
theorem walk_975 : CutsKnown 975 :=
  loop0_cutsKnown (j := 975) oqLoopBody_719
    (by decide) (by decide) (by decide) walkOk_975

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem walk_759 : CutsKnown 759 :=
  main_cutsKnown (j := 759) oqBody_758
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_759

set_option maxRecDepth 100000 in
/-- `__loop390`. -/
theorem walk_979 : CutsKnown 979 :=
  loop0_cutsKnown (j := 979) oqLoopBody_758
    (by decide) (by decide) (by decide) walkOk_979

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem walk_776 : CutsKnown 776 :=
  main_cutsKnown (j := 776) oqBody_775
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_776

set_option maxRecDepth 100000 in
/-- `__loop394`. -/
theorem walk_984 : CutsKnown 984 :=
  loop0_cutsKnown (j := 984) oqLoopBody_775
    (by decide) (by decide) (by decide) walkOk_984

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_794 : CutsKnown 794 :=
  main_cutsKnown (j := 794) oqBody_793
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_794

set_option maxRecDepth 100000 in
/-- `__loop398`. -/
theorem walk_990 : CutsKnown 990 :=
  loop1_cutsKnown (j := 990) oqLoopBody_793
    (by decide) (by decide) (by decide) (by decide) walkOk_990

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_814 : CutsKnown 814 :=
  main_cutsKnown (j := 814) oqBody_813
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_814

set_option maxRecDepth 100000 in
/-- `__loop402`. -/
theorem walk_996 : CutsKnown 996 :=
  loop1_cutsKnown (j := 996) oqLoopBody_813
    (by decide) (by decide) (by decide) (by decide) walkOk_996

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem walk_837 : CutsKnown 837 :=
  main_cutsKnown (j := 837) oqBody_836
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_837

set_option maxRecDepth 100000 in
/-- `__loop406`. -/
theorem walk_1002 : CutsKnown 1002 :=
  loop1_cutsKnown (j := 1002) oqLoopBody_836
    (by decide) (by decide) (by decide) (by decide) walkOk_1002

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem walk_854 : CutsKnown 854 :=
  main_cutsKnown (j := 854) oqBody_853
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_854

set_option maxRecDepth 100000 in
/-- `__loop410`. -/
theorem walk_1007 : CutsKnown 1007 :=
  loop0_cutsKnown (j := 1007) oqLoopBody_853
    (by decide) (by decide) (by decide) walkOk_1007

end
end LeanVM.Guest.End
