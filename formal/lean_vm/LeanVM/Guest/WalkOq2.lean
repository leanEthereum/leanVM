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
theorem walk_496 : CutsKnown 496 :=
  main_cutsKnown (j := 496) oqBody_495
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_496

set_option maxRecDepth 100000 in
/-- `__loop342`. -/
theorem walk_942 : CutsKnown 942 :=
  loop0_cutsKnown (j := 942) oqLoopBody_495
    (by decide) (by decide) (by decide) walkOk_942

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0`. -/
theorem walk_519 : CutsKnown 519 :=
  main_cutsKnown (j := 519) oqBody_518
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_519

set_option maxRecDepth 100000 in
/-- `__loop346`. -/
theorem walk_947 : CutsKnown 947 :=
  loop0_cutsKnown (j := 947) oqLoopBody_518
    (by decide) (by decide) (by decide) walkOk_947

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem walk_541 : CutsKnown 541 :=
  main_cutsKnown (j := 541) oqBody_540
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_541

set_option maxRecDepth 100000 in
/-- `__loop350`. -/
theorem walk_952 : CutsKnown 952 :=
  loop0_cutsKnown (j := 952) oqLoopBody_540
    (by decide) (by decide) (by decide) walkOk_952

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0`. -/
theorem walk_567 : CutsKnown 567 :=
  main_cutsKnown (j := 567) oqBody_566
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_567

set_option maxRecDepth 100000 in
/-- `__loop354`. -/
theorem walk_957 : CutsKnown 957 :=
  loop0_cutsKnown (j := 957) oqLoopBody_566
    (by decide) (by decide) (by decide) walkOk_957

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0`. -/
theorem walk_589 : CutsKnown 589 :=
  main_cutsKnown (j := 589) oqBody_588
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_589

set_option maxRecDepth 100000 in
/-- `__loop358`. -/
theorem walk_962 : CutsKnown 962 :=
  loop0_cutsKnown (j := 962) oqLoopBody_588
    (by decide) (by decide) (by decide) walkOk_962

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0`. -/
theorem walk_607 : CutsKnown 607 :=
  main_cutsKnown (j := 607) oqBody_606
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_607

set_option maxRecDepth 100000 in
/-- `__loop362`. -/
theorem walk_967 : CutsKnown 967 :=
  loop0_cutsKnown (j := 967) oqLoopBody_606
    (by decide) (by decide) (by decide) walkOk_967

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0`. -/
theorem walk_624 : CutsKnown 624 :=
  main_cutsKnown (j := 624) oqBody_623
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_624

set_option maxRecDepth 100000 in
/-- `__loop366`. -/
theorem walk_972 : CutsKnown 972 :=
  loop0_cutsKnown (j := 972) oqLoopBody_623
    (by decide) (by decide) (by decide) walkOk_972

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_649 : CutsKnown 649 :=
  main_cutsKnown (j := 649) oqBody_648
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_649

set_option maxRecDepth 100000 in
/-- `__loop370`. -/
theorem walk_978 : CutsKnown 978 :=
  loop1_cutsKnown (j := 978) oqLoopBody_648
    (by decide) (by decide) (by decide) (by decide) walkOk_978

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0`. -/
theorem walk_671 : CutsKnown 671 :=
  main_cutsKnown (j := 671) oqBody_670
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_671

set_option maxRecDepth 100000 in
/-- `__loop374`. -/
theorem walk_984 : CutsKnown 984 :=
  loop1_cutsKnown (j := 984) oqLoopBody_670
    (by decide) (by decide) (by decide) (by decide) walkOk_984

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0`. -/
theorem walk_695 : CutsKnown 695 :=
  main_cutsKnown (j := 695) oqBody_694
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_695

set_option maxRecDepth 100000 in
/-- `__loop378`. -/
theorem walk_990 : CutsKnown 990 :=
  loop1_cutsKnown (j := 990) oqLoopBody_694
    (by decide) (by decide) (by decide) (by decide) walkOk_990

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0`. -/
theorem walk_713 : CutsKnown 713 :=
  main_cutsKnown (j := 713) oqBody_712
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_713

set_option maxRecDepth 100000 in
/-- `__loop382`. -/
theorem walk_995 : CutsKnown 995 :=
  loop0_cutsKnown (j := 995) oqLoopBody_712
    (by decide) (by decide) (by decide) walkOk_995

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem walk_738 : CutsKnown 738 :=
  main_cutsKnown (j := 738) oqBody_737
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_738

set_option maxRecDepth 100000 in
/-- `__loop386`. -/
theorem walk_999 : CutsKnown 999 :=
  loop0_cutsKnown (j := 999) oqLoopBody_737
    (by decide) (by decide) (by decide) walkOk_999

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem walk_777 : CutsKnown 777 :=
  main_cutsKnown (j := 777) oqBody_776
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_777

set_option maxRecDepth 100000 in
/-- `__loop390`. -/
theorem walk_1003 : CutsKnown 1003 :=
  loop0_cutsKnown (j := 1003) oqLoopBody_776
    (by decide) (by decide) (by decide) walkOk_1003

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem walk_794 : CutsKnown 794 :=
  main_cutsKnown (j := 794) oqBody_793
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_794

set_option maxRecDepth 100000 in
/-- `__loop394`. -/
theorem walk_1008 : CutsKnown 1008 :=
  loop0_cutsKnown (j := 1008) oqLoopBody_793
    (by decide) (by decide) (by decide) walkOk_1008

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem walk_812 : CutsKnown 812 :=
  main_cutsKnown (j := 812) oqBody_811
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_812

set_option maxRecDepth 100000 in
/-- `__loop398`. -/
theorem walk_1014 : CutsKnown 1014 :=
  loop1_cutsKnown (j := 1014) oqLoopBody_811
    (by decide) (by decide) (by decide) (by decide) walkOk_1014

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem walk_832 : CutsKnown 832 :=
  main_cutsKnown (j := 832) oqBody_831
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_832

set_option maxRecDepth 100000 in
/-- `__loop402`. -/
theorem walk_1020 : CutsKnown 1020 :=
  loop1_cutsKnown (j := 1020) oqLoopBody_831
    (by decide) (by decide) (by decide) (by decide) walkOk_1020

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem walk_855 : CutsKnown 855 :=
  main_cutsKnown (j := 855) oqBody_854
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_855

set_option maxRecDepth 100000 in
/-- `__loop406`. -/
theorem walk_1026 : CutsKnown 1026 :=
  loop1_cutsKnown (j := 1026) oqLoopBody_854
    (by decide) (by decide) (by decide) (by decide) walkOk_1026

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem walk_872 : CutsKnown 872 :=
  main_cutsKnown (j := 872) oqBody_871
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_872

set_option maxRecDepth 100000 in
/-- `__loop410`. -/
theorem walk_1031 : CutsKnown 1031 :=
  loop0_cutsKnown (j := 1031) oqLoopBody_871
    (by decide) (by decide) (by decide) walkOk_1031

end
end LeanVM.Guest.End
