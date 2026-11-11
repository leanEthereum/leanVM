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
/-- `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem walk_1037 : CutsKnown 1037 :=
  main_cutsKnown (j := 1037) oqBody_1143
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1037

set_option maxRecDepth 100000 in
/-- `__loop520`. -/
theorem walk_1461 : CutsKnown 1461 :=
  loop1_cutsKnown (j := 1461) oqBody_1664
    (by decide) (by decide) (by decide) (by decide) walkOk_1461

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem walk_1038 : CutsKnown 1038 :=
  main_cutsKnown (j := 1038) oqBody_1144
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1038

set_option maxRecDepth 100000 in
/-- `__loop521`. -/
theorem walk_1463 : CutsKnown 1463 :=
  loop1_cutsKnown (j := 1463) oqBody_1666
    (by decide) (by decide) (by decide) (by decide) walkOk_1463

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem walk_1039 : CutsKnown 1039 :=
  main_cutsKnown (j := 1039) oqBody_1145
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1039

set_option maxRecDepth 100000 in
/-- `__loop522`. -/
theorem walk_1464 : CutsKnown 1464 :=
  loop1_cutsKnown (j := 1464) oqBody_1667
    (by decide) (by decide) (by decide) (by decide) walkOk_1464

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem walk_1043 : CutsKnown 1043 :=
  main_cutsKnown (j := 1043) oqBody_1149
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1043

set_option maxRecDepth 100000 in
/-- `__loop523`. -/
theorem walk_1465 : CutsKnown 1465 :=
  loop0_cutsKnown (j := 1465) oqBody_1668
    (by decide) (by decide) (by decide) walkOk_1465

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem walk_1076 : CutsKnown 1076 :=
  main_cutsKnown (j := 1076) oqBody_1182
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1076

set_option maxRecDepth 100000 in
/-- `__loop524`. -/
theorem walk_1472 : CutsKnown 1472 :=
  loop1_cutsKnown (j := 1472) oqBody_1675
    (by decide) (by decide) (by decide) (by decide) walkOk_1472

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem walk_1077 : CutsKnown 1077 :=
  main_cutsKnown (j := 1077) oqBody_1183
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1077

set_option maxRecDepth 100000 in
/-- `__loop525`. -/
theorem walk_1473 : CutsKnown 1473 :=
  loop1_cutsKnown (j := 1473) oqBody_1676
    (by decide) (by decide) (by decide) (by decide) walkOk_1473

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem walk_1081 : CutsKnown 1081 :=
  main_cutsKnown (j := 1081) oqBody_1187
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1081

set_option maxRecDepth 100000 in
/-- `__loop526`. -/
theorem walk_1474 : CutsKnown 1474 :=
  loop0_cutsKnown (j := 1474) oqBody_1677
    (by decide) (by decide) (by decide) walkOk_1474

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem walk_1114 : CutsKnown 1114 :=
  main_cutsKnown (j := 1114) oqBody_1220
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1114

set_option maxRecDepth 100000 in
/-- `__loop527`. -/
theorem walk_1481 : CutsKnown 1481 :=
  loop1_cutsKnown (j := 1481) oqBody_1684
    (by decide) (by decide) (by decide) (by decide) walkOk_1481

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem walk_1115 : CutsKnown 1115 :=
  main_cutsKnown (j := 1115) oqBody_1221
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1115

set_option maxRecDepth 100000 in
/-- `__loop528`. -/
theorem walk_1482 : CutsKnown 1482 :=
  loop1_cutsKnown (j := 1482) oqBody_1685
    (by decide) (by decide) (by decide) (by decide) walkOk_1482

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem walk_1119 : CutsKnown 1119 :=
  main_cutsKnown (j := 1119) oqBody_1225
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1119

set_option maxRecDepth 100000 in
/-- `__loop529`. -/
theorem walk_1483 : CutsKnown 1483 :=
  loop0_cutsKnown (j := 1483) oqBody_1686
    (by decide) (by decide) (by decide) walkOk_1483

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem walk_1152 : CutsKnown 1152 :=
  main_cutsKnown (j := 1152) oqBody_1258
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1152

set_option maxRecDepth 100000 in
/-- `__loop530`. -/
theorem walk_1490 : CutsKnown 1490 :=
  loop1_cutsKnown (j := 1490) oqBody_1693
    (by decide) (by decide) (by decide) (by decide) walkOk_1490

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem walk_1153 : CutsKnown 1153 :=
  main_cutsKnown (j := 1153) oqBody_1259
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1153

set_option maxRecDepth 100000 in
/-- `__loop531`. -/
theorem walk_1491 : CutsKnown 1491 :=
  loop1_cutsKnown (j := 1491) oqBody_1694
    (by decide) (by decide) (by decide) (by decide) walkOk_1491

end
end LeanVM.Guest.End
