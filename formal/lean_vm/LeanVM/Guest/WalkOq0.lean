/-
  LeanVM.Guest.WalkOq0

  The cut obligations (`CutsKnown`) of a quarter of `opening_queries`' specializations and loops,
  from their templates (`B1/Opening/QueriesBody0.lean`), the generic forms (`WalkKnown.lean`) and
  their certificates' checks (`WalkOqOk0.lean`).
-/

module

public import LeanVM.Guest.WalkKnown
public import LeanVM.Guest.WalkOqOk0
public import LeanVM.Guest.B1.Opening.QueriesBody0

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem walk_1085 : CutsKnown 1085 :=
  main_cutsKnown (j := 1085) oqBody_1084
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1085

set_option maxRecDepth 100000 in
/-- `__loop600`. -/
theorem walk_1644 : CutsKnown 1644 :=
  loop1_cutsKnown (j := 1644) oqBody_1643
    (by decide) (by decide) (by decide) (by decide) walkOk_1644

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem walk_1087 : CutsKnown 1087 :=
  main_cutsKnown (j := 1087) oqBody_1086
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1087

set_option maxRecDepth 100000 in
/-- `__loop601`. -/
theorem walk_1645 : CutsKnown 1645 :=
  loop1_cutsKnown (j := 1645) oqBody_1644
    (by decide) (by decide) (by decide) (by decide) walkOk_1645

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem walk_1089 : CutsKnown 1089 :=
  main_cutsKnown (j := 1089) oqBody_1088
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1089

set_option maxRecDepth 100000 in
/-- `__loop602`. -/
theorem walk_1647 : CutsKnown 1647 :=
  loop1_cutsKnown (j := 1647) oqBody_1646
    (by decide) (by decide) (by decide) (by decide) walkOk_1647

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem walk_1091 : CutsKnown 1091 :=
  main_cutsKnown (j := 1091) oqBody_1090
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1091

set_option maxRecDepth 100000 in
/-- `__loop603`. -/
theorem walk_1648 : CutsKnown 1648 :=
  loop1_cutsKnown (j := 1648) oqBody_1647
    (by decide) (by decide) (by decide) (by decide) walkOk_1648

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem walk_1097 : CutsKnown 1097 :=
  main_cutsKnown (j := 1097) oqBody_1096
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1097

set_option maxRecDepth 100000 in
/-- `__loop604`. -/
theorem walk_1650 : CutsKnown 1650 :=
  loop0_cutsKnown (j := 1650) oqBody_1649
    (by decide) (by decide) (by decide) walkOk_1650

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem walk_1098 : CutsKnown 1098 :=
  main_cutsKnown (j := 1098) oqBody_1097
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1098

set_option maxRecDepth 100000 in
/-- `__loop605`. -/
theorem walk_1651 : CutsKnown 1651 :=
  loop0_cutsKnown (j := 1651) oqBody_1650
    (by decide) (by decide) (by decide) walkOk_1651

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem walk_1099 : CutsKnown 1099 :=
  main_cutsKnown (j := 1099) oqBody_1098
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1099

set_option maxRecDepth 100000 in
/-- `__loop606`. -/
theorem walk_1652 : CutsKnown 1652 :=
  loop0_cutsKnown (j := 1652) oqBody_1651
    (by decide) (by decide) (by decide) walkOk_1652

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem walk_1100 : CutsKnown 1100 :=
  main_cutsKnown (j := 1100) oqBody_1099
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1100

set_option maxRecDepth 100000 in
/-- `__loop607`. -/
theorem walk_1653 : CutsKnown 1653 :=
  loop0_cutsKnown (j := 1653) oqBody_1652
    (by decide) (by decide) (by decide) walkOk_1653

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem walk_1106 : CutsKnown 1106 :=
  main_cutsKnown (j := 1106) oqBody_1105
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1106

set_option maxRecDepth 100000 in
/-- `__loop608`. -/
theorem walk_1655 : CutsKnown 1655 :=
  loop0_cutsKnown (j := 1655) oqBody_1654
    (by decide) (by decide) (by decide) walkOk_1655

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem walk_1111 : CutsKnown 1111 :=
  main_cutsKnown (j := 1111) oqBody_1110
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1111

set_option maxRecDepth 100000 in
/-- `__loop609`. -/
theorem walk_1657 : CutsKnown 1657 :=
  loop0_cutsKnown (j := 1657) oqBody_1656
    (by decide) (by decide) (by decide) walkOk_1657

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem walk_1143 : CutsKnown 1143 :=
  main_cutsKnown (j := 1143) oqBody_1142
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1143

set_option maxRecDepth 100000 in
/-- `__loop610`. -/
theorem walk_1664 : CutsKnown 1664 :=
  loop1_cutsKnown (j := 1664) oqBody_1663
    (by decide) (by decide) (by decide) (by decide) walkOk_1664

end
end LeanVM.Guest.End
