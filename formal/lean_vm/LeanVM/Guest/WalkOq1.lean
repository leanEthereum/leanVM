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
theorem walk_1144 : CutsKnown 1144 :=
  main_cutsKnown (j := 1144) oqBody_1143
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1144

set_option maxRecDepth 100000 in
/-- `__loop611`. -/
theorem walk_1665 : CutsKnown 1665 :=
  loop1_cutsKnown (j := 1665) oqBody_1664
    (by decide) (by decide) (by decide) (by decide) walkOk_1665

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem walk_1145 : CutsKnown 1145 :=
  main_cutsKnown (j := 1145) oqBody_1144
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1145

set_option maxRecDepth 100000 in
/-- `__loop612`. -/
theorem walk_1667 : CutsKnown 1667 :=
  loop1_cutsKnown (j := 1667) oqBody_1666
    (by decide) (by decide) (by decide) (by decide) walkOk_1667

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem walk_1146 : CutsKnown 1146 :=
  main_cutsKnown (j := 1146) oqBody_1145
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1146

set_option maxRecDepth 100000 in
/-- `__loop613`. -/
theorem walk_1668 : CutsKnown 1668 :=
  loop1_cutsKnown (j := 1668) oqBody_1667
    (by decide) (by decide) (by decide) (by decide) walkOk_1668

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem walk_1150 : CutsKnown 1150 :=
  main_cutsKnown (j := 1150) oqBody_1149
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1150

set_option maxRecDepth 100000 in
/-- `__loop614`. -/
theorem walk_1669 : CutsKnown 1669 :=
  loop0_cutsKnown (j := 1669) oqBody_1668
    (by decide) (by decide) (by decide) walkOk_1669

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem walk_1183 : CutsKnown 1183 :=
  main_cutsKnown (j := 1183) oqBody_1182
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1183

set_option maxRecDepth 100000 in
/-- `__loop615`. -/
theorem walk_1676 : CutsKnown 1676 :=
  loop1_cutsKnown (j := 1676) oqBody_1675
    (by decide) (by decide) (by decide) (by decide) walkOk_1676

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem walk_1184 : CutsKnown 1184 :=
  main_cutsKnown (j := 1184) oqBody_1183
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1184

set_option maxRecDepth 100000 in
/-- `__loop616`. -/
theorem walk_1677 : CutsKnown 1677 :=
  loop1_cutsKnown (j := 1677) oqBody_1676
    (by decide) (by decide) (by decide) (by decide) walkOk_1677

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem walk_1188 : CutsKnown 1188 :=
  main_cutsKnown (j := 1188) oqBody_1187
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1188

set_option maxRecDepth 100000 in
/-- `__loop617`. -/
theorem walk_1678 : CutsKnown 1678 :=
  loop0_cutsKnown (j := 1678) oqBody_1677
    (by decide) (by decide) (by decide) walkOk_1678

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem walk_1221 : CutsKnown 1221 :=
  main_cutsKnown (j := 1221) oqBody_1220
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1221

set_option maxRecDepth 100000 in
/-- `__loop618`. -/
theorem walk_1685 : CutsKnown 1685 :=
  loop1_cutsKnown (j := 1685) oqBody_1684
    (by decide) (by decide) (by decide) (by decide) walkOk_1685

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem walk_1222 : CutsKnown 1222 :=
  main_cutsKnown (j := 1222) oqBody_1221
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1222

set_option maxRecDepth 100000 in
/-- `__loop619`. -/
theorem walk_1686 : CutsKnown 1686 :=
  loop1_cutsKnown (j := 1686) oqBody_1685
    (by decide) (by decide) (by decide) (by decide) walkOk_1686

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem walk_1226 : CutsKnown 1226 :=
  main_cutsKnown (j := 1226) oqBody_1225
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1226

set_option maxRecDepth 100000 in
/-- `__loop620`. -/
theorem walk_1687 : CutsKnown 1687 :=
  loop0_cutsKnown (j := 1687) oqBody_1686
    (by decide) (by decide) (by decide) walkOk_1687

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem walk_1259 : CutsKnown 1259 :=
  main_cutsKnown (j := 1259) oqBody_1258
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1259

set_option maxRecDepth 100000 in
/-- `__loop621`. -/
theorem walk_1694 : CutsKnown 1694 :=
  loop1_cutsKnown (j := 1694) oqBody_1693
    (by decide) (by decide) (by decide) (by decide) walkOk_1694

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem walk_1260 : CutsKnown 1260 :=
  main_cutsKnown (j := 1260) oqBody_1259
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1260

set_option maxRecDepth 100000 in
/-- `__loop622`. -/
theorem walk_1695 : CutsKnown 1695 :=
  loop1_cutsKnown (j := 1695) oqBody_1694
    (by decide) (by decide) (by decide) (by decide) walkOk_1695

end
end LeanVM.Guest.End
