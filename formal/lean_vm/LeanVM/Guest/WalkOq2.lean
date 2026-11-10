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
/-- `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem walk_1114 : CutsKnown 1114 :=
  main_cutsKnown (j := 1114) oqBody_1113
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1114

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem walk_1125 : CutsKnown 1125 :=
  main_cutsKnown (j := 1125) oqBody_1124
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1125

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem walk_1157 : CutsKnown 1157 :=
  main_cutsKnown (j := 1157) oqBody_1156
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1157

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem walk_1199 : CutsKnown 1199 :=
  main_cutsKnown (j := 1199) oqBody_1198
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1199

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem walk_1237 : CutsKnown 1237 :=
  main_cutsKnown (j := 1237) oqBody_1236
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1237

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem walk_1278 : CutsKnown 1278 :=
  main_cutsKnown (j := 1278) oqBody_1277
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1278

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem walk_1346 : CutsKnown 1346 :=
  main_cutsKnown (j := 1346) oqBody_1345
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1346

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem walk_1385 : CutsKnown 1385 :=
  main_cutsKnown (j := 1385) oqBody_1384
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1385

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem walk_1424 : CutsKnown 1424 :=
  main_cutsKnown (j := 1424) oqBody_1423
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1424

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem walk_1465 : CutsKnown 1465 :=
  main_cutsKnown (j := 1465) oqBody_1464
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1465

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem walk_1546 : CutsKnown 1546 :=
  main_cutsKnown (j := 1546) oqBody_1545
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1546

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem walk_1598 : CutsKnown 1598 :=
  main_cutsKnown (j := 1598) oqBody_1597
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1598

set_option maxRecDepth 100000 in
/-- `__loop622`. -/
theorem walk_1694 : CutsKnown 1694 :=
  loop1_cutsKnown (j := 1694) oqBody_1693
    (by decide) (by decide) (by decide) (by decide) walkOk_1694

set_option maxRecDepth 100000 in
/-- `__loop626`. -/
theorem walk_1700 : CutsKnown 1700 :=
  loop0_cutsKnown (j := 1700) oqBody_1699
    (by decide) (by decide) (by decide) walkOk_1700

set_option maxRecDepth 100000 in
/-- `__loop630`. -/
theorem walk_1710 : CutsKnown 1710 :=
  loop1_cutsKnown (j := 1710) oqBody_1709
    (by decide) (by decide) (by decide) (by decide) walkOk_1710

set_option maxRecDepth 100000 in
/-- `__loop634`. -/
theorem walk_1721 : CutsKnown 1721 :=
  loop1_cutsKnown (j := 1721) oqBody_1720
    (by decide) (by decide) (by decide) (by decide) walkOk_1721

set_option maxRecDepth 100000 in
/-- `__loop638`. -/
theorem walk_1731 : CutsKnown 1731 :=
  loop1_cutsKnown (j := 1731) oqBody_1730
    (by decide) (by decide) (by decide) (by decide) walkOk_1731

set_option maxRecDepth 100000 in
/-- `__loop642`. -/
theorem walk_1741 : CutsKnown 1741 :=
  loop0_cutsKnown (j := 1741) oqBody_1740
    (by decide) (by decide) (by decide) walkOk_1741

set_option maxRecDepth 100000 in
/-- `__loop646`. -/
theorem walk_1751 : CutsKnown 1751 :=
  loop1_cutsKnown (j := 1751) oqBody_1750
    (by decide) (by decide) (by decide) (by decide) walkOk_1751

set_option maxRecDepth 100000 in
/-- `__loop650`. -/
theorem walk_1759 : CutsKnown 1759 :=
  loop1_cutsKnown (j := 1759) oqBody_1758
    (by decide) (by decide) (by decide) (by decide) walkOk_1759

set_option maxRecDepth 100000 in
/-- `__loop654`. -/
theorem walk_1766 : CutsKnown 1766 :=
  loop1_cutsKnown (j := 1766) oqBody_1765
    (by decide) (by decide) (by decide) (by decide) walkOk_1766

set_option maxRecDepth 100000 in
/-- `__loop658`. -/
theorem walk_1773 : CutsKnown 1773 :=
  loop0_cutsKnown (j := 1773) oqBody_1772
    (by decide) (by decide) (by decide) walkOk_1773

set_option maxRecDepth 100000 in
/-- `__loop662`. -/
theorem walk_1784 : CutsKnown 1784 :=
  loop1_cutsKnown (j := 1784) oqBody_1783
    (by decide) (by decide) (by decide) (by decide) walkOk_1784

set_option maxRecDepth 100000 in
/-- `__loop666`. -/
theorem walk_1792 : CutsKnown 1792 :=
  loop0_cutsKnown (j := 1792) oqBody_1791
    (by decide) (by decide) (by decide) walkOk_1792

end
end LeanVM.Guest.End
