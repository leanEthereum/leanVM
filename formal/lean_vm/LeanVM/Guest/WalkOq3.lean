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
/-- `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem walk_1116 : CutsKnown 1116 :=
  main_cutsKnown (j := 1116) oqBody_1115
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1116

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem walk_1126 : CutsKnown 1126 :=
  main_cutsKnown (j := 1126) oqBody_1125
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1126

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem walk_1158 : CutsKnown 1158 :=
  main_cutsKnown (j := 1158) oqBody_1157
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1158

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem walk_1200 : CutsKnown 1200 :=
  main_cutsKnown (j := 1200) oqBody_1199
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1200

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem walk_1241 : CutsKnown 1241 :=
  main_cutsKnown (j := 1241) oqBody_1240
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1241

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem walk_1307 : CutsKnown 1307 :=
  main_cutsKnown (j := 1307) oqBody_1306
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1307

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem walk_1347 : CutsKnown 1347 :=
  main_cutsKnown (j := 1347) oqBody_1346
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1347

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem walk_1386 : CutsKnown 1386 :=
  main_cutsKnown (j := 1386) oqBody_1385
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1386

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem walk_1428 : CutsKnown 1428 :=
  main_cutsKnown (j := 1428) oqBody_1427
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1428

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem walk_1502 : CutsKnown 1502 :=
  main_cutsKnown (j := 1502) oqBody_1501
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1502

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem walk_1550 : CutsKnown 1550 :=
  main_cutsKnown (j := 1550) oqBody_1549
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1550

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem walk_1640 : CutsKnown 1640 :=
  main_cutsKnown (j := 1640) oqBody_1639
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1640

set_option maxRecDepth 100000 in
/-- `__loop623`. -/
theorem walk_1695 : CutsKnown 1695 :=
  loop1_cutsKnown (j := 1695) oqBody_1694
    (by decide) (by decide) (by decide) (by decide) walkOk_1695

set_option maxRecDepth 100000 in
/-- `__loop627`. -/
theorem walk_1701 : CutsKnown 1701 :=
  loop0_cutsKnown (j := 1701) oqBody_1700
    (by decide) (by decide) (by decide) walkOk_1701

set_option maxRecDepth 100000 in
/-- `__loop631`. -/
theorem walk_1712 : CutsKnown 1712 :=
  loop1_cutsKnown (j := 1712) oqBody_1711
    (by decide) (by decide) (by decide) (by decide) walkOk_1712

set_option maxRecDepth 100000 in
/-- `__loop635`. -/
theorem walk_1722 : CutsKnown 1722 :=
  loop1_cutsKnown (j := 1722) oqBody_1721
    (by decide) (by decide) (by decide) (by decide) walkOk_1722

set_option maxRecDepth 100000 in
/-- `__loop639`. -/
theorem walk_1732 : CutsKnown 1732 :=
  loop0_cutsKnown (j := 1732) oqBody_1731
    (by decide) (by decide) (by decide) walkOk_1732

set_option maxRecDepth 100000 in
/-- `__loop643`. -/
theorem walk_1745 : CutsKnown 1745 :=
  loop1_cutsKnown (j := 1745) oqBody_1744
    (by decide) (by decide) (by decide) (by decide) walkOk_1745

set_option maxRecDepth 100000 in
/-- `__loop647`. -/
theorem walk_1753 : CutsKnown 1753 :=
  loop1_cutsKnown (j := 1753) oqBody_1752
    (by decide) (by decide) (by decide) (by decide) walkOk_1753

set_option maxRecDepth 100000 in
/-- `__loop651`. -/
theorem walk_1760 : CutsKnown 1760 :=
  loop1_cutsKnown (j := 1760) oqBody_1759
    (by decide) (by decide) (by decide) (by decide) walkOk_1760

set_option maxRecDepth 100000 in
/-- `__loop655`. -/
theorem walk_1767 : CutsKnown 1767 :=
  loop0_cutsKnown (j := 1767) oqBody_1766
    (by decide) (by decide) (by decide) walkOk_1767

set_option maxRecDepth 100000 in
/-- `__loop659`. -/
theorem walk_1777 : CutsKnown 1777 :=
  loop1_cutsKnown (j := 1777) oqBody_1776
    (by decide) (by decide) (by decide) (by decide) walkOk_1777

set_option maxRecDepth 100000 in
/-- `__loop663`. -/
theorem walk_1785 : CutsKnown 1785 :=
  loop0_cutsKnown (j := 1785) oqBody_1784
    (by decide) (by decide) (by decide) walkOk_1785

set_option maxRecDepth 100000 in
/-- `__loop667`. -/
theorem walk_1796 : CutsKnown 1796 :=
  loop1_cutsKnown (j := 1796) oqBody_1795
    (by decide) (by decide) (by decide) (by decide) walkOk_1796

end
end LeanVM.Guest.End
