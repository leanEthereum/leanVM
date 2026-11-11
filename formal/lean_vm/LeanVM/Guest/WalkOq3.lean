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
/-- `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem walk_1414 : CutsKnown 1414 :=
  main_cutsKnown (j := 1414) oqBody_1413
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1414

set_option maxRecDepth 100000 in
/-- `__loop635`. -/
theorem walk_1721 : CutsKnown 1721 :=
  loop1_cutsKnown (j := 1721) oqBody_1720
    (by decide) (by decide) (by decide) (by decide) walkOk_1721

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem walk_1418 : CutsKnown 1418 :=
  main_cutsKnown (j := 1418) oqBody_1417
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1418

set_option maxRecDepth 100000 in
/-- `__loop636`. -/
theorem walk_1722 : CutsKnown 1722 :=
  loop0_cutsKnown (j := 1722) oqBody_1721
    (by decide) (by decide) (by decide) walkOk_1722

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem walk_1455 : CutsKnown 1455 :=
  main_cutsKnown (j := 1455) oqBody_1454
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1455

set_option maxRecDepth 100000 in
/-- `__loop637`. -/
theorem walk_1726 : CutsKnown 1726 :=
  loop1_cutsKnown (j := 1726) oqBody_1725
    (by decide) (by decide) (by decide) (by decide) walkOk_1726

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem walk_1456 : CutsKnown 1456 :=
  main_cutsKnown (j := 1456) oqBody_1455
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1456

set_option maxRecDepth 100000 in
/-- `__loop638`. -/
theorem walk_1728 : CutsKnown 1728 :=
  loop1_cutsKnown (j := 1728) oqBody_1727
    (by decide) (by decide) (by decide) (by decide) walkOk_1728

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem walk_1460 : CutsKnown 1460 :=
  main_cutsKnown (j := 1460) oqBody_1459
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1460

set_option maxRecDepth 100000 in
/-- `__loop639`. -/
theorem walk_1729 : CutsKnown 1729 :=
  loop0_cutsKnown (j := 1729) oqBody_1728
    (by decide) (by decide) (by decide) walkOk_1729

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem walk_1499 : CutsKnown 1499 :=
  main_cutsKnown (j := 1499) oqBody_1498
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1499

set_option maxRecDepth 100000 in
/-- `__loop640`. -/
theorem walk_1733 : CutsKnown 1733 :=
  loop1_cutsKnown (j := 1733) oqBody_1732
    (by decide) (by decide) (by decide) (by decide) walkOk_1733

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem walk_1503 : CutsKnown 1503 :=
  main_cutsKnown (j := 1503) oqBody_1502
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1503

set_option maxRecDepth 100000 in
/-- `__loop641`. -/
theorem walk_1734 : CutsKnown 1734 :=
  loop0_cutsKnown (j := 1734) oqBody_1733
    (by decide) (by decide) (by decide) walkOk_1734

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem walk_1546 : CutsKnown 1546 :=
  main_cutsKnown (j := 1546) oqBody_1545
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1546

set_option maxRecDepth 100000 in
/-- `__loop642`. -/
theorem walk_1738 : CutsKnown 1738 :=
  loop1_cutsKnown (j := 1738) oqBody_1737
    (by decide) (by decide) (by decide) (by decide) walkOk_1738

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem walk_1547 : CutsKnown 1547 :=
  main_cutsKnown (j := 1547) oqBody_1546
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1547

set_option maxRecDepth 100000 in
/-- `__loop643`. -/
theorem walk_1740 : CutsKnown 1740 :=
  loop1_cutsKnown (j := 1740) oqBody_1739
    (by decide) (by decide) (by decide) (by decide) walkOk_1740

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem walk_1551 : CutsKnown 1551 :=
  main_cutsKnown (j := 1551) oqBody_1550
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1551

set_option maxRecDepth 100000 in
/-- `__loop644`. -/
theorem walk_1741 : CutsKnown 1741 :=
  loop0_cutsKnown (j := 1741) oqBody_1740
    (by decide) (by decide) (by decide) walkOk_1741

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem walk_1593 : CutsKnown 1593 :=
  main_cutsKnown (j := 1593) oqBody_1592
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1593

set_option maxRecDepth 100000 in
/-- `__loop645`. -/
theorem walk_1745 : CutsKnown 1745 :=
  loop1_cutsKnown (j := 1745) oqBody_1744
    (by decide) (by decide) (by decide) (by decide) walkOk_1745

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem walk_1597 : CutsKnown 1597 :=
  main_cutsKnown (j := 1597) oqBody_1596
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1597

set_option maxRecDepth 100000 in
/-- `__loop646`. -/
theorem walk_1746 : CutsKnown 1746 :=
  loop0_cutsKnown (j := 1746) oqBody_1745
    (by decide) (by decide) (by decide) walkOk_1746

end
end LeanVM.Guest.End
