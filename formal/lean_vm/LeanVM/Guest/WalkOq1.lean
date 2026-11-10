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
/-- `opening_queries__L0_L1_L64_L32_L15_L3`. -/
theorem walk_1112 : CutsKnown 1112 :=
  main_cutsKnown (j := 1112) oqBody_1111
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1112

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem walk_1124 : CutsKnown 1124 :=
  main_cutsKnown (j := 1124) oqBody_1123
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1124

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem walk_1156 : CutsKnown 1156 :=
  main_cutsKnown (j := 1156) oqBody_1155
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1156

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem walk_1163 : CutsKnown 1163 :=
  main_cutsKnown (j := 1163) oqBody_1162
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1163

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem walk_1236 : CutsKnown 1236 :=
  main_cutsKnown (j := 1236) oqBody_1235
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1236

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem walk_1275 : CutsKnown 1275 :=
  main_cutsKnown (j := 1275) oqBody_1274
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1275

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem walk_1312 : CutsKnown 1312 :=
  main_cutsKnown (j := 1312) oqBody_1311
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1312

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem walk_1351 : CutsKnown 1351 :=
  main_cutsKnown (j := 1351) oqBody_1350
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1351

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem walk_1423 : CutsKnown 1423 :=
  main_cutsKnown (j := 1423) oqBody_1422
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1423

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem walk_1461 : CutsKnown 1461 :=
  main_cutsKnown (j := 1461) oqBody_1460
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1461

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem walk_1507 : CutsKnown 1507 :=
  main_cutsKnown (j := 1507) oqBody_1506
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1507

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem walk_1594 : CutsKnown 1594 :=
  main_cutsKnown (j := 1594) oqBody_1593
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1594

set_option maxRecDepth 100000 in
/-- `__loop621`. -/
theorem walk_1692 : CutsKnown 1692 :=
  loop1_cutsKnown (j := 1692) oqBody_1691
    (by decide) (by decide) (by decide) (by decide) walkOk_1692

set_option maxRecDepth 100000 in
/-- `__loop625`. -/
theorem walk_1699 : CutsKnown 1699 :=
  loop0_cutsKnown (j := 1699) oqBody_1698
    (by decide) (by decide) (by decide) walkOk_1699

set_option maxRecDepth 100000 in
/-- `__loop629`. -/
theorem walk_1709 : CutsKnown 1709 :=
  loop1_cutsKnown (j := 1709) oqBody_1708
    (by decide) (by decide) (by decide) (by decide) walkOk_1709

set_option maxRecDepth 100000 in
/-- `__loop633`. -/
theorem walk_1714 : CutsKnown 1714 :=
  loop0_cutsKnown (j := 1714) oqBody_1713
    (by decide) (by decide) (by decide) walkOk_1714

set_option maxRecDepth 100000 in
/-- `__loop637`. -/
theorem walk_1730 : CutsKnown 1730 :=
  loop1_cutsKnown (j := 1730) oqBody_1729
    (by decide) (by decide) (by decide) (by decide) walkOk_1730

set_option maxRecDepth 100000 in
/-- `__loop641`. -/
theorem walk_1740 : CutsKnown 1740 :=
  loop1_cutsKnown (j := 1740) oqBody_1739
    (by decide) (by decide) (by decide) (by decide) walkOk_1740

set_option maxRecDepth 100000 in
/-- `__loop645`. -/
theorem walk_1747 : CutsKnown 1747 :=
  loop0_cutsKnown (j := 1747) oqBody_1746
    (by decide) (by decide) (by decide) walkOk_1747

set_option maxRecDepth 100000 in
/-- `__loop649`. -/
theorem walk_1755 : CutsKnown 1755 :=
  loop0_cutsKnown (j := 1755) oqBody_1754
    (by decide) (by decide) (by decide) walkOk_1755

set_option maxRecDepth 100000 in
/-- `__loop653`. -/
theorem walk_1765 : CutsKnown 1765 :=
  loop1_cutsKnown (j := 1765) oqBody_1764
    (by decide) (by decide) (by decide) (by decide) walkOk_1765

set_option maxRecDepth 100000 in
/-- `__loop657`. -/
theorem walk_1772 : CutsKnown 1772 :=
  loop1_cutsKnown (j := 1772) oqBody_1771
    (by decide) (by decide) (by decide) (by decide) walkOk_1772

set_option maxRecDepth 100000 in
/-- `__loop661`. -/
theorem walk_1780 : CutsKnown 1780 :=
  loop0_cutsKnown (j := 1780) oqBody_1779
    (by decide) (by decide) (by decide) walkOk_1780

set_option maxRecDepth 100000 in
/-- `__loop665`. -/
theorem walk_1791 : CutsKnown 1791 :=
  loop1_cutsKnown (j := 1791) oqBody_1790
    (by decide) (by decide) (by decide) (by decide) walkOk_1791

end
end LeanVM.Guest.End
