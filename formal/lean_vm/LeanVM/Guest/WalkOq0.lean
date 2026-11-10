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
/-- `opening_queries__L1_L1_L64_L32_L14_L8`. -/
theorem walk_1110 : CutsKnown 1110 :=
  main_cutsKnown (j := 1110) oqBody_1109
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1110

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem walk_1122 : CutsKnown 1122 :=
  main_cutsKnown (j := 1122) oqBody_1121
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1122

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem walk_1132 : CutsKnown 1132 :=
  main_cutsKnown (j := 1132) oqBody_1131
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1132

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem walk_1159 : CutsKnown 1159 :=
  main_cutsKnown (j := 1159) oqBody_1158
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1159

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem walk_1204 : CutsKnown 1204 :=
  main_cutsKnown (j := 1204) oqBody_1203
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1204

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem walk_1274 : CutsKnown 1274 :=
  main_cutsKnown (j := 1274) oqBody_1273
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1274

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem walk_1308 : CutsKnown 1308 :=
  main_cutsKnown (j := 1308) oqBody_1307
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1308

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem walk_1348 : CutsKnown 1348 :=
  main_cutsKnown (j := 1348) oqBody_1347
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1348

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem walk_1389 : CutsKnown 1389 :=
  main_cutsKnown (j := 1389) oqBody_1388
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1389

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem walk_1460 : CutsKnown 1460 :=
  main_cutsKnown (j := 1460) oqBody_1459
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1460

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem walk_1503 : CutsKnown 1503 :=
  main_cutsKnown (j := 1503) oqBody_1502
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1503

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem walk_1593 : CutsKnown 1593 :=
  main_cutsKnown (j := 1593) oqBody_1592
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1593

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem walk_1644 : CutsKnown 1644 :=
  main_cutsKnown (j := 1644) oqBody_1643
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1644

set_option maxRecDepth 100000 in
/-- `__loop620`. -/
theorem walk_1691 : CutsKnown 1691 :=
  loop1_cutsKnown (j := 1691) oqBody_1690
    (by decide) (by decide) (by decide) (by decide) walkOk_1691

set_option maxRecDepth 100000 in
/-- `__loop624`. -/
theorem walk_1698 : CutsKnown 1698 :=
  loop0_cutsKnown (j := 1698) oqBody_1697
    (by decide) (by decide) (by decide) walkOk_1698

set_option maxRecDepth 100000 in
/-- `__loop628`. -/
theorem walk_1703 : CutsKnown 1703 :=
  loop0_cutsKnown (j := 1703) oqBody_1702
    (by decide) (by decide) (by decide) walkOk_1703

set_option maxRecDepth 100000 in
/-- `__loop632`. -/
theorem walk_1713 : CutsKnown 1713 :=
  loop1_cutsKnown (j := 1713) oqBody_1712
    (by decide) (by decide) (by decide) (by decide) walkOk_1713

set_option maxRecDepth 100000 in
/-- `__loop636`. -/
theorem walk_1723 : CutsKnown 1723 :=
  loop0_cutsKnown (j := 1723) oqBody_1722
    (by decide) (by decide) (by decide) walkOk_1723

set_option maxRecDepth 100000 in
/-- `__loop640`. -/
theorem walk_1739 : CutsKnown 1739 :=
  loop1_cutsKnown (j := 1739) oqBody_1738
    (by decide) (by decide) (by decide) (by decide) walkOk_1739

set_option maxRecDepth 100000 in
/-- `__loop644`. -/
theorem walk_1746 : CutsKnown 1746 :=
  loop1_cutsKnown (j := 1746) oqBody_1745
    (by decide) (by decide) (by decide) (by decide) walkOk_1746

set_option maxRecDepth 100000 in
/-- `__loop648`. -/
theorem walk_1754 : CutsKnown 1754 :=
  loop1_cutsKnown (j := 1754) oqBody_1753
    (by decide) (by decide) (by decide) (by decide) walkOk_1754

set_option maxRecDepth 100000 in
/-- `__loop652`. -/
theorem walk_1761 : CutsKnown 1761 :=
  loop0_cutsKnown (j := 1761) oqBody_1760
    (by decide) (by decide) (by decide) walkOk_1761

set_option maxRecDepth 100000 in
/-- `__loop656`. -/
theorem walk_1771 : CutsKnown 1771 :=
  loop1_cutsKnown (j := 1771) oqBody_1770
    (by decide) (by decide) (by decide) (by decide) walkOk_1771

set_option maxRecDepth 100000 in
/-- `__loop660`. -/
theorem walk_1779 : CutsKnown 1779 :=
  loop1_cutsKnown (j := 1779) oqBody_1778
    (by decide) (by decide) (by decide) (by decide) walkOk_1779

set_option maxRecDepth 100000 in
/-- `__loop664`. -/
theorem walk_1789 : CutsKnown 1789 :=
  loop1_cutsKnown (j := 1789) oqBody_1788
    (by decide) (by decide) (by decide) (by decide) walkOk_1789

set_option maxRecDepth 100000 in
/-- `__loop668`. -/
theorem walk_1797 : CutsKnown 1797 :=
  loop0_cutsKnown (j := 1797) oqBody_1796
    (by decide) (by decide) (by decide) walkOk_1797

end
end LeanVM.Guest.End
