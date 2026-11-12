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
/-- `opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem walk_1014 : CutsKnown 1014 :=
  main_cutsKnown (j := 1014) oqBody_1013
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1014

set_option maxRecDepth 100000 in
/-- `__loop504`. -/
theorem walk_1513 : CutsKnown 1513 :=
  loop1_cutsKnown (j := 1513) oqLoopBody_1013
    (by decide) (by decide) (by decide) (by decide) walkOk_1513

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0`. -/
theorem walk_1025 : CutsKnown 1025 :=
  main_cutsKnown (j := 1025) oqBody_1024
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1025

set_option maxRecDepth 100000 in
/-- `__loop508`. -/
theorem walk_1518 : CutsKnown 1518 :=
  loop0_cutsKnown (j := 1518) oqLoopBody_1024
    (by decide) (by decide) (by decide) walkOk_1518

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1`. -/
theorem walk_1040 : CutsKnown 1040 :=
  main_cutsKnown (j := 1040) oqBody_1039
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1040

set_option maxRecDepth 100000 in
/-- `__loop512`. -/
theorem walk_1522 : CutsKnown 1522 :=
  loop0_cutsKnown (j := 1522) oqLoopBody_1039
    (by decide) (by decide) (by decide) walkOk_1522

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1072 : CutsKnown 1072 :=
  main_cutsKnown (j := 1072) oqBody_1071
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1072

set_option maxRecDepth 100000 in
/-- `__loop516`. -/
theorem walk_1527 : CutsKnown 1527 :=
  loop1_cutsKnown (j := 1527) oqLoopBody_1071
    (by decide) (by decide) (by decide) (by decide) walkOk_1527

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1`. -/
theorem walk_1082 : CutsKnown 1082 :=
  main_cutsKnown (j := 1082) oqBody_1081
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1082

set_option maxRecDepth 100000 in
/-- `__loop520`. -/
theorem walk_1531 : CutsKnown 1531 :=
  loop0_cutsKnown (j := 1531) oqLoopBody_1081
    (by decide) (by decide) (by decide) walkOk_1531

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1117 : CutsKnown 1117 :=
  main_cutsKnown (j := 1117) oqBody_1116
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1117

set_option maxRecDepth 100000 in
/-- `__loop524`. -/
theorem walk_1536 : CutsKnown 1536 :=
  loop0_cutsKnown (j := 1536) oqLoopBody_1116
    (by decide) (by decide) (by decide) walkOk_1536

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1`. -/
theorem walk_1123 : CutsKnown 1123 :=
  main_cutsKnown (j := 1123) oqBody_1122
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1123

set_option maxRecDepth 100000 in
/-- `__loop528`. -/
theorem walk_1540 : CutsKnown 1540 :=
  loop0_cutsKnown (j := 1540) oqLoopBody_1122
    (by decide) (by decide) (by decide) walkOk_1540

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1`. -/
theorem walk_1160 : CutsKnown 1160 :=
  main_cutsKnown (j := 1160) oqBody_1159
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1160

set_option maxRecDepth 100000 in
/-- `__loop532`. -/
theorem walk_1545 : CutsKnown 1545 :=
  loop0_cutsKnown (j := 1545) oqLoopBody_1159
    (by decide) (by decide) (by decide) walkOk_1545

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1191 : CutsKnown 1191 :=
  main_cutsKnown (j := 1191) oqBody_1190
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1191

set_option maxRecDepth 100000 in
/-- `__loop536`. -/
theorem walk_1549 : CutsKnown 1549 :=
  loop1_cutsKnown (j := 1549) oqLoopBody_1190
    (by decide) (by decide) (by decide) (by decide) walkOk_1549

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1`. -/
theorem walk_1201 : CutsKnown 1201 :=
  main_cutsKnown (j := 1201) oqBody_1200
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1201

set_option maxRecDepth 100000 in
/-- `__loop540`. -/
theorem walk_1554 : CutsKnown 1554 :=
  loop0_cutsKnown (j := 1554) oqLoopBody_1200
    (by decide) (by decide) (by decide) walkOk_1554

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem walk_1242 : CutsKnown 1242 :=
  main_cutsKnown (j := 1242) oqBody_1241
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1242

set_option maxRecDepth 100000 in
/-- `__loop544`. -/
theorem walk_1559 : CutsKnown 1559 :=
  loop0_cutsKnown (j := 1559) oqLoopBody_1241
    (by decide) (by decide) (by decide) walkOk_1559

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem walk_1281 : CutsKnown 1281 :=
  main_cutsKnown (j := 1281) oqBody_1280
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1281

set_option maxRecDepth 100000 in
/-- `__loop548`. -/
theorem walk_1563 : CutsKnown 1563 :=
  loop1_cutsKnown (j := 1563) oqLoopBody_1280
    (by decide) (by decide) (by decide) (by decide) walkOk_1563

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1`. -/
theorem walk_1291 : CutsKnown 1291 :=
  main_cutsKnown (j := 1291) oqBody_1290
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1291

set_option maxRecDepth 100000 in
/-- `__loop552`. -/
theorem walk_1568 : CutsKnown 1568 :=
  loop0_cutsKnown (j := 1568) oqLoopBody_1290
    (by decide) (by decide) (by decide) walkOk_1568

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem walk_1330 : CutsKnown 1330 :=
  main_cutsKnown (j := 1330) oqBody_1329
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1330

set_option maxRecDepth 100000 in
/-- `__loop556`. -/
theorem walk_1573 : CutsKnown 1573 :=
  loop0_cutsKnown (j := 1573) oqLoopBody_1329
    (by decide) (by decide) (by decide) walkOk_1573

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0`. -/
theorem walk_1368 : CutsKnown 1368 :=
  main_cutsKnown (j := 1368) oqBody_1367
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1368

set_option maxRecDepth 100000 in
/-- `__loop560`. -/
theorem walk_1577 : CutsKnown 1577 :=
  loop1_cutsKnown (j := 1577) oqLoopBody_1367
    (by decide) (by decide) (by decide) (by decide) walkOk_1577

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1`. -/
theorem walk_1379 : CutsKnown 1379 :=
  main_cutsKnown (j := 1379) oqBody_1378
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1379

set_option maxRecDepth 100000 in
/-- `__loop564`. -/
theorem walk_1582 : CutsKnown 1582 :=
  loop0_cutsKnown (j := 1582) oqLoopBody_1378
    (by decide) (by decide) (by decide) walkOk_1582

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0`. -/
theorem walk_1423 : CutsKnown 1423 :=
  main_cutsKnown (j := 1423) oqBody_1422
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1423

set_option maxRecDepth 100000 in
/-- `__loop568`. -/
theorem walk_1587 : CutsKnown 1587 :=
  loop0_cutsKnown (j := 1587) oqLoopBody_1422
    (by decide) (by decide) (by decide) walkOk_1587

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1465 : CutsKnown 1465 :=
  main_cutsKnown (j := 1465) oqBody_1464
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1465

set_option maxRecDepth 100000 in
/-- `__loop572`. -/
theorem walk_1591 : CutsKnown 1591 :=
  loop1_cutsKnown (j := 1591) oqLoopBody_1464
    (by decide) (by decide) (by decide) (by decide) walkOk_1591

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1`. -/
theorem walk_1476 : CutsKnown 1476 :=
  main_cutsKnown (j := 1476) oqBody_1475
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1476

set_option maxRecDepth 100000 in
/-- `__loop576`. -/
theorem walk_1596 : CutsKnown 1596 :=
  loop0_cutsKnown (j := 1596) oqLoopBody_1475
    (by decide) (by decide) (by decide) walkOk_1596

end
end LeanVM.Guest.End
