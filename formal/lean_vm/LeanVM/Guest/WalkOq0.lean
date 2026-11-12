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
/-- `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0`. -/
theorem walk_1010 : CutsKnown 1010 :=
  main_cutsKnown (j := 1010) oqBody_1009
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1010

set_option maxRecDepth 100000 in
/-- `__loop502`. -/
theorem walk_1509 : CutsKnown 1509 :=
  loop1_cutsKnown (j := 1509) oqLoopBody_1009
    (by decide) (by decide) (by decide) (by decide) walkOk_1509

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0`. -/
theorem walk_1023 : CutsKnown 1023 :=
  main_cutsKnown (j := 1023) oqBody_1022
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1023

set_option maxRecDepth 100000 in
/-- `__loop506`. -/
theorem walk_1516 : CutsKnown 1516 :=
  loop0_cutsKnown (j := 1516) oqLoopBody_1022
    (by decide) (by decide) (by decide) walkOk_1516

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1033 : CutsKnown 1033 :=
  main_cutsKnown (j := 1033) oqBody_1032
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1033

set_option maxRecDepth 100000 in
/-- `__loop510`. -/
theorem walk_1520 : CutsKnown 1520 :=
  loop0_cutsKnown (j := 1520) oqLoopBody_1032
    (by decide) (by decide) (by decide) walkOk_1520

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1`. -/
theorem walk_1042 : CutsKnown 1042 :=
  main_cutsKnown (j := 1042) oqBody_1041
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1042

set_option maxRecDepth 100000 in
/-- `__loop514`. -/
theorem walk_1524 : CutsKnown 1524 :=
  loop0_cutsKnown (j := 1524) oqLoopBody_1041
    (by decide) (by decide) (by decide) walkOk_1524

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1`. -/
theorem walk_1080 : CutsKnown 1080 :=
  main_cutsKnown (j := 1080) oqBody_1079
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1080

set_option maxRecDepth 100000 in
/-- `__loop518`. -/
theorem walk_1529 : CutsKnown 1529 :=
  loop0_cutsKnown (j := 1529) oqLoopBody_1079
    (by decide) (by decide) (by decide) walkOk_1529

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem walk_1111 : CutsKnown 1111 :=
  main_cutsKnown (j := 1111) oqBody_1110
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1111

set_option maxRecDepth 100000 in
/-- `__loop522`. -/
theorem walk_1533 : CutsKnown 1533 :=
  loop1_cutsKnown (j := 1533) oqLoopBody_1110
    (by decide) (by decide) (by decide) (by decide) walkOk_1533

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1`. -/
theorem walk_1121 : CutsKnown 1121 :=
  main_cutsKnown (j := 1121) oqBody_1120
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1121

set_option maxRecDepth 100000 in
/-- `__loop526`. -/
theorem walk_1538 : CutsKnown 1538 :=
  loop0_cutsKnown (j := 1538) oqLoopBody_1120
    (by decide) (by decide) (by decide) walkOk_1538

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem walk_1152 : CutsKnown 1152 :=
  main_cutsKnown (j := 1152) oqBody_1151
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1152

set_option maxRecDepth 100000 in
/-- `__loop530`. -/
theorem walk_1543 : CutsKnown 1543 :=
  loop1_cutsKnown (j := 1543) oqLoopBody_1151
    (by decide) (by decide) (by decide) (by decide) walkOk_1543

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1`. -/
theorem walk_1162 : CutsKnown 1162 :=
  main_cutsKnown (j := 1162) oqBody_1161
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1162

set_option maxRecDepth 100000 in
/-- `__loop534`. -/
theorem walk_1547 : CutsKnown 1547 :=
  loop0_cutsKnown (j := 1547) oqLoopBody_1161
    (by decide) (by decide) (by decide) walkOk_1547

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0`. -/
theorem walk_1196 : CutsKnown 1196 :=
  main_cutsKnown (j := 1196) oqBody_1195
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1196

set_option maxRecDepth 100000 in
/-- `__loop538`. -/
theorem walk_1552 : CutsKnown 1552 :=
  loop0_cutsKnown (j := 1552) oqLoopBody_1195
    (by decide) (by decide) (by decide) walkOk_1552

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0`. -/
theorem walk_1237 : CutsKnown 1237 :=
  main_cutsKnown (j := 1237) oqBody_1236
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1237

set_option maxRecDepth 100000 in
/-- `__loop542`. -/
theorem walk_1556 : CutsKnown 1556 :=
  loop1_cutsKnown (j := 1556) oqLoopBody_1236
    (by decide) (by decide) (by decide) (by decide) walkOk_1556

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1`. -/
theorem walk_1247 : CutsKnown 1247 :=
  main_cutsKnown (j := 1247) oqBody_1246
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1247

set_option maxRecDepth 100000 in
/-- `__loop546`. -/
theorem walk_1561 : CutsKnown 1561 :=
  loop0_cutsKnown (j := 1561) oqLoopBody_1246
    (by decide) (by decide) (by decide) walkOk_1561

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem walk_1286 : CutsKnown 1286 :=
  main_cutsKnown (j := 1286) oqBody_1285
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1286

set_option maxRecDepth 100000 in
/-- `__loop550`. -/
theorem walk_1566 : CutsKnown 1566 :=
  loop0_cutsKnown (j := 1566) oqLoopBody_1285
    (by decide) (by decide) (by decide) walkOk_1566

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem walk_1325 : CutsKnown 1325 :=
  main_cutsKnown (j := 1325) oqBody_1324
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1325

set_option maxRecDepth 100000 in
/-- `__loop554`. -/
theorem walk_1570 : CutsKnown 1570 :=
  loop1_cutsKnown (j := 1570) oqLoopBody_1324
    (by decide) (by decide) (by decide) (by decide) walkOk_1570

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1`. -/
theorem walk_1334 : CutsKnown 1334 :=
  main_cutsKnown (j := 1334) oqBody_1333
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1334

set_option maxRecDepth 100000 in
/-- `__loop558`. -/
theorem walk_1575 : CutsKnown 1575 :=
  loop0_cutsKnown (j := 1575) oqLoopBody_1333
    (by decide) (by decide) (by decide) walkOk_1575

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0`. -/
theorem walk_1373 : CutsKnown 1373 :=
  main_cutsKnown (j := 1373) oqBody_1372
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1373

set_option maxRecDepth 100000 in
/-- `__loop562`. -/
theorem walk_1580 : CutsKnown 1580 :=
  loop0_cutsKnown (j := 1580) oqLoopBody_1372
    (by decide) (by decide) (by decide) walkOk_1580

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem walk_1418 : CutsKnown 1418 :=
  main_cutsKnown (j := 1418) oqBody_1417
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1418

set_option maxRecDepth 100000 in
/-- `__loop566`. -/
theorem walk_1584 : CutsKnown 1584 :=
  loop1_cutsKnown (j := 1584) oqLoopBody_1417
    (by decide) (by decide) (by decide) (by decide) walkOk_1584

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1`. -/
theorem walk_1428 : CutsKnown 1428 :=
  main_cutsKnown (j := 1428) oqBody_1427
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1428

set_option maxRecDepth 100000 in
/-- `__loop570`. -/
theorem walk_1589 : CutsKnown 1589 :=
  loop0_cutsKnown (j := 1589) oqLoopBody_1427
    (by decide) (by decide) (by decide) walkOk_1589

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0`. -/
theorem walk_1470 : CutsKnown 1470 :=
  main_cutsKnown (j := 1470) oqBody_1469
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1470

set_option maxRecDepth 100000 in
/-- `__loop574`. -/
theorem walk_1594 : CutsKnown 1594 :=
  loop0_cutsKnown (j := 1594) oqLoopBody_1469
    (by decide) (by decide) (by decide) walkOk_1594

end
end LeanVM.Guest.End
