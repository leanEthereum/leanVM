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
/-- `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem walk_1157 : CutsKnown 1157 :=
  main_cutsKnown (j := 1157) oqBody_1263
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1157

set_option maxRecDepth 100000 in
/-- `__loop532`. -/
theorem walk_1492 : CutsKnown 1492 :=
  loop0_cutsKnown (j := 1492) oqBody_1695
    (by decide) (by decide) (by decide) walkOk_1492

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem walk_1192 : CutsKnown 1192 :=
  main_cutsKnown (j := 1192) oqBody_1298
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1192

set_option maxRecDepth 100000 in
/-- `__loop533`. -/
theorem walk_1496 : CutsKnown 1496 :=
  loop1_cutsKnown (j := 1496) oqBody_1699
    (by decide) (by decide) (by decide) (by decide) walkOk_1496

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem walk_1193 : CutsKnown 1193 :=
  main_cutsKnown (j := 1193) oqBody_1299
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1193

set_option maxRecDepth 100000 in
/-- `__loop534`. -/
theorem walk_1498 : CutsKnown 1498 :=
  loop1_cutsKnown (j := 1498) oqBody_1701
    (by decide) (by decide) (by decide) (by decide) walkOk_1498

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem walk_1194 : CutsKnown 1194 :=
  main_cutsKnown (j := 1194) oqBody_1300
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1194

set_option maxRecDepth 100000 in
/-- `__loop535`. -/
theorem walk_1499 : CutsKnown 1499 :=
  loop1_cutsKnown (j := 1499) oqBody_1702
    (by decide) (by decide) (by decide) (by decide) walkOk_1499

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem walk_1197 : CutsKnown 1197 :=
  main_cutsKnown (j := 1197) oqBody_1303
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1197

set_option maxRecDepth 100000 in
/-- `__loop536`. -/
theorem walk_1500 : CutsKnown 1500 :=
  loop0_cutsKnown (j := 1500) oqBody_1703
    (by decide) (by decide) (by decide) walkOk_1500

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem walk_1231 : CutsKnown 1231 :=
  main_cutsKnown (j := 1231) oqBody_1337
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1231

set_option maxRecDepth 100000 in
/-- `__loop537`. -/
theorem walk_1504 : CutsKnown 1504 :=
  loop1_cutsKnown (j := 1504) oqBody_1707
    (by decide) (by decide) (by decide) (by decide) walkOk_1504

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem walk_1232 : CutsKnown 1232 :=
  main_cutsKnown (j := 1232) oqBody_1338
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1232

set_option maxRecDepth 100000 in
/-- `__loop538`. -/
theorem walk_1505 : CutsKnown 1505 :=
  loop1_cutsKnown (j := 1505) oqBody_1708
    (by decide) (by decide) (by decide) (by decide) walkOk_1505

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem walk_1235 : CutsKnown 1235 :=
  main_cutsKnown (j := 1235) oqBody_1341
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1235

set_option maxRecDepth 100000 in
/-- `__loop539`. -/
theorem walk_1506 : CutsKnown 1506 :=
  loop0_cutsKnown (j := 1506) oqBody_1709
    (by decide) (by decide) (by decide) walkOk_1506

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem walk_1269 : CutsKnown 1269 :=
  main_cutsKnown (j := 1269) oqBody_1375
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1269

set_option maxRecDepth 100000 in
/-- `__loop540`. -/
theorem walk_1510 : CutsKnown 1510 :=
  loop1_cutsKnown (j := 1510) oqBody_1713
    (by decide) (by decide) (by decide) (by decide) walkOk_1510

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem walk_1270 : CutsKnown 1270 :=
  main_cutsKnown (j := 1270) oqBody_1376
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1270

set_option maxRecDepth 100000 in
/-- `__loop541`. -/
theorem walk_1511 : CutsKnown 1511 :=
  loop1_cutsKnown (j := 1511) oqBody_1714
    (by decide) (by decide) (by decide) (by decide) walkOk_1511

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem walk_1274 : CutsKnown 1274 :=
  main_cutsKnown (j := 1274) oqBody_1380
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1274

set_option maxRecDepth 100000 in
/-- `__loop542`. -/
theorem walk_1512 : CutsKnown 1512 :=
  loop0_cutsKnown (j := 1512) oqBody_1715
    (by decide) (by decide) (by decide) walkOk_1512

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem walk_1306 : CutsKnown 1306 :=
  main_cutsKnown (j := 1306) oqBody_1412
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1306

set_option maxRecDepth 100000 in
/-- `__loop543`. -/
theorem walk_1516 : CutsKnown 1516 :=
  loop1_cutsKnown (j := 1516) oqBody_1719
    (by decide) (by decide) (by decide) (by decide) walkOk_1516

end
end LeanVM.Guest.End
