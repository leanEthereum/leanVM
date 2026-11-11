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
theorem walk_1264 : CutsKnown 1264 :=
  main_cutsKnown (j := 1264) oqBody_1263
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1264

set_option maxRecDepth 100000 in
/-- `__loop623`. -/
theorem walk_1696 : CutsKnown 1696 :=
  loop0_cutsKnown (j := 1696) oqBody_1695
    (by decide) (by decide) (by decide) walkOk_1696

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem walk_1299 : CutsKnown 1299 :=
  main_cutsKnown (j := 1299) oqBody_1298
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1299

set_option maxRecDepth 100000 in
/-- `__loop624`. -/
theorem walk_1700 : CutsKnown 1700 :=
  loop1_cutsKnown (j := 1700) oqBody_1699
    (by decide) (by decide) (by decide) (by decide) walkOk_1700

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem walk_1300 : CutsKnown 1300 :=
  main_cutsKnown (j := 1300) oqBody_1299
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1300

set_option maxRecDepth 100000 in
/-- `__loop625`. -/
theorem walk_1702 : CutsKnown 1702 :=
  loop1_cutsKnown (j := 1702) oqBody_1701
    (by decide) (by decide) (by decide) (by decide) walkOk_1702

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem walk_1301 : CutsKnown 1301 :=
  main_cutsKnown (j := 1301) oqBody_1300
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1301

set_option maxRecDepth 100000 in
/-- `__loop626`. -/
theorem walk_1703 : CutsKnown 1703 :=
  loop1_cutsKnown (j := 1703) oqBody_1702
    (by decide) (by decide) (by decide) (by decide) walkOk_1703

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem walk_1304 : CutsKnown 1304 :=
  main_cutsKnown (j := 1304) oqBody_1303
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1304

set_option maxRecDepth 100000 in
/-- `__loop627`. -/
theorem walk_1704 : CutsKnown 1704 :=
  loop0_cutsKnown (j := 1704) oqBody_1703
    (by decide) (by decide) (by decide) walkOk_1704

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem walk_1338 : CutsKnown 1338 :=
  main_cutsKnown (j := 1338) oqBody_1337
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1338

set_option maxRecDepth 100000 in
/-- `__loop628`. -/
theorem walk_1708 : CutsKnown 1708 :=
  loop1_cutsKnown (j := 1708) oqBody_1707
    (by decide) (by decide) (by decide) (by decide) walkOk_1708

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem walk_1339 : CutsKnown 1339 :=
  main_cutsKnown (j := 1339) oqBody_1338
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1339

set_option maxRecDepth 100000 in
/-- `__loop629`. -/
theorem walk_1709 : CutsKnown 1709 :=
  loop1_cutsKnown (j := 1709) oqBody_1708
    (by decide) (by decide) (by decide) (by decide) walkOk_1709

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem walk_1342 : CutsKnown 1342 :=
  main_cutsKnown (j := 1342) oqBody_1341
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1342

set_option maxRecDepth 100000 in
/-- `__loop630`. -/
theorem walk_1710 : CutsKnown 1710 :=
  loop0_cutsKnown (j := 1710) oqBody_1709
    (by decide) (by decide) (by decide) walkOk_1710

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem walk_1376 : CutsKnown 1376 :=
  main_cutsKnown (j := 1376) oqBody_1375
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1376

set_option maxRecDepth 100000 in
/-- `__loop631`. -/
theorem walk_1714 : CutsKnown 1714 :=
  loop1_cutsKnown (j := 1714) oqBody_1713
    (by decide) (by decide) (by decide) (by decide) walkOk_1714

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem walk_1377 : CutsKnown 1377 :=
  main_cutsKnown (j := 1377) oqBody_1376
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1377

set_option maxRecDepth 100000 in
/-- `__loop632`. -/
theorem walk_1715 : CutsKnown 1715 :=
  loop1_cutsKnown (j := 1715) oqBody_1714
    (by decide) (by decide) (by decide) (by decide) walkOk_1715

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem walk_1381 : CutsKnown 1381 :=
  main_cutsKnown (j := 1381) oqBody_1380
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1381

set_option maxRecDepth 100000 in
/-- `__loop633`. -/
theorem walk_1716 : CutsKnown 1716 :=
  loop0_cutsKnown (j := 1716) oqBody_1715
    (by decide) (by decide) (by decide) walkOk_1716

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem walk_1413 : CutsKnown 1413 :=
  main_cutsKnown (j := 1413) oqBody_1412
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1413

set_option maxRecDepth 100000 in
/-- `__loop634`. -/
theorem walk_1720 : CutsKnown 1720 :=
  loop1_cutsKnown (j := 1720) oqBody_1719
    (by decide) (by decide) (by decide) (by decide) walkOk_1720

end
end LeanVM.Guest.End
