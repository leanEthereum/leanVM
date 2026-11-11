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
theorem walk_1307 : CutsKnown 1307 :=
  main_cutsKnown (j := 1307) oqBody_1413
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1307

set_option maxRecDepth 100000 in
/-- `__loop544`. -/
theorem walk_1517 : CutsKnown 1517 :=
  loop1_cutsKnown (j := 1517) oqBody_1720
    (by decide) (by decide) (by decide) (by decide) walkOk_1517

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem walk_1311 : CutsKnown 1311 :=
  main_cutsKnown (j := 1311) oqBody_1417
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1311

set_option maxRecDepth 100000 in
/-- `__loop545`. -/
theorem walk_1518 : CutsKnown 1518 :=
  loop0_cutsKnown (j := 1518) oqBody_1721
    (by decide) (by decide) (by decide) walkOk_1518

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem walk_1348 : CutsKnown 1348 :=
  main_cutsKnown (j := 1348) oqBody_1454
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1348

set_option maxRecDepth 100000 in
/-- `__loop546`. -/
theorem walk_1522 : CutsKnown 1522 :=
  loop1_cutsKnown (j := 1522) oqBody_1725
    (by decide) (by decide) (by decide) (by decide) walkOk_1522

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem walk_1349 : CutsKnown 1349 :=
  main_cutsKnown (j := 1349) oqBody_1455
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1349

set_option maxRecDepth 100000 in
/-- `__loop547`. -/
theorem walk_1524 : CutsKnown 1524 :=
  loop1_cutsKnown (j := 1524) oqBody_1727
    (by decide) (by decide) (by decide) (by decide) walkOk_1524

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem walk_1353 : CutsKnown 1353 :=
  main_cutsKnown (j := 1353) oqBody_1459
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1353

set_option maxRecDepth 100000 in
/-- `__loop548`. -/
theorem walk_1525 : CutsKnown 1525 :=
  loop0_cutsKnown (j := 1525) oqBody_1728
    (by decide) (by decide) (by decide) walkOk_1525

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem walk_1392 : CutsKnown 1392 :=
  main_cutsKnown (j := 1392) oqBody_1498
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1392

set_option maxRecDepth 100000 in
/-- `__loop549`. -/
theorem walk_1529 : CutsKnown 1529 :=
  loop1_cutsKnown (j := 1529) oqBody_1732
    (by decide) (by decide) (by decide) (by decide) walkOk_1529

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem walk_1396 : CutsKnown 1396 :=
  main_cutsKnown (j := 1396) oqBody_1502
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) walkOk_1396

set_option maxRecDepth 100000 in
/-- `__loop550`. -/
theorem walk_1530 : CutsKnown 1530 :=
  loop0_cutsKnown (j := 1530) oqBody_1733
    (by decide) (by decide) (by decide) walkOk_1530

end
end LeanVM.Guest.End
