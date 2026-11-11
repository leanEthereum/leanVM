/-
  LeanVM.Guest.B1.Opening.QueriesBody3

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem oqBody_1413 : Data.core1306.body = oqMainT ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop544" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop544`, the loop of `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem oqBody_1720 : Data.core1516.body = oqLoop1T ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop544" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1417 : Data.core1310.body = oqMainT ⟨0, 16, 18, 7⟩ 0 (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop545" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop545`, the loop of `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1721 : Data.core1517.body = oqLoop0T ⟨0, 16, 18, 7⟩ (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop545" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1454 : Data.core1347.body = oqMainT ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop546" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop546`, the loop of `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1725 : Data.core1521.body = oqLoop1T ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop546" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1455 : Data.core1348.body = oqMainT ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop547" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop547`, the loop of `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1727 : Data.core1523.body = oqLoop1T ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop547" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1459 : Data.core1352.body = oqMainT ⟨0, 16, 24, 2⟩ 0 (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop548" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop548`, the loop of `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1728 : Data.core1524.body = oqLoop0T ⟨0, 16, 24, 2⟩ (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop548" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1498 : Data.core1391.body = oqMainT ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop549" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop549`, the loop of `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1732 : Data.core1528.body = oqLoop1T ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop549" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1502 : Data.core1395.body = oqMainT ⟨0, 16, 24, 3⟩ 0 (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop550" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop550`, the loop of `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1733 : Data.core1529.body = oqLoop0T ⟨0, 16, 24, 3⟩ (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop550" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
