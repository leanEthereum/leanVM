/-
  LeanVM.Guest.B1.Opening.QueriesBody2

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
/-- `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem oqBody_1263 : Data.core1156.body = oqMainT ⟨0, 16, 18, 3⟩ 0 (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop532" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop532`, the loop of `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem oqBody_1695 : Data.core1491.body = oqLoop0T ⟨0, 16, 18, 3⟩ (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop532" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1298 : Data.core1191.body = oqMainT ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop533" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop533`, the loop of `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1699 : Data.core1495.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop533" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1299 : Data.core1192.body = oqMainT ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop534" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop534`, the loop of `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1701 : Data.core1497.body = oqLoop1T ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop534" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1300 : Data.core1193.body = oqMainT ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop535" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop535`, the loop of `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1702 : Data.core1498.body = oqLoop1T ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop535" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1303 : Data.core1196.body = oqMainT ⟨0, 16, 18, 4⟩ 0 (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop536" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop536`, the loop of `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1703 : Data.core1499.body = oqLoop0T ⟨0, 16, 18, 4⟩ (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop536" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1337 : Data.core1230.body = oqMainT ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop537" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop537`, the loop of `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1707 : Data.core1503.body = oqLoop1T ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop537" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1338 : Data.core1231.body = oqMainT ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop538" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop538`, the loop of `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1708 : Data.core1504.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop538" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1341 : Data.core1234.body = oqMainT ⟨0, 16, 18, 5⟩ 0 (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop539" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop539`, the loop of `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1709 : Data.core1505.body = oqLoop0T ⟨0, 16, 18, 5⟩ (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop539" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1375 : Data.core1268.body = oqMainT ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop540" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop540`, the loop of `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1713 : Data.core1509.body = oqLoop1T ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop540" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1376 : Data.core1269.body = oqMainT ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop541" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop541`, the loop of `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1714 : Data.core1510.body = oqLoop1T ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop541" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1380 : Data.core1273.body = oqMainT ⟨0, 16, 18, 6⟩ 0 (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop542" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop542`, the loop of `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1715 : Data.core1511.body = oqLoop0T ⟨0, 16, 18, 6⟩ (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop542" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1412 : Data.core1305.body = oqMainT ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop543" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop543`, the loop of `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1719 : Data.core1515.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop543" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
