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
theorem oqBody_1263 : Data.core1263.body = oqMainT ⟨0, 16, 18, 3⟩ 0 (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop623" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop623`, the loop of `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem oqBody_1695 : Data.core1695.body = oqLoop0T ⟨0, 16, 18, 3⟩ (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop623" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1298 : Data.core1298.body = oqMainT ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop624" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop624`, the loop of `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1699 : Data.core1699.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop624" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1299 : Data.core1299.body = oqMainT ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop625" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop625`, the loop of `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1701 : Data.core1701.body = oqLoop1T ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop625" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1300 : Data.core1300.body = oqMainT ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop626" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop626`, the loop of `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1702 : Data.core1702.body = oqLoop1T ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop626" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1303 : Data.core1303.body = oqMainT ⟨0, 16, 18, 4⟩ 0 (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop627" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop627`, the loop of `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1703 : Data.core1703.body = oqLoop0T ⟨0, 16, 18, 4⟩ (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop627" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1337 : Data.core1337.body = oqMainT ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop628" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop628`, the loop of `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1707 : Data.core1707.body = oqLoop1T ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop628" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1338 : Data.core1338.body = oqMainT ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop629" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop629`, the loop of `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1708 : Data.core1708.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop629" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1341 : Data.core1341.body = oqMainT ⟨0, 16, 18, 5⟩ 0 (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop630" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop630`, the loop of `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1709 : Data.core1709.body = oqLoop0T ⟨0, 16, 18, 5⟩ (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop630" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1375 : Data.core1375.body = oqMainT ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop631" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop631`, the loop of `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1713 : Data.core1713.body = oqLoop1T ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop631" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1376 : Data.core1376.body = oqMainT ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop632" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop632`, the loop of `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1714 : Data.core1714.body = oqLoop1T ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop632" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1380 : Data.core1380.body = oqMainT ⟨0, 16, 18, 6⟩ 0 (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop633" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop633`, the loop of `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1715 : Data.core1715.body = oqLoop0T ⟨0, 16, 18, 6⟩ (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop633" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1412 : Data.core1412.body = oqMainT ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop634" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop634`, the loop of `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1719 : Data.core1719.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop634" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
