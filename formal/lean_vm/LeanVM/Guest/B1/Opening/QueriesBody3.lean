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
/-- `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem oqBody_1115 : Data.core1115.body = oqMainT ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop623" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop623`, the loop of `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem oqBody_1694 : Data.core1694.body = oqLoop1T ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop623" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1125 : Data.core1125.body = oqMainT ⟨0, 16, 12, 4⟩ 0 (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop627" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop627`, the loop of `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1700 : Data.core1700.body = oqLoop0T ⟨0, 16, 12, 4⟩ (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop627" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1157 : Data.core1157.body = oqMainT ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop631" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop631`, the loop of `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1711 : Data.core1711.body = oqLoop1T ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop631" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1199 : Data.core1199.body = oqMainT ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop635" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop635`, the loop of `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1721 : Data.core1721.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop635" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1240 : Data.core1240.body = oqMainT ⟨0, 16, 12, 7⟩ 0 (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop639" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop639`, the loop of `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1731 : Data.core1731.body = oqLoop0T ⟨0, 16, 12, 7⟩ (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop639" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1306 : Data.core1306.body = oqMainT ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop643`, the loop of `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1744 : Data.core1744.body = oqLoop1T ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1346 : Data.core1346.body = oqMainT ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop647" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop647`, the loop of `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem oqBody_1752 : Data.core1752.body = oqLoop1T ⟨1, 64, 18, 4⟩ 1 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop647" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1385 : Data.core1385.body = oqMainT ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop651" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop651`, the loop of `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem oqBody_1759 : Data.core1759.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop651" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1427 : Data.core1427.body = oqMainT ⟨0, 16, 18, 6⟩ 0 (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop655" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop655`, the loop of `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem oqBody_1766 : Data.core1766.body = oqLoop0T ⟨0, 16, 18, 6⟩ (oqWalkOf ⟨0, 16, 18, 6⟩) "__loop655" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1501 : Data.core1501.body = oqMainT ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop659" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop659`, the loop of `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1776 : Data.core1776.body = oqLoop1T ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop659" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1549 : Data.core1549.body = oqMainT ⟨0, 16, 24, 3⟩ 0 (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop663" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop663`, the loop of `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1784 : Data.core1784.body = oqLoop0T ⟨0, 16, 24, 3⟩ (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop663" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem oqBody_1639 : Data.core1639.body = oqMainT ⟨1, 64, 24, 6⟩ 1 (oqWalkOf ⟨1, 64, 24, 6⟩) "__loop667" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop667`, the loop of `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem oqBody_1795 : Data.core1795.body = oqLoop1T ⟨1, 64, 24, 6⟩ 1 (oqWalkOf ⟨1, 64, 24, 6⟩) "__loop667" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
