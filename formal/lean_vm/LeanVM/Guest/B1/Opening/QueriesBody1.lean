/-
  LeanVM.Guest.B1.Opening.QueriesBody1

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
/-- `opening_queries__L0_L1_L64_L32_L15_L3`. -/
theorem oqBody_1111 : Data.core1111.body = oqMainT ⟨1, 64, 12, 3⟩ 0 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop621" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop621`, the loop of `opening_queries__L0_L1_L64_L32_L15_L3`. -/
theorem oqBody_1691 : Data.core1691.body = oqLoop1T ⟨1, 64, 12, 3⟩ 0 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop621" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1123 : Data.core1123.body = oqMainT ⟨0, 16, 12, 2⟩ 0 (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop625" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop625`, the loop of `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1698 : Data.core1698.body = oqLoop0T ⟨0, 16, 12, 2⟩ (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop625" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem oqBody_1155 : Data.core1155.body = oqMainT ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop629" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop629`, the loop of `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem oqBody_1708 : Data.core1708.body = oqLoop1T ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop629" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1162 : Data.core1162.body = oqMainT ⟨0, 16, 12, 5⟩ 0 (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop633" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop633`, the loop of `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1713 : Data.core1713.body = oqLoop0T ⟨0, 16, 12, 5⟩ (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop633" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1235 : Data.core1235.body = oqMainT ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop637" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop637`, the loop of `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1729 : Data.core1729.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop637" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1274 : Data.core1274.body = oqMainT ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop641" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop641`, the loop of `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1739 : Data.core1739.body = oqLoop1T ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop641" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem oqBody_1311 : Data.core1311.body = oqMainT ⟨0, 16, 18, 3⟩ 0 (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop645" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop645`, the loop of `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem oqBody_1746 : Data.core1746.body = oqLoop0T ⟨0, 16, 18, 3⟩ (oqWalkOf ⟨0, 16, 18, 3⟩) "__loop645" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1350 : Data.core1350.body = oqMainT ⟨0, 16, 18, 4⟩ 0 (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop649" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop649`, the loop of `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem oqBody_1754 : Data.core1754.body = oqLoop0T ⟨0, 16, 18, 4⟩ (oqWalkOf ⟨0, 16, 18, 4⟩) "__loop649" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1422 : Data.core1422.body = oqMainT ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop653" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop653`, the loop of `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem oqBody_1764 : Data.core1764.body = oqLoop1T ⟨1, 64, 18, 6⟩ 1 (oqWalkOf ⟨1, 64, 18, 6⟩) "__loop653" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem oqBody_1460 : Data.core1460.body = oqMainT ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop657" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop657`, the loop of `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem oqBody_1771 : Data.core1771.body = oqLoop1T ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop657" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1506 : Data.core1506.body = oqMainT ⟨0, 16, 24, 2⟩ 0 (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop661" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop661`, the loop of `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1779 : Data.core1779.body = oqLoop0T ⟨0, 16, 24, 2⟩ (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop661" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem oqBody_1593 : Data.core1593.body = oqMainT ⟨1, 64, 24, 5⟩ 1 (oqWalkOf ⟨1, 64, 24, 5⟩) "__loop665" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop665`, the loop of `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem oqBody_1790 : Data.core1790.body = oqLoop1T ⟨1, 64, 24, 5⟩ 1 (oqWalkOf ⟨1, 64, 24, 5⟩) "__loop665" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
