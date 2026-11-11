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
/-- `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem oqBody_1143 : Data.core1036.body = oqMainT ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop520" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop520`, the loop of `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem oqBody_1664 : Data.core1460.body = oqLoop1T ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop520" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1144 : Data.core1037.body = oqMainT ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop521" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop521`, the loop of `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1666 : Data.core1462.body = oqLoop1T ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop521" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1145 : Data.core1038.body = oqMainT ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop522" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop522`, the loop of `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1667 : Data.core1463.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop522" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1149 : Data.core1042.body = oqMainT ⟨0, 16, 12, 6⟩ 0 (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop523" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop523`, the loop of `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1668 : Data.core1464.body = oqLoop0T ⟨0, 16, 12, 6⟩ (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop523" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1182 : Data.core1075.body = oqMainT ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop524" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop524`, the loop of `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1675 : Data.core1471.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop524" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1183 : Data.core1076.body = oqMainT ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop525" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop525`, the loop of `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1676 : Data.core1472.body = oqLoop1T ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop525" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1187 : Data.core1080.body = oqMainT ⟨0, 16, 12, 7⟩ 0 (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop526" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop526`, the loop of `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1677 : Data.core1473.body = oqLoop0T ⟨0, 16, 12, 7⟩ (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop526" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1220 : Data.core1113.body = oqMainT ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop527" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop527`, the loop of `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1684 : Data.core1480.body = oqLoop1T ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop527" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1221 : Data.core1114.body = oqMainT ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop528" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop528`, the loop of `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1685 : Data.core1481.body = oqLoop1T ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop528" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1225 : Data.core1118.body = oqMainT ⟨0, 16, 18, 2⟩ 0 (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop529" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop529`, the loop of `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1686 : Data.core1482.body = oqLoop0T ⟨0, 16, 18, 2⟩ (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop529" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1258 : Data.core1151.body = oqMainT ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop530" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop530`, the loop of `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1693 : Data.core1489.body = oqLoop1T ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop530" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1259 : Data.core1152.body = oqMainT ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop531" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop531`, the loop of `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1694 : Data.core1490.body = oqLoop1T ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop531" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
