/-
  LeanVM.Guest.B1.Opening.QueriesBody0

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
/-- `opening_queries__L1_L1_L64_L32_L14_L8`. -/
theorem oqBody_1109 : Data.core1109.body = oqMainT ⟨1, 64, 6, 8⟩ 1 (oqWalkOf ⟨1, 64, 6, 8⟩) "__loop620" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop620`, the loop of `opening_queries__L1_L1_L64_L32_L14_L8`. -/
theorem oqBody_1690 : Data.core1690.body = oqLoop1T ⟨1, 64, 6, 8⟩ 1 (oqWalkOf ⟨1, 64, 6, 8⟩) "__loop620" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1121 : Data.core1121.body = oqMainT ⟨0, 16, 6, 7⟩ 0 (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop624" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop624`, the loop of `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1697 : Data.core1697.body = oqLoop0T ⟨0, 16, 6, 7⟩ (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop624" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1131 : Data.core1131.body = oqMainT ⟨0, 16, 6, 6⟩ 0 (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop628" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop628`, the loop of `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1702 : Data.core1702.body = oqLoop0T ⟨0, 16, 6, 6⟩ (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop628" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1158 : Data.core1158.body = oqMainT ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop632" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop632`, the loop of `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1712 : Data.core1712.body = oqLoop1T ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop632" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1203 : Data.core1203.body = oqMainT ⟨0, 16, 12, 6⟩ 0 (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop636" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop636`, the loop of `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1722 : Data.core1722.body = oqLoop0T ⟨0, 16, 12, 6⟩ (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop636" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1273 : Data.core1273.body = oqMainT ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop640" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop640`, the loop of `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1738 : Data.core1738.body = oqLoop1T ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop640" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1307 : Data.core1307.body = oqMainT ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop644" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop644`, the loop of `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1745 : Data.core1745.body = oqLoop1T ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop644" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1347 : Data.core1347.body = oqMainT ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop648" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop648`, the loop of `opening_queries__L0_L1_L64_L32_L23_L5`. -/
theorem oqBody_1753 : Data.core1753.body = oqLoop1T ⟨1, 64, 18, 5⟩ 0 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop648" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1388 : Data.core1388.body = oqMainT ⟨0, 16, 18, 5⟩ 0 (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop652" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop652`, the loop of `opening_queries__L0_L0_L16_L24_L23_L5`. -/
theorem oqBody_1760 : Data.core1760.body = oqLoop0T ⟨0, 16, 18, 5⟩ (oqWalkOf ⟨0, 16, 18, 5⟩) "__loop652" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1459 : Data.core1459.body = oqMainT ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop656" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop656`, the loop of `opening_queries__L1_L1_L64_L32_L25_L7`. -/
theorem oqBody_1770 : Data.core1770.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop656" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1502 : Data.core1502.body = oqMainT ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop660" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop660`, the loop of `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1778 : Data.core1778.body = oqLoop1T ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop660" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem oqBody_1592 : Data.core1592.body = oqMainT ⟨1, 64, 18, 8⟩ 0 (oqWalkOf ⟨1, 64, 18, 8⟩) "__loop664" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop664`, the loop of `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem oqBody_1788 : Data.core1788.body = oqLoop1T ⟨1, 64, 18, 8⟩ 0 (oqWalkOf ⟨1, 64, 18, 8⟩) "__loop664" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem oqBody_1643 : Data.core1643.body = oqMainT ⟨0, 16, 24, 5⟩ 0 (oqWalkOf ⟨0, 16, 24, 5⟩) "__loop668" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop668`, the loop of `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem oqBody_1796 : Data.core1796.body = oqLoop0T ⟨0, 16, 24, 5⟩ (oqWalkOf ⟨0, 16, 24, 5⟩) "__loop668" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
