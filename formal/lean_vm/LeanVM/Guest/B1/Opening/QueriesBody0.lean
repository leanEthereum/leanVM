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
/-- `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem oqBody_1084 : Data.core977.body = oqMainT ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop509" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop509`, the loop of `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem oqBody_1643 : Data.core1439.body = oqLoop1T ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop509" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1086 : Data.core979.body = oqMainT ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop510" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop510`, the loop of `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1644 : Data.core1440.body = oqLoop1T ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop510" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1088 : Data.core981.body = oqMainT ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop511" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop511`, the loop of `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1646 : Data.core1442.body = oqLoop1T ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop511" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1090 : Data.core983.body = oqMainT ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop512" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop512`, the loop of `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1647 : Data.core1443.body = oqLoop1T ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop512" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1096 : Data.core989.body = oqMainT ⟨0, 16, 12, 2⟩ 0 (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop513" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop513`, the loop of `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1649 : Data.core1445.body = oqLoop0T ⟨0, 16, 12, 2⟩ (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop513" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1097 : Data.core990.body = oqMainT ⟨0, 16, 12, 3⟩ 0 (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop514" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop514`, the loop of `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1650 : Data.core1446.body = oqLoop0T ⟨0, 16, 12, 3⟩ (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop514" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1098 : Data.core991.body = oqMainT ⟨0, 16, 12, 4⟩ 0 (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop515" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop515`, the loop of `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1651 : Data.core1447.body = oqLoop0T ⟨0, 16, 12, 4⟩ (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop515" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1099 : Data.core992.body = oqMainT ⟨0, 16, 12, 5⟩ 0 (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop516" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop516`, the loop of `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1652 : Data.core1448.body = oqLoop0T ⟨0, 16, 12, 5⟩ (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop516" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1105 : Data.core998.body = oqMainT ⟨0, 16, 6, 7⟩ 0 (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop517" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop517`, the loop of `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1654 : Data.core1450.body = oqLoop0T ⟨0, 16, 6, 7⟩ (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop517" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1110 : Data.core1003.body = oqMainT ⟨0, 16, 6, 6⟩ 0 (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop518" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop518`, the loop of `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1656 : Data.core1452.body = oqLoop0T ⟨0, 16, 6, 6⟩ (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop518" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1142 : Data.core1035.body = oqMainT ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop519" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop519`, the loop of `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1663 : Data.core1459.body = oqLoop1T ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop519" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
