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
theorem oqBody_1084 : Data.core1084.body = oqMainT ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop600" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop600`, the loop of `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem oqBody_1643 : Data.core1643.body = oqLoop1T ⟨1, 64, 12, 3⟩ 1 (oqWalkOf ⟨1, 64, 12, 3⟩) "__loop600" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1086 : Data.core1086.body = oqMainT ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop601" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop601`, the loop of `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1644 : Data.core1644.body = oqLoop1T ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop601" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1088 : Data.core1088.body = oqMainT ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop602" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop602`, the loop of `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem oqBody_1646 : Data.core1646.body = oqLoop1T ⟨1, 64, 12, 5⟩ 1 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop602" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1090 : Data.core1090.body = oqMainT ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop603" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop603`, the loop of `opening_queries__L0_L1_L64_L32_L18_L6`. -/
theorem oqBody_1647 : Data.core1647.body = oqLoop1T ⟨1, 64, 12, 6⟩ 0 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop603" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1096 : Data.core1096.body = oqMainT ⟨0, 16, 12, 2⟩ 0 (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop604" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop604`, the loop of `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem oqBody_1649 : Data.core1649.body = oqLoop0T ⟨0, 16, 12, 2⟩ (oqWalkOf ⟨0, 16, 12, 2⟩) "__loop604" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1097 : Data.core1097.body = oqMainT ⟨0, 16, 12, 3⟩ 0 (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop605" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop605`, the loop of `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1650 : Data.core1650.body = oqLoop0T ⟨0, 16, 12, 3⟩ (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop605" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1098 : Data.core1098.body = oqMainT ⟨0, 16, 12, 4⟩ 0 (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop606" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop606`, the loop of `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem oqBody_1651 : Data.core1651.body = oqLoop0T ⟨0, 16, 12, 4⟩ (oqWalkOf ⟨0, 16, 12, 4⟩) "__loop606" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1099 : Data.core1099.body = oqMainT ⟨0, 16, 12, 5⟩ 0 (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop607" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop607`, the loop of `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem oqBody_1652 : Data.core1652.body = oqLoop0T ⟨0, 16, 12, 5⟩ (oqWalkOf ⟨0, 16, 12, 5⟩) "__loop607" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1105 : Data.core1105.body = oqMainT ⟨0, 16, 6, 7⟩ 0 (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop608" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop608`, the loop of `opening_queries__L0_L0_L16_L24_L13_L7`. -/
theorem oqBody_1654 : Data.core1654.body = oqLoop0T ⟨0, 16, 6, 7⟩ (oqWalkOf ⟨0, 16, 6, 7⟩) "__loop608" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1110 : Data.core1110.body = oqMainT ⟨0, 16, 6, 6⟩ 0 (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop609" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop609`, the loop of `opening_queries__L0_L0_L16_L24_L12_L6`. -/
theorem oqBody_1656 : Data.core1656.body = oqLoop0T ⟨0, 16, 6, 6⟩ (oqWalkOf ⟨0, 16, 6, 6⟩) "__loop609" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1142 : Data.core1142.body = oqMainT ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop610" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop610`, the loop of `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1663 : Data.core1663.body = oqLoop1T ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop610" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
