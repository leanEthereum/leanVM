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
/-- `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1113 : Data.core1113.body = oqMainT ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop622" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop622`, the loop of `opening_queries__L1_L1_L64_L32_L16_L4`. -/
theorem oqBody_1693 : Data.core1693.body = oqLoop1T ⟨1, 64, 12, 4⟩ 1 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop622" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1124 : Data.core1124.body = oqMainT ⟨0, 16, 12, 3⟩ 0 (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop626" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop626`, the loop of `opening_queries__L0_L0_L16_L24_L15_L3`. -/
theorem oqBody_1699 : Data.core1699.body = oqLoop0T ⟨0, 16, 12, 3⟩ (oqWalkOf ⟨0, 16, 12, 3⟩) "__loop626" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1156 : Data.core1156.body = oqMainT ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop630" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop630`, the loop of `opening_queries__L0_L1_L64_L32_L16_L4`. -/
theorem oqBody_1709 : Data.core1709.body = oqLoop1T ⟨1, 64, 12, 4⟩ 0 (oqWalkOf ⟨1, 64, 12, 4⟩) "__loop630" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1198 : Data.core1198.body = oqMainT ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop634" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop634`, the loop of `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1720 : Data.core1720.body = oqLoop1T ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop634" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1236 : Data.core1236.body = oqMainT ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop638" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop638`, the loop of `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1730 : Data.core1730.body = oqLoop1T ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop638" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1277 : Data.core1277.body = oqMainT ⟨0, 16, 18, 2⟩ 0 (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop642" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop642`, the loop of `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1740 : Data.core1740.body = oqLoop0T ⟨0, 16, 18, 2⟩ (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop642" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1345 : Data.core1345.body = oqMainT ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop646" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop646`, the loop of `opening_queries__L0_L1_L64_L32_L20_L8`. -/
theorem oqBody_1750 : Data.core1750.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 (oqWalkOf ⟨1, 64, 12, 8⟩) "__loop646" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1384 : Data.core1384.body = oqMainT ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop650" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop650`, the loop of `opening_queries__L1_L1_L64_L32_L23_L5`. -/
theorem oqBody_1758 : Data.core1758.body = oqLoop1T ⟨1, 64, 18, 5⟩ 1 (oqWalkOf ⟨1, 64, 18, 5⟩) "__loop650" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1423 : Data.core1423.body = oqMainT ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop654" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop654`, the loop of `opening_queries__L0_L1_L64_L32_L25_L7`. -/
theorem oqBody_1765 : Data.core1765.body = oqLoop1T ⟨1, 64, 18, 7⟩ 0 (oqWalkOf ⟨1, 64, 18, 7⟩) "__loop654" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1464 : Data.core1464.body = oqMainT ⟨0, 16, 18, 7⟩ 0 (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop658" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop658`, the loop of `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1772 : Data.core1772.body = oqLoop0T ⟨0, 16, 18, 7⟩ (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop658" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1545 : Data.core1545.body = oqMainT ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop662" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop662`, the loop of `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1783 : Data.core1783.body = oqLoop1T ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop662" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem oqBody_1597 : Data.core1597.body = oqMainT ⟨0, 16, 24, 4⟩ 0 (oqWalkOf ⟨0, 16, 24, 4⟩) "__loop666" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop666`, the loop of `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem oqBody_1791 : Data.core1791.body = oqLoop0T ⟨0, 16, 24, 4⟩ (oqWalkOf ⟨0, 16, 24, 4⟩) "__loop666" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
