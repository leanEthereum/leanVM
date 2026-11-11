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
theorem oqBody_1413 : Data.core1413.body = oqMainT ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop635" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop635`, the loop of `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem oqBody_1720 : Data.core1720.body = oqLoop1T ⟨1, 64, 24, 2⟩ 0 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop635" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1417 : Data.core1417.body = oqMainT ⟨0, 16, 18, 7⟩ 0 (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop636" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop636`, the loop of `opening_queries__L0_L0_L16_L24_L25_L7`. -/
theorem oqBody_1721 : Data.core1721.body = oqLoop0T ⟨0, 16, 18, 7⟩ (oqWalkOf ⟨0, 16, 18, 7⟩) "__loop636" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1454 : Data.core1454.body = oqMainT ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop637" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop637`, the loop of `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem oqBody_1725 : Data.core1725.body = oqLoop1T ⟨1, 64, 24, 2⟩ 1 (oqWalkOf ⟨1, 64, 24, 2⟩) "__loop637" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1455 : Data.core1455.body = oqMainT ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop638" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop638`, the loop of `opening_queries__L1_L1_L64_L32_L27_L3`. -/
theorem oqBody_1727 : Data.core1727.body = oqLoop1T ⟨1, 64, 24, 3⟩ 1 (oqWalkOf ⟨1, 64, 24, 3⟩) "__loop638" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1459 : Data.core1459.body = oqMainT ⟨0, 16, 24, 2⟩ 0 (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop639" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop639`, the loop of `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem oqBody_1728 : Data.core1728.body = oqLoop0T ⟨0, 16, 24, 2⟩ (oqWalkOf ⟨0, 16, 24, 2⟩) "__loop639" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1498 : Data.core1498.body = oqMainT ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop640" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop640`, the loop of `opening_queries__L1_L1_L64_L32_L28_L4`. -/
theorem oqBody_1732 : Data.core1732.body = oqLoop1T ⟨1, 64, 24, 4⟩ 1 (oqWalkOf ⟨1, 64, 24, 4⟩) "__loop640" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1502 : Data.core1502.body = oqMainT ⟨0, 16, 24, 3⟩ 0 (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop641" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop641`, the loop of `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem oqBody_1733 : Data.core1733.body = oqLoop0T ⟨0, 16, 24, 3⟩ (oqWalkOf ⟨0, 16, 24, 3⟩) "__loop641" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem oqBody_1545 : Data.core1545.body = oqMainT ⟨1, 64, 18, 8⟩ 0 (oqWalkOf ⟨1, 64, 18, 8⟩) "__loop642" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop642`, the loop of `opening_queries__L0_L1_L64_L32_L26_L8`. -/
theorem oqBody_1737 : Data.core1737.body = oqLoop1T ⟨1, 64, 18, 8⟩ 0 (oqWalkOf ⟨1, 64, 18, 8⟩) "__loop642" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem oqBody_1546 : Data.core1546.body = oqMainT ⟨1, 64, 24, 5⟩ 1 (oqWalkOf ⟨1, 64, 24, 5⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop643`, the loop of `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem oqBody_1739 : Data.core1739.body = oqLoop1T ⟨1, 64, 24, 5⟩ 1 (oqWalkOf ⟨1, 64, 24, 5⟩) "__loop643" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem oqBody_1550 : Data.core1550.body = oqMainT ⟨0, 16, 24, 4⟩ 0 (oqWalkOf ⟨0, 16, 24, 4⟩) "__loop644" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop644`, the loop of `opening_queries__L0_L0_L16_L24_L28_L4`. -/
theorem oqBody_1740 : Data.core1740.body = oqLoop0T ⟨0, 16, 24, 4⟩ (oqWalkOf ⟨0, 16, 24, 4⟩) "__loop644" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem oqBody_1592 : Data.core1592.body = oqMainT ⟨1, 64, 24, 6⟩ 1 (oqWalkOf ⟨1, 64, 24, 6⟩) "__loop645" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop645`, the loop of `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem oqBody_1744 : Data.core1744.body = oqLoop1T ⟨1, 64, 24, 6⟩ 1 (oqWalkOf ⟨1, 64, 24, 6⟩) "__loop645" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem oqBody_1596 : Data.core1596.body = oqMainT ⟨0, 16, 24, 5⟩ 0 (oqWalkOf ⟨0, 16, 24, 5⟩) "__loop646" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop646`, the loop of `opening_queries__L0_L0_L16_L24_L29_L5`. -/
theorem oqBody_1745 : Data.core1745.body = oqLoop0T ⟨0, 16, 24, 5⟩ (oqWalkOf ⟨0, 16, 24, 5⟩) "__loop646" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
