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
theorem oqBody_1143 : Data.core1143.body = oqMainT ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop611" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop611`, the loop of `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem oqBody_1664 : Data.core1664.body = oqLoop1T ⟨1, 64, 12, 5⟩ 0 (oqWalkOf ⟨1, 64, 12, 5⟩) "__loop611" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1144 : Data.core1144.body = oqMainT ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop612" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop612`, the loop of `opening_queries__L1_L1_L64_L32_L18_L6`. -/
theorem oqBody_1666 : Data.core1666.body = oqLoop1T ⟨1, 64, 12, 6⟩ 1 (oqWalkOf ⟨1, 64, 12, 6⟩) "__loop612" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1145 : Data.core1145.body = oqMainT ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop613" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop613`, the loop of `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem oqBody_1667 : Data.core1667.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop613" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1149 : Data.core1149.body = oqMainT ⟨0, 16, 12, 6⟩ 0 (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop614" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop614`, the loop of `opening_queries__L0_L0_L16_L24_L18_L6`. -/
theorem oqBody_1668 : Data.core1668.body = oqLoop0T ⟨0, 16, 12, 6⟩ (oqWalkOf ⟨0, 16, 12, 6⟩) "__loop614" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1182 : Data.core1182.body = oqMainT ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop615" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop615`, the loop of `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem oqBody_1675 : Data.core1675.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 (oqWalkOf ⟨1, 64, 12, 7⟩) "__loop615" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1183 : Data.core1183.body = oqMainT ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop616" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop616`, the loop of `opening_queries__L0_L1_L64_L32_L20_L2`. -/
theorem oqBody_1676 : Data.core1676.body = oqLoop1T ⟨1, 64, 18, 2⟩ 0 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop616" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1187 : Data.core1187.body = oqMainT ⟨0, 16, 12, 7⟩ 0 (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop617" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop617`, the loop of `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem oqBody_1677 : Data.core1677.body = oqLoop0T ⟨0, 16, 12, 7⟩ (oqWalkOf ⟨0, 16, 12, 7⟩) "__loop617" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1220 : Data.core1220.body = oqMainT ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop618" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop618`, the loop of `opening_queries__L1_L1_L64_L32_L20_L2`. -/
theorem oqBody_1684 : Data.core1684.body = oqLoop1T ⟨1, 64, 18, 2⟩ 1 (oqWalkOf ⟨1, 64, 18, 2⟩) "__loop618" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1221 : Data.core1221.body = oqMainT ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop619" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop619`, the loop of `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem oqBody_1685 : Data.core1685.body = oqLoop1T ⟨1, 64, 18, 3⟩ 0 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop619" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1225 : Data.core1225.body = oqMainT ⟨0, 16, 18, 2⟩ 0 (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop620" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop620`, the loop of `opening_queries__L0_L0_L16_L24_L20_L2`. -/
theorem oqBody_1686 : Data.core1686.body = oqLoop0T ⟨0, 16, 18, 2⟩ (oqWalkOf ⟨0, 16, 18, 2⟩) "__loop620" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1258 : Data.core1258.body = oqMainT ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop621" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop621`, the loop of `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem oqBody_1693 : Data.core1693.body = oqLoop1T ⟨1, 64, 18, 3⟩ 1 (oqWalkOf ⟨1, 64, 18, 3⟩) "__loop621" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1259 : Data.core1259.body = oqMainT ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop622" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop622`, the loop of `opening_queries__L0_L1_L64_L32_L22_L4`. -/
theorem oqBody_1694 : Data.core1694.body = oqLoop1T ⟨1, 64, 18, 4⟩ 0 (oqWalkOf ⟨1, 64, 18, 4⟩) "__loop622" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
