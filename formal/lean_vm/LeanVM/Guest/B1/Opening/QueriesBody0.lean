/-
  LeanVM.Guest.B1.Opening.QueriesBody0

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are
  the templates (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1009 : Data.core1009.body = oqMainT (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop502" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop502`. -/
theorem oqLoopBody_1009 : Data.core1508.body = oqLoop1T (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop502" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1022 : Data.core1022.body = oqMainT (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop506" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop506`. -/
theorem oqLoopBody_1022 : Data.core1515.body = oqLoop0T (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop506" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1032 : Data.core1032.body = oqMainT (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop510" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop510`. -/
theorem oqLoopBody_1032 : Data.core1519.body = oqLoop0T (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop510" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1`. -/
theorem oqBody_1041 : Data.core1041.body = oqMainT (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop514" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop514`. -/
theorem oqLoopBody_1041 : Data.core1523.body = oqLoop0T (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop514" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1`. -/
theorem oqBody_1079 : Data.core1079.body = oqMainT (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop518" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop518`. -/
theorem oqLoopBody_1079 : Data.core1528.body = oqLoop0T (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop518" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1110 : Data.core1110.body = oqMainT (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop522" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop522`. -/
theorem oqLoopBody_1110 : Data.core1532.body = oqLoop1T (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop522" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1`. -/
theorem oqBody_1120 : Data.core1120.body = oqMainT (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop526" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop526`. -/
theorem oqLoopBody_1120 : Data.core1537.body = oqLoop0T (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop526" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1151 : Data.core1151.body = oqMainT (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop530" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop530`. -/
theorem oqLoopBody_1151 : Data.core1542.body = oqLoop1T (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop530" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1`. -/
theorem oqBody_1161 : Data.core1161.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop534" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop534`. -/
theorem oqLoopBody_1161 : Data.core1546.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop534" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1195 : Data.core1195.body = oqMainT (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop538" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop538`. -/
theorem oqLoopBody_1195 : Data.core1551.body = oqLoop0T (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop538" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_1236 : Data.core1236.body = oqMainT (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop542" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop542`. -/
theorem oqLoopBody_1236 : Data.core1555.body = oqLoop1T (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop542" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1`. -/
theorem oqBody_1246 : Data.core1246.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop546" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop546`. -/
theorem oqLoopBody_1246 : Data.core1560.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop546" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1285 : Data.core1285.body = oqMainT (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop550" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop550`. -/
theorem oqLoopBody_1285 : Data.core1565.body = oqLoop0T (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop550" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1324 : Data.core1324.body = oqMainT (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop554" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop554`. -/
theorem oqLoopBody_1324 : Data.core1569.body = oqLoop1T (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop554" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1`. -/
theorem oqBody_1333 : Data.core1333.body = oqMainT (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop558" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop558`. -/
theorem oqLoopBody_1333 : Data.core1574.body = oqLoop0T (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop558" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1372 : Data.core1372.body = oqMainT (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop562" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop562`. -/
theorem oqLoopBody_1372 : Data.core1579.body = oqLoop0T (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop562" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1417 : Data.core1417.body = oqMainT (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop566" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop566`. -/
theorem oqLoopBody_1417 : Data.core1583.body = oqLoop1T (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop566" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1`. -/
theorem oqBody_1427 : Data.core1427.body = oqMainT (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop570" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop570`. -/
theorem oqLoopBody_1427 : Data.core1588.body = oqLoop0T (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop570" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1469 : Data.core1469.body = oqMainT (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop574" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop574`. -/
theorem oqLoopBody_1469 : Data.core1593.body = oqLoop0T (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop574" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
