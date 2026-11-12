/-
  LeanVM.Guest.B1.Opening.QueriesBody3

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
/-- `opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1015 : Data.core1015.body = oqMainT (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop505" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop505`. -/
theorem oqLoopBody_1015 : Data.core1514.body = oqLoop1T (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop505" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1025 : Data.core1025.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop509" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop509`. -/
theorem oqLoopBody_1025 : Data.core1518.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop509" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1`. -/
theorem oqBody_1040 : Data.core1040.body = oqMainT (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop513" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop513`. -/
theorem oqLoopBody_1040 : Data.core1522.body = oqLoop0T (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop513" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1076 : Data.core1076.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop517" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop517`. -/
theorem oqLoopBody_1076 : Data.core1527.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop517" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1`. -/
theorem oqBody_1082 : Data.core1082.body = oqMainT (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop521" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop521`. -/
theorem oqLoopBody_1082 : Data.core1531.body = oqLoop0T (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop521" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1`. -/
theorem oqBody_1119 : Data.core1119.body = oqMainT (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop525" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop525`. -/
theorem oqLoopBody_1119 : Data.core1536.body = oqLoop0T (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop525" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1150 : Data.core1150.body = oqMainT (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop529" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop529`. -/
theorem oqLoopBody_1150 : Data.core1540.body = oqLoop1T (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop529" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1`. -/
theorem oqBody_1160 : Data.core1160.body = oqMainT (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop533" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop533`. -/
theorem oqLoopBody_1160 : Data.core1545.body = oqLoop0T (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop533" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1191 : Data.core1191.body = oqMainT (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop537" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop537`. -/
theorem oqLoopBody_1191 : Data.core1550.body = oqLoop1T (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop537" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1`. -/
theorem oqBody_1201 : Data.core1201.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop541" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop541`. -/
theorem oqLoopBody_1201 : Data.core1554.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop541" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1`. -/
theorem oqBody_1245 : Data.core1245.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop545" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop545`. -/
theorem oqLoopBody_1245 : Data.core1559.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop545" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1281 : Data.core1281.body = oqMainT (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop549" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop549`. -/
theorem oqLoopBody_1281 : Data.core1564.body = oqLoop1T (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop549" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1`. -/
theorem oqBody_1291 : Data.core1291.body = oqMainT (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop553" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop553`. -/
theorem oqLoopBody_1291 : Data.core1568.body = oqLoop0T (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop553" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1`. -/
theorem oqBody_1332 : Data.core1332.body = oqMainT (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop557" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop557`. -/
theorem oqLoopBody_1332 : Data.core1573.body = oqLoop0T (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop557" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1368 : Data.core1368.body = oqMainT (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop561" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop561`. -/
theorem oqLoopBody_1368 : Data.core1578.body = oqLoop1T (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop561" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1`. -/
theorem oqBody_1379 : Data.core1379.body = oqMainT (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop565" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop565`. -/
theorem oqLoopBody_1379 : Data.core1582.body = oqLoop0T (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop565" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1`. -/
theorem oqBody_1426 : Data.core1426.body = oqMainT (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop569" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop569`. -/
theorem oqLoopBody_1426 : Data.core1587.body = oqLoop0T (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop569" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1465 : Data.core1465.body = oqMainT (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop573" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop573`. -/
theorem oqLoopBody_1465 : Data.core1592.body = oqLoop1T (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop573" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1`. -/
theorem oqBody_1476 : Data.core1476.body = oqMainT (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop577" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop577`. -/
theorem oqLoopBody_1476 : Data.core1596.body = oqLoop0T (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop577" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
