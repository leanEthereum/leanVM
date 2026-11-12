/-
  LeanVM.Guest.B1.Opening.QueriesBody2

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
/-- `opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1013 : Data.core1013.body = oqMainT (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop504" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop504`. -/
theorem oqLoopBody_1013 : Data.core1512.body = oqLoop1T (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop504" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1024 : Data.core1024.body = oqMainT (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop508" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop508`. -/
theorem oqLoopBody_1024 : Data.core1517.body = oqLoop0T (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop508" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1`. -/
theorem oqBody_1039 : Data.core1039.body = oqMainT (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop512" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop512`. -/
theorem oqLoopBody_1039 : Data.core1521.body = oqLoop0T (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop512" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1071 : Data.core1071.body = oqMainT (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop516" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop516`. -/
theorem oqLoopBody_1071 : Data.core1526.body = oqLoop1T (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop516" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1`. -/
theorem oqBody_1081 : Data.core1081.body = oqMainT (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop520" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop520`. -/
theorem oqLoopBody_1081 : Data.core1530.body = oqLoop0T (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop520" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1116 : Data.core1116.body = oqMainT (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop524" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop524`. -/
theorem oqLoopBody_1116 : Data.core1535.body = oqLoop0T (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop524" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1`. -/
theorem oqBody_1122 : Data.core1122.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop528" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop528`. -/
theorem oqLoopBody_1122 : Data.core1539.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop528" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1`. -/
theorem oqBody_1159 : Data.core1159.body = oqMainT (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop532" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop532`. -/
theorem oqLoopBody_1159 : Data.core1544.body = oqLoop0T (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop532" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1190 : Data.core1190.body = oqMainT (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop536" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop536`. -/
theorem oqLoopBody_1190 : Data.core1548.body = oqLoop1T (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop536" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1`. -/
theorem oqBody_1200 : Data.core1200.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop540" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop540`. -/
theorem oqLoopBody_1200 : Data.core1553.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop540" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1241 : Data.core1241.body = oqMainT (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop544" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop544`. -/
theorem oqLoopBody_1241 : Data.core1558.body = oqLoop0T (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop544" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1280 : Data.core1280.body = oqMainT (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop548" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop548`. -/
theorem oqLoopBody_1280 : Data.core1562.body = oqLoop1T (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop548" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1`. -/
theorem oqBody_1290 : Data.core1290.body = oqMainT (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop552" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop552`. -/
theorem oqLoopBody_1290 : Data.core1567.body = oqLoop0T (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop552" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1329 : Data.core1329.body = oqMainT (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop556" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop556`. -/
theorem oqLoopBody_1329 : Data.core1572.body = oqLoop0T (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop556" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1367 : Data.core1367.body = oqMainT (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop560" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop560`. -/
theorem oqLoopBody_1367 : Data.core1576.body = oqLoop1T (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop560" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1`. -/
theorem oqBody_1378 : Data.core1378.body = oqMainT (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop564" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop564`. -/
theorem oqLoopBody_1378 : Data.core1581.body = oqLoop0T (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop564" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1422 : Data.core1422.body = oqMainT (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop568" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop568`. -/
theorem oqLoopBody_1422 : Data.core1586.body = oqLoop0T (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop568" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1464 : Data.core1464.body = oqMainT (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop572" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop572`. -/
theorem oqLoopBody_1464 : Data.core1590.body = oqLoop1T (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop572" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1`. -/
theorem oqBody_1475 : Data.core1475.body = oqMainT (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop576" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop576`. -/
theorem oqLoopBody_1475 : Data.core1595.body = oqLoop0T (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop576" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
