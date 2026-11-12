/-
  LeanVM.Guest.B1.Opening.QueriesBody1

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
/-- `opening_queries__L1_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1011 : Data.core1011.body = oqMainT (⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop503" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop503`. -/
theorem oqLoopBody_1011 : Data.core1510.body = oqLoop1T (⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop503" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1023 : Data.core1023.body = oqMainT (⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop507" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop507`. -/
theorem oqLoopBody_1023 : Data.core1516.body = oqLoop0T (⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop507" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L12_L6_L2_L3_L8_L3_L1`. -/
theorem oqBody_1038 : Data.core1038.body = oqMainT (⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop511" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop511`. -/
theorem oqLoopBody_1038 : Data.core1520.body = oqLoop0T (⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop511" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1070 : Data.core1070.body = oqMainT (⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop515" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop515`. -/
theorem oqLoopBody_1070 : Data.core1524.body = oqLoop1T (⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop515" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L3_L6_L12_L4_L1`. -/
theorem oqBody_1080 : Data.core1080.body = oqMainT (⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop519" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop519`. -/
theorem oqLoopBody_1080 : Data.core1529.body = oqLoop0T (⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop519" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1111 : Data.core1111.body = oqMainT (⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop523" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop523`. -/
theorem oqLoopBody_1111 : Data.core1534.body = oqLoop1T (⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop523" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L4_L10_L20_L5_L1`. -/
theorem oqBody_1121 : Data.core1121.body = oqMainT (⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop527" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop527`. -/
theorem oqLoopBody_1121 : Data.core1538.body = oqLoop0T (⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop527" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1156 : Data.core1156.body = oqMainT (⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop531" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop531`. -/
theorem oqLoopBody_1156 : Data.core1543.body = oqLoop0T (⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop531" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L5_L15_L36_L6_L1`. -/
theorem oqBody_1162 : Data.core1162.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop535" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop535`. -/
theorem oqLoopBody_1162 : Data.core1547.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop535" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L2_L3_L8_L3_L1`. -/
theorem oqBody_1199 : Data.core1199.body = oqMainT (⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop539" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop539`. -/
theorem oqLoopBody_1199 : Data.core1552.body = oqLoop0T (⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop539" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1237 : Data.core1237.body = oqMainT (⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop543" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop543`. -/
theorem oqLoopBody_1237 : Data.core1557.body = oqLoop1T (⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop543" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L3_L6_L12_L4_L1`. -/
theorem oqBody_1247 : Data.core1247.body = oqMainT (⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop547" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop547`. -/
theorem oqLoopBody_1247 : Data.core1561.body = oqLoop0T (⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop547" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1`. -/
theorem oqBody_1289 : Data.core1289.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop551" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop551`. -/
theorem oqLoopBody_1289 : Data.core1566.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop551" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1325 : Data.core1325.body = oqMainT (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop555" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop555`. -/
theorem oqLoopBody_1325 : Data.core1571.body = oqLoop1T (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop555" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L5_L15_L36_L6_L1`. -/
theorem oqBody_1334 : Data.core1334.body = oqMainT (⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop559" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop559`. -/
theorem oqLoopBody_1334 : Data.core1575.body = oqLoop0T (⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop559" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L2_L3_L8_L3_L1`. -/
theorem oqBody_1377 : Data.core1377.body = oqMainT (⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop563" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop563`. -/
theorem oqLoopBody_1377 : Data.core1580.body = oqLoop0T (⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop563" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L27_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1418 : Data.core1418.body = oqMainT (⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop567" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop567`. -/
theorem oqLoopBody_1418 : Data.core1585.body = oqLoop1T (⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop567" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L3_L6_L12_L4_L1`. -/
theorem oqBody_1428 : Data.core1428.body = oqMainT (⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop571" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop571`. -/
theorem oqLoopBody_1428 : Data.core1589.body = oqLoop0T (⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop571" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L4_L10_L20_L5_L1`. -/
theorem oqBody_1474 : Data.core1474.body = oqMainT (⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop575" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop575`. -/
theorem oqLoopBody_1474 : Data.core1594.body = oqLoop0T (⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop575" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
