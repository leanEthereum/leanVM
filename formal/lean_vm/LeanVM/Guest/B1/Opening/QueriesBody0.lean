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
/-- `opening_queries__L0_L1_L6_L32_L17_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_482 : Data.core482.body = oqMainT (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop340" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop340`. -/
theorem oqLoopBody_482 : Data.core939.body = oqLoop1T (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop340" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_508 : Data.core508.body = oqMainT (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop344" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop344`. -/
theorem oqLoopBody_508 : Data.core944.body = oqLoop1T (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop344" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_530 : Data.core530.body = oqMainT (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop348" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop348`. -/
theorem oqLoopBody_530 : Data.core949.body = oqLoop1T (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop348" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_556 : Data.core556.body = oqMainT (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop352" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop352`. -/
theorem oqLoopBody_556 : Data.core954.body = oqLoop1T (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop352" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_582 : Data.core582.body = oqMainT (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop356" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop356`. -/
theorem oqLoopBody_582 : Data.core959.body = oqLoop1T (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop356" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_600 : Data.core600.body = oqMainT (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop360`. -/
theorem oqLoopBody_600 : Data.core964.body = oqLoop1T (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop360" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_617 : Data.core617.body = oqMainT (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop364`. -/
theorem oqLoopBody_617 : Data.core969.body = oqLoop1T (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop364" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_638 : Data.core638.body = oqMainT (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop368`. -/
theorem oqLoopBody_638 : Data.core974.body = oqLoop1T (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop368" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_658 : Data.core658.body = oqMainT (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop372`. -/
theorem oqLoopBody_658 : Data.core980.body = oqLoop1T (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop372" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_682 : Data.core682.body = oqMainT (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop376`. -/
theorem oqLoopBody_682 : Data.core986.body = oqLoop1T (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop376" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_706 : Data.core706.body = oqMainT (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop380`. -/
theorem oqLoopBody_706 : Data.core992.body = oqLoop1T (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop380" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1`. -/
theorem oqBody_719 : Data.core719.body = oqMainT (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop384`. -/
theorem oqLoopBody_719 : Data.core996.body = oqLoop0T (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop384" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1`. -/
theorem oqBody_756 : Data.core756.body = oqMainT (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop388`. -/
theorem oqLoopBody_756 : Data.core1000.body = oqLoop0T (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop388" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_786 : Data.core786.body = oqMainT (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop392`. -/
theorem oqLoopBody_786 : Data.core1005.body = oqLoop0T (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_802 : Data.core802.body = oqMainT (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop396`. -/
theorem oqLoopBody_802 : Data.core1010.body = oqLoop1T (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_820 : Data.core820.body = oqMainT (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop400`. -/
theorem oqLoopBody_820 : Data.core1016.body = oqLoop1T (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_842 : Data.core842.body = oqMainT (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop404`. -/
theorem oqLoopBody_842 : Data.core1022.body = oqLoop1T (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1`. -/
theorem oqBody_861 : Data.core861.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop408`. -/
theorem oqLoopBody_861 : Data.core1027.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop408" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1`. -/
theorem oqBody_878 : Data.core878.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop412`. -/
theorem oqLoopBody_878 : Data.core1032.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop412" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
