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
/-- `opening_queries__L0_L0_L4_L16_L16_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_489 : Data.core489.body = oqMainT (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop341" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop341`. -/
theorem oqLoopBody_489 : Data.core940.body = oqLoop0T (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop341" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_513 : Data.core513.body = oqMainT (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop345" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop345`. -/
theorem oqLoopBody_513 : Data.core945.body = oqLoop0T (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop345" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_535 : Data.core535.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop349" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop349`. -/
theorem oqLoopBody_535 : Data.core950.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop349" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_561 : Data.core561.body = oqMainT (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop353" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop353`. -/
theorem oqLoopBody_561 : Data.core955.body = oqLoop0T (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop353" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_585 : Data.core585.body = oqMainT (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop357`. -/
theorem oqLoopBody_585 : Data.core960.body = oqLoop0T (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_603 : Data.core603.body = oqMainT (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop361`. -/
theorem oqLoopBody_603 : Data.core965.body = oqLoop0T (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_620 : Data.core620.body = oqMainT (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop365`. -/
theorem oqLoopBody_620 : Data.core970.body = oqLoop0T (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1`. -/
theorem oqBody_642 : Data.core642.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop369`. -/
theorem oqLoopBody_642 : Data.core975.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1`. -/
theorem oqBody_663 : Data.core663.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop373`. -/
theorem oqLoopBody_663 : Data.core981.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1`. -/
theorem oqBody_687 : Data.core687.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop377`. -/
theorem oqLoopBody_687 : Data.core987.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_709 : Data.core709.body = oqMainT (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop381`. -/
theorem oqLoopBody_709 : Data.core993.body = oqLoop0T (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L4_L1131_L20_L5_L1`. -/
theorem oqBody_729 : Data.core729.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop385`. -/
theorem oqLoopBody_729 : Data.core997.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L4_L1464_L20_L5_L1`. -/
theorem oqBody_766 : Data.core766.body = oqMainT (⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop389`. -/
theorem oqLoopBody_766 : Data.core1001.body = oqLoop0T (⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_789 : Data.core789.body = oqMainT (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop393`. -/
theorem oqLoopBody_789 : Data.core1006.body = oqLoop0T (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L1677_L20_L5_L1`. -/
theorem oqBody_806 : Data.core806.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop397`. -/
theorem oqLoopBody_806 : Data.core1011.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L1846_L8_L3_L1`. -/
theorem oqBody_825 : Data.core825.body = oqMainT (⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop401`. -/
theorem oqLoopBody_825 : Data.core1017.body = oqLoop0T (⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L4_L2010_L20_L5_L1`. -/
theorem oqBody_847 : Data.core847.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop405`. -/
theorem oqLoopBody_847 : Data.core1023.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_868 : Data.core868.body = oqMainT (⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop409`. -/
theorem oqLoopBody_868 : Data.core1029.body = oqLoop1T (⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
