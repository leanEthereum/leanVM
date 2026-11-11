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
theorem oqBody_487 : Data.core487.body = oqMainT (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop341" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop341`. -/
theorem oqLoopBody_487 : Data.core921.body = oqLoop0T (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop341" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_508 : Data.core508.body = oqMainT (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop345" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop345`. -/
theorem oqLoopBody_508 : Data.core925.body = oqLoop0T (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop345" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_527 : Data.core527.body = oqMainT (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop349" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop349`. -/
theorem oqLoopBody_527 : Data.core929.body = oqLoop0T (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop349" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_548 : Data.core548.body = oqMainT (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop353" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop353`. -/
theorem oqLoopBody_548 : Data.core933.body = oqLoop0T (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop353" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_569 : Data.core569.body = oqMainT (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop357`. -/
theorem oqLoopBody_569 : Data.core937.body = oqLoop0T (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop357" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_586 : Data.core586.body = oqMainT (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop361`. -/
theorem oqLoopBody_586 : Data.core941.body = oqLoop0T (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop361" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_602 : Data.core602.body = oqMainT (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop365`. -/
theorem oqLoopBody_602 : Data.core945.body = oqLoop0T (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1`. -/
theorem oqBody_624 : Data.core624.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop369`. -/
theorem oqLoopBody_624 : Data.core950.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1`. -/
theorem oqBody_645 : Data.core645.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop373`. -/
theorem oqLoopBody_645 : Data.core956.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop373" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1`. -/
theorem oqBody_669 : Data.core669.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop377`. -/
theorem oqLoopBody_669 : Data.core962.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_691 : Data.core691.body = oqMainT (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop381`. -/
theorem oqLoopBody_691 : Data.core968.body = oqLoop0T (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem oqBody_717 : Data.core717.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop385`. -/
theorem oqLoopBody_717 : Data.core972.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem oqBody_757 : Data.core757.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop389`. -/
theorem oqLoopBody_757 : Data.core976.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop389" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_774 : Data.core774.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop393`. -/
theorem oqLoopBody_774 : Data.core981.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop393" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_792 : Data.core792.body = oqMainT (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop397`. -/
theorem oqLoopBody_792 : Data.core987.body = oqLoop1T (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_812 : Data.core812.body = oqMainT (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop401`. -/
theorem oqLoopBody_812 : Data.core993.body = oqLoop1T (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop401" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_835 : Data.core835.body = oqMainT (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop405`. -/
theorem oqLoopBody_835 : Data.core999.body = oqLoop1T (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_852 : Data.core852.body = oqMainT (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop409`. -/
theorem oqLoopBody_852 : Data.core1004.body = oqLoop0T (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
