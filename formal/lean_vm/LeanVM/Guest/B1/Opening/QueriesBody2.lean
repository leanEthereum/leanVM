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
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_495 : Data.core495.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop342`. -/
theorem oqLoopBody_495 : Data.core941.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_518 : Data.core518.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop346" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop346`. -/
theorem oqLoopBody_518 : Data.core946.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop346" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_540 : Data.core540.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop350`. -/
theorem oqLoopBody_540 : Data.core951.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_566 : Data.core566.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop354" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop354`. -/
theorem oqLoopBody_566 : Data.core956.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop354" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_588 : Data.core588.body = oqMainT (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop358" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop358`. -/
theorem oqLoopBody_588 : Data.core961.body = oqLoop0T (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop358" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_606 : Data.core606.body = oqMainT (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop362`. -/
theorem oqLoopBody_606 : Data.core966.body = oqLoop0T (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_623 : Data.core623.body = oqMainT (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop366`. -/
theorem oqLoopBody_623 : Data.core971.body = oqLoop0T (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_648 : Data.core648.body = oqMainT (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop370`. -/
theorem oqLoopBody_648 : Data.core977.body = oqLoop1T (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_670 : Data.core670.body = oqMainT (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop374`. -/
theorem oqLoopBody_670 : Data.core983.body = oqLoop1T (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_694 : Data.core694.body = oqMainT (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop378`. -/
theorem oqLoopBody_694 : Data.core989.body = oqLoop1T (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_712 : Data.core712.body = oqMainT (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop382`. -/
theorem oqLoopBody_712 : Data.core994.body = oqLoop0T (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem oqBody_737 : Data.core737.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop386`. -/
theorem oqLoopBody_737 : Data.core998.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem oqBody_776 : Data.core776.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop390`. -/
theorem oqLoopBody_776 : Data.core1002.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_793 : Data.core793.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop394`. -/
theorem oqLoopBody_793 : Data.core1007.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_811 : Data.core811.body = oqMainT (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop398`. -/
theorem oqLoopBody_811 : Data.core1013.body = oqLoop1T (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_831 : Data.core831.body = oqMainT (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop402`. -/
theorem oqLoopBody_831 : Data.core1019.body = oqLoop1T (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_854 : Data.core854.body = oqMainT (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop406`. -/
theorem oqLoopBody_854 : Data.core1025.body = oqLoop1T (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_871 : Data.core871.body = oqMainT (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop410`. -/
theorem oqLoopBody_871 : Data.core1030.body = oqLoop0T (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
