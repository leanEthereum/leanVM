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
theorem oqBody_492 : Data.core492.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop342`. -/
theorem oqLoopBody_492 : Data.core923.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop342" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_512 : Data.core512.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop346" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop346`. -/
theorem oqLoopBody_512 : Data.core927.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop346" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_531 : Data.core531.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop350`. -/
theorem oqLoopBody_531 : Data.core931.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop350" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_552 : Data.core552.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop354" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop354`. -/
theorem oqLoopBody_552 : Data.core935.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop354" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_572 : Data.core572.body = oqMainT (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop358" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop358`. -/
theorem oqLoopBody_572 : Data.core939.body = oqLoop0T (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop358" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_589 : Data.core589.body = oqMainT (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop362`. -/
theorem oqLoopBody_589 : Data.core943.body = oqLoop0T (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop362" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_605 : Data.core605.body = oqMainT (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop366`. -/
theorem oqLoopBody_605 : Data.core947.body = oqLoop0T (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_630 : Data.core630.body = oqMainT (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop370`. -/
theorem oqLoopBody_630 : Data.core953.body = oqLoop1T (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_652 : Data.core652.body = oqMainT (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop374`. -/
theorem oqLoopBody_652 : Data.core959.body = oqLoop1T (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_676 : Data.core676.body = oqMainT (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop378`. -/
theorem oqLoopBody_676 : Data.core965.body = oqLoop1T (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_694 : Data.core694.body = oqMainT (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop382`. -/
theorem oqLoopBody_694 : Data.core970.body = oqLoop0T (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1`. -/
theorem oqBody_719 : Data.core719.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop386`. -/
theorem oqLoopBody_719 : Data.core974.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1`. -/
theorem oqBody_758 : Data.core758.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop390`. -/
theorem oqLoopBody_758 : Data.core978.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop390" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_775 : Data.core775.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop394`. -/
theorem oqLoopBody_775 : Data.core983.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop394" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_793 : Data.core793.body = oqMainT (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop398`. -/
theorem oqLoopBody_793 : Data.core989.body = oqLoop1T (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop398" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_813 : Data.core813.body = oqMainT (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop402`. -/
theorem oqLoopBody_813 : Data.core995.body = oqLoop1T (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_836 : Data.core836.body = oqMainT (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop406`. -/
theorem oqLoopBody_836 : Data.core1001.body = oqLoop1T (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop406" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_853 : Data.core853.body = oqMainT (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop410`. -/
theorem oqLoopBody_853 : Data.core1006.body = oqLoop0T (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop410" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
