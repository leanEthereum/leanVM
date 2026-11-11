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
/-- `opening_queries__L0_L0_L4_L16_L14_L5_L4_L39_L20_L5_L1`. -/
theorem oqBody_496 : Data.core496.body = oqMainT (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop343`. -/
theorem oqLoopBody_496 : Data.core923.body = oqLoop0T (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1`. -/
theorem oqBody_515 : Data.core515.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop347" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop347`. -/
theorem oqLoopBody_515 : Data.core927.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop347" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1`. -/
theorem oqBody_535 : Data.core535.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop351" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop351`. -/
theorem oqLoopBody_535 : Data.core931.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop351" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1`. -/
theorem oqBody_557 : Data.core557.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop355" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop355`. -/
theorem oqLoopBody_557 : Data.core935.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop355" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1`. -/
theorem oqBody_575 : Data.core575.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop359`. -/
theorem oqLoopBody_575 : Data.core939.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1`. -/
theorem oqBody_592 : Data.core592.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop363`. -/
theorem oqLoopBody_592 : Data.core943.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1`. -/
theorem oqBody_611 : Data.core611.body = oqMainT (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop367`. -/
theorem oqLoopBody_611 : Data.core947.body = oqLoop0T (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1`. -/
theorem oqBody_634 : Data.core634.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop371`. -/
theorem oqLoopBody_634 : Data.core953.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1`. -/
theorem oqBody_657 : Data.core657.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop375`. -/
theorem oqLoopBody_657 : Data.core959.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1`. -/
theorem oqBody_681 : Data.core681.body = oqMainT (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop379`. -/
theorem oqLoopBody_681 : Data.core965.body = oqLoop0T (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1`. -/
theorem oqBody_699 : Data.core699.body = oqMainT (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop383`. -/
theorem oqLoopBody_699 : Data.core970.body = oqLoop0T (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1`. -/
theorem oqBody_736 : Data.core736.body = oqMainT (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop387`. -/
theorem oqLoopBody_736 : Data.core974.body = oqLoop0T (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_767 : Data.core767.body = oqMainT (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop391`. -/
theorem oqLoopBody_767 : Data.core979.body = oqLoop0T (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_783 : Data.core783.body = oqMainT (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop395`. -/
theorem oqLoopBody_783 : Data.core984.body = oqLoop1T (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_801 : Data.core801.body = oqMainT (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop399`. -/
theorem oqLoopBody_801 : Data.core990.body = oqLoop1T (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_823 : Data.core823.body = oqMainT (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop403`. -/
theorem oqLoopBody_823 : Data.core996.body = oqLoop1T (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1`. -/
theorem oqBody_842 : Data.core842.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop407`. -/
theorem oqLoopBody_842 : Data.core1001.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1`. -/
theorem oqBody_859 : Data.core859.body = oqMainT (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop411`. -/
theorem oqLoopBody_859 : Data.core1006.body = oqLoop0T (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
