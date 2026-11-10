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
theorem oqBody_499 : Data.core499.body = oqMainT (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop343`. -/
theorem oqLoopBody_499 : Data.core942.body = oqLoop0T (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop343" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1`. -/
theorem oqBody_521 : Data.core521.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop347" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop347`. -/
theorem oqLoopBody_521 : Data.core947.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop347" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1`. -/
theorem oqBody_546 : Data.core546.body = oqMainT (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop351" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop351`. -/
theorem oqLoopBody_546 : Data.core952.body = oqLoop0T (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop351" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1`. -/
theorem oqBody_572 : Data.core572.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop355" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop355`. -/
theorem oqLoopBody_572 : Data.core957.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop355" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1`. -/
theorem oqBody_591 : Data.core591.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop359`. -/
theorem oqLoopBody_591 : Data.core962.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq) "__loop359" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1`. -/
theorem oqBody_609 : Data.core609.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop363`. -/
theorem oqLoopBody_609 : Data.core967.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop363" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1`. -/
theorem oqBody_629 : Data.core629.body = oqMainT (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop367`. -/
theorem oqLoopBody_629 : Data.core972.body = oqLoop0T (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1`. -/
theorem oqBody_652 : Data.core652.body = oqMainT (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop371`. -/
theorem oqLoopBody_652 : Data.core978.body = oqLoop0T (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1`. -/
theorem oqBody_675 : Data.core675.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop375`. -/
theorem oqLoopBody_675 : Data.core984.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop375" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1`. -/
theorem oqBody_699 : Data.core699.body = oqMainT (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop379`. -/
theorem oqLoopBody_699 : Data.core990.body = oqLoop0T (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_716 : Data.core716.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop383`. -/
theorem oqLoopBody_716 : Data.core995.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop383" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1`. -/
theorem oqBody_746 : Data.core746.body = oqMainT (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop387`. -/
theorem oqLoopBody_746 : Data.core999.body = oqLoop0T (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_783 : Data.core783.body = oqMainT (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop391`. -/
theorem oqLoopBody_783 : Data.core1004.body = oqLoop1T (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1`. -/
theorem oqBody_795 : Data.core795.body = oqMainT (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop395`. -/
theorem oqLoopBody_795 : Data.core1008.body = oqLoop0T (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape).oq) "__loop395" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1`. -/
theorem oqBody_815 : Data.core815.body = oqMainT (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop399`. -/
theorem oqLoopBody_815 : Data.core1014.body = oqLoop0T (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq) "__loop399" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1`. -/
theorem oqBody_836 : Data.core836.body = oqMainT (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop403`. -/
theorem oqLoopBody_836 : Data.core1020.body = oqLoop0T (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq) "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_857 : Data.core857.body = oqMainT (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop407`. -/
theorem oqLoopBody_857 : Data.core1026.body = oqLoop0T (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop407" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_876 : Data.core876.body = oqMainT (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `__loop411`. -/
theorem oqLoopBody_876 : Data.core1031.body = oqLoop0T (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq) "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
