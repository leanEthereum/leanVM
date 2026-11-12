/-
  LeanVM.Guest.B1.Whir.CHonAlloc3

  The arms' body allocations at rate 3, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_0_3 : BodyStatic (osCfgR 0 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_1_3 : BodyStatic (osCfgR 1 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_2_3 : BodyStatic (osCfgR 2 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_3_3 : BodyStatic (osCfgR 3 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_4_3 : BodyStatic (osCfgR 4 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_5_3 : BodyStatic (osCfgR 5 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_6_3 : BodyStatic (osCfgR 6 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_7_3 : BodyStatic (osCfgR 7 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_8_3 : BodyStatic (osCfgR 8 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_9_3 : BodyStatic (osCfgR 9 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_10_3 : BodyStatic (osCfgR 10 3) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
