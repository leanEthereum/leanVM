/-
  LeanVM.Guest.B1.Whir.CHonAlloc1

  The arms' body allocations at rate 1, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_0_1 : BodyStatic (osCfgR 0 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_1_1 : BodyStatic (osCfgR 1 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_2_1 : BodyStatic (osCfgR 2 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_3_1 : BodyStatic (osCfgR 3 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_4_1 : BodyStatic (osCfgR 4 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_5_1 : BodyStatic (osCfgR 5 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_6_1 : BodyStatic (osCfgR 6 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_7_1 : BodyStatic (osCfgR 7 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_8_1 : BodyStatic (osCfgR 8 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_9_1 : BodyStatic (osCfgR 9 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_10_1 : BodyStatic (osCfgR 10 1) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
