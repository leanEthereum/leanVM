/-
  LeanVM.Guest.B1.Whir.CHonAlloc2

  The arms' body allocations at rate 2, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodyStatic_0_2 : BodyStatic (osCfgR 0 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_1_2 : BodyStatic (osCfgR 1 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_2_2 : BodyStatic (osCfgR 2 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_3_2 : BodyStatic (osCfgR 3 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_4_2 : BodyStatic (osCfgR 4 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_5_2 : BodyStatic (osCfgR 5 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_6_2 : BodyStatic (osCfgR 6 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_7_2 : BodyStatic (osCfgR 7 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_8_2 : BodyStatic (osCfgR 8 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_9_2 : BodyStatic (osCfgR 9 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem bodyStatic_10_2 : BodyStatic (osCfgR 10 2) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
