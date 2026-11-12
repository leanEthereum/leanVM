/-
  LeanVM.Guest.B1.Whir.CHonStatic3

  The arms' buffer facts at rate 3, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_0_3 : HonStatic (osCfgR 0 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_1_3 : HonStatic (osCfgR 1 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_2_3 : HonStatic (osCfgR 2 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_3_3 : HonStatic (osCfgR 3 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_4_3 : HonStatic (osCfgR 4 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_5_3 : HonStatic (osCfgR 5 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_6_3 : HonStatic (osCfgR 6 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_7_3 : HonStatic (osCfgR 7 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_8_3 : HonStatic (osCfgR 8 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_9_3 : HonStatic (osCfgR 9 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_10_3 : HonStatic (osCfgR 10 3) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
