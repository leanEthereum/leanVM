/-
  LeanVM.Guest.B1.Whir.CHonStatic1

  The arms' buffer facts at rate 1, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_0_1 : HonStatic (osCfgR 0 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_1_1 : HonStatic (osCfgR 1 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_2_1 : HonStatic (osCfgR 2 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_3_1 : HonStatic (osCfgR 3 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_4_1 : HonStatic (osCfgR 4 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_5_1 : HonStatic (osCfgR 5 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_6_1 : HonStatic (osCfgR 6 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_7_1 : HonStatic (osCfgR 7 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_8_1 : HonStatic (osCfgR 8 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_9_1 : HonStatic (osCfgR 9 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_10_1 : HonStatic (osCfgR 10 1) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
