/-
  LeanVM.Guest.B1.Whir.CHonStatic2

  The arms' buffer facts at rate 2, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honStatic_0_2 : HonStatic (osCfgR 0 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_1_2 : HonStatic (osCfgR 1 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_2_2 : HonStatic (osCfgR 2 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_3_2 : HonStatic (osCfgR 3 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_4_2 : HonStatic (osCfgR 4 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_5_2 : HonStatic (osCfgR 5 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_6_2 : HonStatic (osCfgR 6 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_7_2 : HonStatic (osCfgR 7 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_8_2 : HonStatic (osCfgR 8 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_9_2 : HonStatic (osCfgR 9 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honStatic_10_2 : HonStatic (osCfgR 10 2) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
