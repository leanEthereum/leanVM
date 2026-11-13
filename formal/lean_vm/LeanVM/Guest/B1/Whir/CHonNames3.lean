/-
  LeanVM.Guest.B1.Whir.CHonNames3

  The arms' callees' kinds at rate 3, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honNames_0_3 : HonNames (osCfgR 0 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_1_3 : HonNames (osCfgR 1 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_2_3 : HonNames (osCfgR 2 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_3_3 : HonNames (osCfgR 3 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_4_3 : HonNames (osCfgR 4 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_5_3 : HonNames (osCfgR 5 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_6_3 : HonNames (osCfgR 6 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_7_3 : HonNames (osCfgR 7 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_8_3 : HonNames (osCfgR 8 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_9_3 : HonNames (osCfgR 9 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_10_3 : HonNames (osCfgR 10 3) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
