/-
  LeanVM.Guest.B1.Whir.CHonNames2

  The arms' callees' kinds at rate 2, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honNames_0_2 : HonNames (osCfgR 0 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_1_2 : HonNames (osCfgR 1 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_2_2 : HonNames (osCfgR 2 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_3_2 : HonNames (osCfgR 3 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_4_2 : HonNames (osCfgR 4 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_5_2 : HonNames (osCfgR 5 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_6_2 : HonNames (osCfgR 6 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_7_2 : HonNames (osCfgR 7 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_8_2 : HonNames (osCfgR 8 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_9_2 : HonNames (osCfgR 9 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_10_2 : HonNames (osCfgR 10 2) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
