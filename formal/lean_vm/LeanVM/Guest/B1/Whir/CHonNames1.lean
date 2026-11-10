/-
  LeanVM.Guest.B1.Whir.CHonNames1

  Candidates 7..13's callees' kinds, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honNames_7 : HonNames (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_8 : HonNames (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_9 : HonNames (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_10 : HonNames (osCfg 10) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_11 : HonNames (osCfg 11) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_12 : HonNames (osCfg 12) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_13 : HonNames (osCfg 13) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
