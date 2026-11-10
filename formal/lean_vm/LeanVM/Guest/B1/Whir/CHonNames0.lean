/-
  LeanVM.Guest.B1.Whir.CHonNames0

  Candidates 0..6's callees' kinds, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem honNames_0 : HonNames (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_1 : HonNames (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_2 : HonNames (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_3 : HonNames (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_4 : HonNames (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_5 : HonNames (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem honNames_6 : HonNames (osCfg 6) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
