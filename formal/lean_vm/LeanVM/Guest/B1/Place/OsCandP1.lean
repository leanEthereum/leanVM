/-
  LeanVM.Guest.B1.Place.OsCandP1

  Candidates 7..13's placed facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCand

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placedP_7 : PlacedP (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_8 : PlacedP (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_9 : PlacedP (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_10 : PlacedP (osCfg 10) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_11 : PlacedP (osCfg 11) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_12 : PlacedP (osCfg 12) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_13 : PlacedP (osCfg 13) := by decide +kernel

end
end LeanVM.Guest.B1
