/-
  LeanVM.Guest.B1.Place.OsCandP2

  Candidates 14..20's placed facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCand

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placedP_14 : PlacedP (osCfg 14) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_15 : PlacedP (osCfg 15) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_16 : PlacedP (osCfg 16) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_17 : PlacedP (osCfg 17) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_18 : PlacedP (osCfg 18) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_19 : PlacedP (osCfg 19) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_20 : PlacedP (osCfg 20) := by decide +kernel

end
end LeanVM.Guest.B1
