/-
  LeanVM.Guest.B1.Place.OsCandP0

  Candidates 0..6's placed facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCand

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placedP_0 : PlacedP (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_1 : PlacedP (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_2 : PlacedP (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_3 : PlacedP (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_4 : PlacedP (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_5 : PlacedP (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_6 : PlacedP (osCfg 6) := by decide +kernel

end
end LeanVM.Guest.B1
