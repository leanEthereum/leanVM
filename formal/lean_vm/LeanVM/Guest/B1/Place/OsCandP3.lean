/-
  LeanVM.Guest.B1.Place.OsCandP3

  Candidates 21..27's placed facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCand

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placedP_21 : PlacedP (osCfg 21) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_22 : PlacedP (osCfg 22) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_23 : PlacedP (osCfg 23) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_24 : PlacedP (osCfg 24) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_25 : PlacedP (osCfg 25) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_26 : PlacedP (osCfg 26) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placedP_27 : PlacedP (osCfg 27) := by decide +kernel

end
end LeanVM.Guest.B1
