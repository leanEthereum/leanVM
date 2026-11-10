/-
  LeanVM.Guest.B1.Place.OsCandF1

  Candidates 7..13's placed-lift facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placeAll_7 : PlaceAll (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_8 : PlaceAll (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_9 : PlaceAll (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_10 : PlaceAll (osCfg 10) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_11 : PlaceAll (osCfg 11) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_12 : PlaceAll (osCfg 12) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_13 : PlaceAll (osCfg 13) := by decide +kernel

end
end LeanVM.Guest.B1
