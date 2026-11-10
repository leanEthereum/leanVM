/-
  LeanVM.Guest.B1.Place.OsCandF2

  Candidates 14..20's placed-lift facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placeAll_14 : PlaceAll (osCfg 14) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_15 : PlaceAll (osCfg 15) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_16 : PlaceAll (osCfg 16) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_17 : PlaceAll (osCfg 17) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_18 : PlaceAll (osCfg 18) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_19 : PlaceAll (osCfg 19) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_20 : PlaceAll (osCfg 20) := by decide +kernel

end
end LeanVM.Guest.B1
