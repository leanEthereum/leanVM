/-
  LeanVM.Guest.B1.Place.OsCandF0

  Candidates 0..6's placed-lift facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placeAll_0 : PlaceAll (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_1 : PlaceAll (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_2 : PlaceAll (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_3 : PlaceAll (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_4 : PlaceAll (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_5 : PlaceAll (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_6 : PlaceAll (osCfg 6) := by decide +kernel

end
end LeanVM.Guest.B1
