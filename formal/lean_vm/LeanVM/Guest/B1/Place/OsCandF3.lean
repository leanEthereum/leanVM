/-
  LeanVM.Guest.B1.Place.OsCandF3

  Candidates 21..27's placed-lift facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF

namespace LeanVM.Guest.B1

open LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem placeAll_21 : PlaceAll (osCfg 21) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_22 : PlaceAll (osCfg 22) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_23 : PlaceAll (osCfg 23) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_24 : PlaceAll (osCfg 24) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_25 : PlaceAll (osCfg 25) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_26 : PlaceAll (osCfg 26) := by decide +kernel

set_option maxRecDepth 100000 in
theorem placeAll_27 : PlaceAll (osCfg 27) := by decide +kernel

end
end LeanVM.Guest.B1
