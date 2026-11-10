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

end
end LeanVM.Guest.B1
