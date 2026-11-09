/-
  LeanVM.Guest.B1.Whir.Facts15

  Candidate 15's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_15 : candB 15 23 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
