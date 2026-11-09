/-
  LeanVM.Guest.B1.Whir.Facts25

  Candidate 25's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_25 : candB 25 26 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
