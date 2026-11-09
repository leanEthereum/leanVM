/-
  LeanVM.Guest.B1.Whir.Facts0

  Candidate 0's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_0 : candB 0 22 1 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
