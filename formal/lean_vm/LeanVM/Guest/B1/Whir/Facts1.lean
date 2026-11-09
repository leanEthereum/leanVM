/-
  LeanVM.Guest.B1.Whir.Facts1

  Candidate 1's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_1 : candB 1 23 1 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
