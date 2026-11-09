/-
  LeanVM.Guest.B1.Whir.Facts9

  Candidate 9's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_9 : candB 9 24 2 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
