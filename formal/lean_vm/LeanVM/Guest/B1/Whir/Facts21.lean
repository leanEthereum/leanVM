/-
  LeanVM.Guest.B1.Whir.Facts21

  Candidate 21's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_21 : candB 21 22 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
