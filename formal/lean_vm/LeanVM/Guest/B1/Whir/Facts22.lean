/-
  LeanVM.Guest.B1.Whir.Facts22

  Candidate 22's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_22 : candB 22 23 4 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
