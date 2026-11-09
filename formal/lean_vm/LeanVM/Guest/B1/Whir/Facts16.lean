/-
  LeanVM.Guest.B1.Whir.Facts16

  Candidate 16's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_16 : candB 16 24 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
