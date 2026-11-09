/-
  LeanVM.Guest.B1.Whir.Facts6

  Candidate 6's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_6 : candB 6 28 1 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
