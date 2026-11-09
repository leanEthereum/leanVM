/-
  LeanVM.Guest.B1.Whir.Facts10

  Candidate 10's facts, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_10 : candB 10 25 2 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
