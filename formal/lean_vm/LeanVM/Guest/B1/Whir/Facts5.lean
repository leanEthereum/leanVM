/-
  LeanVM.Guest.B1.Whir.Facts5

  Size 5's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_5_0 : candB 5 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_5_1 : candB 5 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_5_2 : candB 5 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_5_3 : candB 5 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
