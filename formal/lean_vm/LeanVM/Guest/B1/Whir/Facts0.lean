/-
  LeanVM.Guest.B1.Whir.Facts0

  Size 0's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_0_0 : candB 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_0_1 : candB 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_0_2 : candB 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_0_3 : candB 0 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
