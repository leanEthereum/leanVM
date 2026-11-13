/-
  LeanVM.Guest.B1.Whir.Facts1

  Size 1's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_1_0 : candB 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_1_1 : candB 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_1_2 : candB 1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_1_3 : candB 1 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
