/-
  LeanVM.Guest.B1.Whir.Facts2

  Size 2's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_2_0 : candB 2 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_2_1 : candB 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_2_2 : candB 2 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_2_3 : candB 2 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
