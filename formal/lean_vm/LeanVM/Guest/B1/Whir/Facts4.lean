/-
  LeanVM.Guest.B1.Whir.Facts4

  Size 4's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_4_0 : candB 4 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_4_1 : candB 4 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_4_2 : candB 4 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_4_3 : candB 4 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
