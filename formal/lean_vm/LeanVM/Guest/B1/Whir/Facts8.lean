/-
  LeanVM.Guest.B1.Whir.Facts8

  Size 8's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_8_0 : candB 8 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_8_1 : candB 8 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_8_2 : candB 8 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_8_3 : candB 8 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
