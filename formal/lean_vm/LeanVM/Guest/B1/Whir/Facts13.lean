/-
  LeanVM.Guest.B1.Whir.Facts13

  Size 13's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_13_0 : candB 13 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_13_1 : candB 13 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_13_2 : candB 13 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_13_3 : candB 13 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
