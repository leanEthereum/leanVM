/-
  LeanVM.Guest.B1.Whir.Facts7

  Size 7's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_7_0 : candB 7 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_7_1 : candB 7 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_7_2 : candB 7 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_7_3 : candB 7 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
