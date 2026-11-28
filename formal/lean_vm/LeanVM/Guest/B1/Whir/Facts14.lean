/-
  LeanVM.Guest.B1.Whir.Facts14

  Size 14's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_14_0 : candB 14 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_14_1 : candB 14 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_14_2 : candB 14 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_14_3 : candB 14 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
