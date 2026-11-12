/-
  LeanVM.Guest.B1.Whir.Facts10

  Size 10's facts at each rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.Facts

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem candB_10_0 : candB 10 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_10_1 : candB 10 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_10_2 : candB 10 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem candB_10_3 : candB 10 3 = true := by decide +kernel

end
end LeanVM.Guest.B1.Whir
