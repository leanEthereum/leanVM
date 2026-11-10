module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wsplit_323_1555 : blockR (wlookJ 323) (womLookJ 323) true [(.n 13, 4), (.n 15, 14), (.n 17, 30), (.n 19, 7), (.n 21, 7), (.n 23, 1638), (.n 25, 1638), (.n 27, 128), (.n 157, 182), (.n 159, 28), (.n 376, 64), (.n 599, 64), (.n 826, 64), (.n 1053, 64), (.n 1280, 64), (.n 1507, 64), (.n 1632, 64), (.n 1654, 5), (.n 1867, 182), (.n 1869, 7), (.n 2550, 8)] Data.core323.params Data.core323.name (Data.core323.body.drop 1555)
    ([(.n 1654, 5), (.n 1632, 64), (.n 1507, 64), (.n 1280, 64), (.n 1053, 64), (.n 826, 64), (.n 599, 64), (.n 376, 64), (.n 159, 28), (.n 157, 182), (.n 27, 128), (.n 25, 1638), (.n 23, 1638), (.n 21, 7), (.n 19, 7), (.n 17, 30), (.n 15, 14), (.n 13, 4)], []) = some (⟨39896, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_324 : wStaticRange 324 21 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_345 : wStaticRange 345 22 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_367 : wStaticRange 367 23 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
