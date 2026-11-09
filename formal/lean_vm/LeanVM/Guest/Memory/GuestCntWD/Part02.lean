module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_291 : kudStaticRange 291 18 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_309 : kudStaticRange 309 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
