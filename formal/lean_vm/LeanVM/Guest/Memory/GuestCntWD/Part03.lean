module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_316 : kudStaticRange 316 3 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_319 : kudStaticRange 319 2 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
