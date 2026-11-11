module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_320 : kudStaticRange 320 18 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_338 : kudStaticRange 338 3 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
