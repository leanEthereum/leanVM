module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_320 : kudStaticRange 320 17 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_337 : kudStaticRange 337 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
