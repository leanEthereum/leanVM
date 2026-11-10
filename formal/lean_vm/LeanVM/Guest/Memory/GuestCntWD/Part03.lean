module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_342 : kudStaticRange 342 6 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_348 : kudStaticRange 348 6 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
