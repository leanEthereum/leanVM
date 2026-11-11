module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_344 : kudStaticRange 344 6 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_350 : kudStaticRange 350 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
