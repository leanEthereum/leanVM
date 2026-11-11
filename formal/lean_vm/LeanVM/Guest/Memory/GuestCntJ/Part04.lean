module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_337 : kwjStaticRange 337 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_344 : kwjStaticRange 344 6 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
