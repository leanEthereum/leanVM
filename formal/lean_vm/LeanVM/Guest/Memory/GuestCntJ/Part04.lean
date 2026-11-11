module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_336 : kwjStaticRange 336 6 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_342 : kwjStaticRange 342 6 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
