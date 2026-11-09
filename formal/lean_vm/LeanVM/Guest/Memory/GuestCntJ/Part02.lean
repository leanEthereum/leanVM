module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_36 : kwjStaticRange 36 1 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
