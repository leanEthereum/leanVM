module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_20 : kwjStaticRange 20 16 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
