module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_314 : kwjStaticRange 314 3 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_317 : kwjStaticRange 317 3 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
