module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_307 : kwjStaticRange 307 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_314 : kwjStaticRange 314 7 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
