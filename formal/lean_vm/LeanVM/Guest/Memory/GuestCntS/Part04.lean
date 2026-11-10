module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_314 : kwsStaticRange 314 3 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_317 : kwsStaticRange 317 3 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
